//! A bounded public interface to the colocated node's wallet-data methods.
use anyhow::{ensure, Result};
use axum::{
    extract::{DefaultBodyLimit, State},
    http::{header, StatusCode},
    response::{IntoResponse, Response},
    routing::post,
    Json, Router,
};
use serde_json::{json, Value};
use std::{collections::BTreeSet, sync::Arc, time::Duration};
use tokio::sync::Semaphore;

const MAX_RESPONSE: usize = 4 * 1024 * 1024;
#[derive(Clone)]
struct Gateway {
    endpoint: reqwest::Url,
    client: reqwest::Client,
    permits: Arc<Semaphore>,
}

fn validate(request: &Value) -> Result<()> {
    let object = request
        .as_object()
        .ok_or_else(|| anyhow::anyhow!("One JSON-RPC request is required"))?;
    ensure!(
        object.len() == 4
            && request["jsonrpc"] == "2.0"
            && object.contains_key("id")
            && (request["id"].is_string() || request["id"].is_number()),
        "Invalid JSON-RPC request"
    );
    let params = request["params"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("Positional parameters are required"))?;
    ensure!(params.len() == 1, "One parameter is required");
    match request["method"].as_str() {
        Some("paranoid_getSlotsByOwner") => {
            let address = params[0].as_str().unwrap_or("");
            ensure!(
                address.starts_with("o1") && address.len() <= 128,
                "Invalid owner address"
            );
        }
        Some("paranoid_getSlotHints") => ensure!(
            params[0].as_u64().is_some_and(|n| (1..=8).contains(&n)),
            "Request at most eight slot hints"
        ),
        Some("paranoid_getSlotProof") => {
            let indices = params[0]
                .as_array()
                .ok_or_else(|| anyhow::anyhow!("Expected slot indices"))?;
            ensure!(
                !indices.is_empty() && indices.len() <= 128,
                "Request at most 128 slots"
            );
            let mut previous = None;
            let mut segments = BTreeSet::new();
            for index in indices {
                let index = index
                    .as_u64()
                    .filter(|v| *v <= u32::MAX as u64)
                    .ok_or_else(|| anyhow::anyhow!("Invalid slot index"))?;
                ensure!(
                    previous.is_none_or(|p| p < index),
                    "Slot indices must be sorted and unique"
                );
                previous = Some(index);
                segments.insert(index >> 16);
            }
            ensure!(segments.len() <= 8, "Request at most eight State segments");
        }
        Some("paranoid_getTx" | "paranoid_getMempoolEntry") => {
            paramo1d_courier::decode_array::<32>(params[0].as_str().unwrap_or(""))?;
        }
        Some("paranoid_getBlock") => ensure!(params[0].as_u64().is_some(), "Expected block height"),
        Some("paranoid_submitTxIntent") => {
            let encoded = params[0].as_str().unwrap_or("");
            ensure!(
                !encoded.is_empty()
                    && encoded.len() <= 606990
                    && encoded.len() % 2 == 0
                    && encoded.bytes().all(|c| c.is_ascii_hexdigit()),
                "Invalid transaction encoding"
            );
        }
        _ => anyhow::bail!("Method is unavailable on the public wallet interface"),
    }
    Ok(())
}

async fn call(State(gateway): State<Gateway>, Json(request): Json<Value>) -> Response {
    if let Err(error) = validate(&request) {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error":error.to_string()})),
        )
            .into_response();
    }
    let Ok(_permit) = gateway.permits.clone().try_acquire_owned() else {
        return (
            StatusCode::TOO_MANY_REQUESTS,
            Json(json!({"error":"Wallet data is busy; retry shortly"})),
        )
            .into_response();
    };
    let result = async {
        let mut response = gateway
            .client
            .post(gateway.endpoint.clone())
            .json(&request)
            .send()
            .await?
            .error_for_status()?;
        ensure!(
            response
                .content_length()
                .is_none_or(|n| n <= MAX_RESPONSE as u64),
            "Node response exceeds byte limit"
        );
        let mut bytes = Vec::new();
        while let Some(chunk) = response.chunk().await? {
            ensure!(
                bytes.len() + chunk.len() <= MAX_RESPONSE,
                "Node response exceeds byte limit"
            );
            bytes.extend_from_slice(&chunk);
        }
        let result: Value = serde_json::from_slice(&bytes)?;
        ensure!(
            result["jsonrpc"] == "2.0"
                && result["id"] == request["id"]
                && (result.get("result").is_some() != result.get("error").is_some()),
            "Node response identity mismatch"
        );
        Ok::<_, anyhow::Error>(bytes)
    }
    .await;
    match result {
        Ok(bytes) => ([(header::CONTENT_TYPE, "application/json")], bytes).into_response(),
        Err(_) => (
            StatusCode::BAD_GATEWAY,
            Json(json!({"error":"Chain data is temporarily unavailable"})),
        )
            .into_response(),
    }
}

pub fn router(endpoint: &str) -> Result<Router> {
    let endpoint = reqwest::Url::parse(endpoint)?;
    ensure!(
        endpoint.scheme() == "http"
            && endpoint.host_str().is_some_and(|host| host == "localhost"
                || host
                    .parse::<std::net::IpAddr>()
                    .is_ok_and(|ip| ip.is_loopback()))
            && endpoint.username().is_empty()
            && endpoint.password().is_none()
            && endpoint.query().is_none()
            && endpoint.fragment().is_none(),
        "The data gateway requires a loopback node endpoint without URL credentials"
    );
    let client = reqwest::Client::builder()
        .no_proxy()
        .redirect(reqwest::redirect::Policy::none())
        .timeout(Duration::from_secs(20))
        .connect_timeout(Duration::from_secs(2))
        .build()?;
    Ok(Router::new()
        .route("/chain", post(call))
        .layer(DefaultBodyLimit::max(paramo1d_courier::MAX_ENVELOPE))
        .with_state(Gateway {
            endpoint,
            client,
            permits: Arc::new(Semaphore::new(2)),
        }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn public_gateway_exposes_only_bounded_data_and_submission_calls() {
        let request = |method: &str, params: Value| json!({"jsonrpc":"2.0","id":"mobile-1","method":method,"params":params});
        assert!(validate(&request("paranoid_getSlotProof", json!([[1, 2, 3]]))).is_ok());
        for method in [
            "paranoid_getMasterSecret",
            "paranoid_send",
            "paranoid_exportKey",
            "paranoid_getWalletAddresses",
            "paranoid_getNativeAsset",
        ] {
            assert!(validate(&request(method, json!([]))).is_err());
        }
        assert!(validate(&request("paranoid_getSlotProof", json!([[3, 2, 1]]))).is_err());
        assert!(validate(&request(
            "paranoid_getSlotProof",
            json!([(0u64..9).map(|i| i << 16).collect::<Vec<_>>()])
        ))
        .is_err());
        assert!(validate(&request("paranoid_getSlotHints", json!([10000]))).is_err());
        assert!(validate(&json!([request("paranoid_getBlock", json!([1]))])).is_err());
        assert!(router("http://example.com/rpc").is_err());
    }
}
