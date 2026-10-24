use crate::collector::copy_origins;
use anyhow::{bail, ensure, Context, Result};
use noid_chain::{consensus::genesis::genesis_header, history_step::HistoryStepTerminalMetadata};
use reqwest::{blocking::Client, redirect::Policy, Url};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{Read, Write},
    path::Path,
    time::Duration,
};

const MAX_RPC_BYTES: u64 = 4 * 1024 * 1024;
const HEADER_BATCH: u64 = 64;

pub struct Rpc {
    endpoint: Url,
    client: Client,
    id: u64,
}

impl Rpc {
    pub fn new(endpoint: &str) -> Result<Self> {
        let endpoint = Url::parse(endpoint)?;
        let loopback = endpoint.host_str().is_some_and(|host| {
            host == "localhost"
                || host
                    .trim_start_matches('[')
                    .trim_end_matches(']')
                    .parse::<std::net::IpAddr>()
                    .is_ok_and(|address| address.is_loopback())
        });
        ensure!(
            endpoint.username().is_empty() && endpoint.password().is_none(),
            "RPC URL credentials are unsupported"
        );
        ensure!(
            endpoint.scheme() == "https" || endpoint.scheme() == "http" && loopback,
            "use HTTPS or loopback HTTP"
        );
        ensure!(endpoint.fragment().is_none(), "RPC URL fragment");
        let client = Client::builder()
            .redirect(Policy::none())
            .no_proxy()
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .build()?;
        Ok(Self {
            endpoint,
            client,
            id: 0,
        })
    }

    fn post(&self, body: &Value) -> Result<Value> {
        let response = self
            .client
            .post(self.endpoint.clone())
            .json(body)
            .send()?
            .error_for_status()?;
        if let Some(length) = response.content_length() {
            ensure!(length <= MAX_RPC_BYTES, "RPC byte limit");
        }
        let mut bytes = Vec::new();
        response.take(MAX_RPC_BYTES + 1).read_to_end(&mut bytes)?;
        ensure!(
            bytes.len() as u64 <= MAX_RPC_BYTES,
            "RPC streamed byte limit"
        );
        Ok(serde_json::from_slice(&bytes)?)
    }

    fn envelope(value: &Value, expected: &str) -> Result<Value> {
        let object = value.as_object().context("RPC envelope object")?;
        ensure!(
            object.get("jsonrpc").and_then(Value::as_str) == Some("2.0"),
            "RPC version"
        );
        ensure!(
            object.get("id").and_then(Value::as_str) == Some(expected),
            "RPC response identity"
        );
        ensure!(
            object.contains_key("result") != object.contains_key("error"),
            "ambiguous RPC envelope"
        );
        if let Some(error) = object.get("error") {
            bail!("node RPC error: {error}");
        }
        Ok(object["result"].clone())
    }

    pub fn call(&mut self, method: &str, params: Value) -> Result<Value> {
        self.id = self.id.checked_add(1).context("RPC identity overflow")?;
        let id = format!("paramo1d-{}", self.id);
        let value = self.post(&json!({"jsonrpc":"2.0", "id":id, "method":format!("paranoid_{method}"), "params":params}))?;
        Self::envelope(&value, &id)
    }

    fn headers(&self, first: u64, count: u64) -> Result<Vec<Vec<u8>>> {
        ensure!((1..=HEADER_BATCH).contains(&count), "header batch count");
        let requests: Vec<_> = (first..first + count)
            .map(|height| {
                json!({"jsonrpc":"2.0",
            "id":height.to_string(), "method":"paranoid_getHeaderByHeight", "params":[height]})
            })
            .collect();
        let value = self.post(&Value::Array(requests))?;
        let values = value.as_array().context("RPC batch response")?;
        ensure!(values.len() == count as usize, "RPC batch response count");
        let mut indexed = BTreeMap::new();
        for value in values {
            let id = value
                .get("id")
                .and_then(Value::as_str)
                .context("RPC batch identity")?;
            let height: u64 = id.parse()?;
            ensure!(
                height >= first && height < first + count && id == height.to_string(),
                "unexpected RPC batch identity"
            );
            let result = Self::envelope(value, id)?;
            let encoded = result.as_str().context("missing canonical header")?;
            ensure!(
                encoded.len() == noid_chain::wire::BLOCK_HEADER_WIRE_SIZE * 2,
                "header byte length"
            );
            ensure!(
                indexed.insert(height, hex::decode(encoded)?).is_none(),
                "duplicate RPC batch response"
            );
        }
        Ok(indexed.into_values().collect())
    }
}

pub fn fetch(endpoint: &str, origins: &Path, output: &Path) -> Result<Value> {
    ensure!(!output.exists(), "output bundle already exists");
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent)?;
    let temporary = tempfile::Builder::new()
        .prefix(".paramo1d-bundle-")
        .tempdir_in(parent)?;
    let mut rpc = Rpc::new(endpoint)?;
    let chain = rpc.call("getChainInfo", json!([]))?;
    let tip = chain
        .get("height")
        .and_then(Value::as_u64)
        .context("node tip height")?;
    ensure!(tip < 40_000_000, "header synchronization byte limit");
    let genesis = rpc.call("getHeaderByHeight", json!([0]))?;
    ensure!(
        genesis.as_str() == Some(&hex::encode(genesis_header().to_bytes())),
        "node network differs from the compiled profile"
    );
    let terminal = rpc.call("getHistoryStepTerminal", json!([]))?;
    let encoded = terminal
        .as_str()
        .context("node has no finalized terminal")?;
    ensure!(encoded.len() <= 2_200_000, "terminal encoding byte limit");
    let bytes = hex::decode(encoded)?;
    let metadata = HistoryStepTerminalMetadata::decode_prefix(&bytes)?;
    ensure!(
        metadata.terminal_height() <= tip,
        "terminal exceeds announced tip"
    );
    fs::write(temporary.path().join("terminal.bin"), bytes)?;
    let mut headers = File::create(temporary.path().join("headers.bin"))?;
    let mut first = 0;
    let boundary = metadata.terminal_height();
    while first <= boundary {
        let count = HEADER_BATCH.min(boundary - first + 1);
        for header in rpc.headers(first, count)? {
            headers.write_all(&header)?;
        }
        first += count;
    }
    headers.sync_all()?;
    drop(headers);
    let origin_bytes = copy_origins(origins, temporary.path(), boundary)?;
    let manifest = json!({"schema":1, "network":crate::artifacts::profile().network,
        "announced_tip":tip, "terminal_height":metadata.terminal_height(),
        "origin_bytes":origin_bytes,
        "headers":boundary + 1, "header_bytes":(boundary + 1) * 212});
    fs::write(
        temporary.path().join("bundle.json"),
        serde_json::to_vec_pretty(&manifest)?,
    )?;
    fs::rename(temporary.path(), output)?;
    Ok(manifest)
}
