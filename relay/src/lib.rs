use anyhow::{ensure, Result};
pub mod gateway;
use axum::{
    extract::{DefaultBodyLimit, Path as RoutePath, Query, State},
    http::{HeaderMap, StatusCode, Uri},
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use paramo1d_courier::{
    decode_array, validate_room, verify_read, Destination, Envelope, Message, LOBBY, MAX_ENVELOPE,
};
use rusqlite::{params, Connection};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::HashMap,
    path::Path,
    sync::{Arc, Mutex},
    time::{SystemTime, UNIX_EPOCH},
};
use tokio::sync::{watch, Semaphore};

const MAX_MESSAGES: i64 = 20_000;
const MAX_STORED_BYTES: i64 = 128 * 1024 * 1024;
const MAX_REPLY_BYTES: usize = 4 * 1024 * 1024;

#[derive(Clone)]
pub struct Relay {
    inner: Arc<Mutex<Store>>,
    changes: watch::Sender<i64>,
    readers: Arc<Semaphore>,
}
struct Store {
    db: Connection,
    rates: HashMap<String, (u64, u32)>,
}

#[derive(Serialize, Deserialize)]
pub struct Delivery {
    pub cursor: i64,
    pub envelope: Envelope,
}
#[derive(Serialize, Deserialize)]
pub struct Page {
    pub messages: Vec<Delivery>,
    pub cursor: i64,
}
#[derive(Default, Deserialize)]
struct Pagination {
    #[serde(default)]
    after: i64,
    limit: Option<usize>,
}
#[derive(Default, Deserialize)]
struct SyncQuery {
    #[serde(default)]
    group_after: i64,
    #[serde(default)]
    inbox_after: i64,
    wait_ms: Option<u64>,
}
#[derive(Serialize, Deserialize)]
struct SyncPage {
    group: Page,
    inbox: Page,
}

pub fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

impl Relay {
    pub fn open(path: &Path) -> Result<Self> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let db = Connection::open(path)?;
        db.execute_batch("PRAGMA journal_mode=WAL; PRAGMA synchronous=NORMAL;
            PRAGMA max_page_count=49152;
            CREATE TABLE IF NOT EXISTS messages (
              seq INTEGER PRIMARY KEY AUTOINCREMENT, id TEXT NOT NULL UNIQUE,
              room TEXT, recipient TEXT, sender TEXT NOT NULL, expires INTEGER NOT NULL,
              bytes INTEGER NOT NULL, envelope TEXT NOT NULL);
            CREATE INDEX IF NOT EXISTS messages_room ON messages(room,seq);
            CREATE INDEX IF NOT EXISTS messages_inbox ON messages(recipient,seq);
            CREATE INDEX IF NOT EXISTS messages_expiry ON messages(expires);
            CREATE TABLE IF NOT EXISTS status_updates (sender TEXT NOT NULL, txid TEXT NOT NULL, seq INTEGER NOT NULL, created INTEGER NOT NULL, PRIMARY KEY(sender,txid));")?;
        Ok(Self {
            inner: Arc::new(Mutex::new(Store {
                db,
                rates: HashMap::new(),
            })),
            changes: watch::channel(0).0,
            readers: Arc::new(Semaphore::new(256)),
        })
    }

    pub fn publish(&self, envelope: Envelope, now: u64) -> Result<i64> {
        envelope.verify(now)?;
        if let Destination::Group { room } = &envelope.data.destination {
            ensure!(room == LOBBY, "This relay serves the community chat");
        }
        let update = match envelope.public_message()? {
            Some(Message::RelayUpdate { txid, .. }) => Some(txid),
            _ => None,
        };
        let encoded = serde_json::to_string(&envelope)?;
        ensure!(
            encoded.len() <= MAX_ENVELOPE,
            "Envelope exceeds delivery limit"
        );
        let mut store = self
            .inner
            .lock()
            .map_err(|_| anyhow::anyhow!("Store unavailable"))?;
        store
            .db
            .execute("DELETE FROM messages WHERE expires <= ?1", [now])?;
        store.db.execute(
            "DELETE FROM status_updates WHERE seq NOT IN (SELECT seq FROM messages)",
            [],
        )?;
        if let Ok(existing) = store.db.query_row(
            "SELECT seq FROM messages WHERE id=?1",
            [&envelope.id],
            |r| r.get(0),
        ) {
            return Ok(existing);
        }
        let minute = now / 60_000;
        store
            .rates
            .retain(|_, (time, _)| *time >= minute.saturating_sub(1));
        ensure!(
            store.rates.len() < 4096 || store.rates.contains_key(&envelope.data.sender.id),
            "Relay admission is busy"
        );
        let rate = store
            .rates
            .entry(envelope.data.sender.id.clone())
            .or_insert((minute, 0));
        if rate.0 != minute {
            *rate = (minute, 0);
        }
        ensure!(rate.1 < 30, "Message rate limit; retry next minute");
        rate.1 += 1;
        let transaction = store.db.transaction()?;
        if let Some(txid) = &update {
            let previous: Option<(i64, u64)> = transaction
                .query_row(
                    "SELECT seq,created FROM status_updates WHERE sender=?1 AND txid=?2",
                    params![envelope.data.sender.id, txid],
                    |r| Ok((r.get(0)?, r.get(1)?)),
                )
                .ok();
            if let Some((seq, created)) = previous {
                if created >= envelope.data.created_ms {
                    return Ok(seq);
                }
                transaction.execute("DELETE FROM messages WHERE seq=?1", [seq])?;
            }
        }
        let (count, bytes): (i64, i64) = transaction.query_row(
            "SELECT COUNT(*),COALESCE(SUM(bytes),0) FROM messages",
            [],
            |r| Ok((r.get(0)?, r.get(1)?)),
        )?;
        ensure!(
            count < MAX_MESSAGES && bytes + encoded.len() as i64 <= MAX_STORED_BYTES,
            "Relay storage is full"
        );
        let (room, recipient) = match &envelope.data.destination {
            Destination::Group { room } => (Some(room.as_str()), None),
            Destination::Direct { contact } => (None, Some(contact.id.as_str())),
        };
        transaction.execute("INSERT INTO messages(id,room,recipient,sender,expires,bytes,envelope) VALUES(?1,?2,?3,?4,?5,?6,?7)",
            params![envelope.id,room,recipient,envelope.data.sender.id,envelope.data.expires_ms,encoded.len(),encoded])?;
        let seq = transaction.last_insert_rowid();
        if let Some(txid) = update {
            transaction.execute("INSERT INTO status_updates(sender,txid,seq,created) VALUES(?1,?2,?3,?4) ON CONFLICT(sender,txid) DO UPDATE SET seq=excluded.seq,created=excluded.created",params![envelope.data.sender.id,txid,seq,envelope.data.created_ms])?;
        }
        transaction.commit()?;
        self.changes.send_replace(seq);
        Ok(seq)
    }

    pub fn read(
        &self,
        column: &str,
        key: &str,
        after: i64,
        limit: usize,
        now: u64,
    ) -> Result<Page> {
        self.read_limited(column, key, after, limit, now, MAX_REPLY_BYTES)
    }

    fn read_limited(
        &self,
        column: &str,
        key: &str,
        after: i64,
        limit: usize,
        now: u64,
        byte_limit: usize,
    ) -> Result<Page> {
        ensure!(
            matches!(column, "room" | "recipient"),
            "Invalid delivery scope"
        );
        ensure!(
            after >= 0 && limit > 0 && limit <= 100,
            "Invalid page range"
        );
        let store = self
            .inner
            .lock()
            .map_err(|_| anyhow::anyhow!("Store unavailable"))?;
        let sql=format!("SELECT seq,envelope FROM messages WHERE {column}=?1 AND seq>?2 AND expires>?3 ORDER BY seq LIMIT ?4");
        let mut statement = store.db.prepare(&sql)?;
        let mut rows = statement.query(params![key, after, now, limit])?;
        let mut messages = Vec::new();
        let mut bytes = 0;
        while let Some(row) = rows.next()? {
            let encoded: String = row.get(1)?;
            if !messages.is_empty() && bytes + encoded.len() > byte_limit {
                break;
            }
            bytes += encoded.len();
            messages.push(Delivery {
                cursor: row.get(0)?,
                envelope: serde_json::from_str(&encoded)?,
            });
        }
        let cursor = messages.last().map_or(after, |m| m.cursor);
        Ok(Page { messages, cursor })
    }

    fn rooms(&self) -> Result<Vec<Value>> {
        let store = self
            .inner
            .lock()
            .map_err(|_| anyhow::anyhow!("Store unavailable"))?;
        let mut q=store.db.prepare("SELECT room,COUNT(*),MAX(seq) FROM messages WHERE room IS NOT NULL AND expires>?1 GROUP BY room ORDER BY MAX(seq) DESC LIMIT 100")?;
        let mut rooms=q.query_map([now_ms()],|r|Ok(json!({"id":r.get::<_,String>(0)?,"messages":r.get::<_,i64>(1)?,"cursor":r.get::<_,i64>(2)?})))?.collect::<rusqlite::Result<Vec<_>>>()?;
        if !rooms.iter().any(|r| r["id"] == "parano1d") {
            rooms.insert(0, json!({"id":"parano1d","messages":0,"cursor":0}));
        }
        Ok(rooms)
    }
}

type ApiResult<T> = std::result::Result<Json<T>, (StatusCode, Json<Value>)>;
fn error(e: impl std::fmt::Display) -> (StatusCode, Json<Value>) {
    (
        StatusCode::BAD_REQUEST,
        Json(json!({"error":e.to_string()})),
    )
}
async fn publish(State(relay): State<Relay>, Json(envelope): Json<Envelope>) -> ApiResult<Value> {
    let cursor = relay.publish(envelope, now_ms()).map_err(error)?;
    Ok(Json(json!({"accepted":true,"cursor":cursor})))
}
async fn group(
    State(relay): State<Relay>,
    RoutePath(room): RoutePath<String>,
    Query(p): Query<Pagination>,
) -> ApiResult<Page> {
    validate_room(&room).map_err(error)?;
    if room != LOBBY {
        return Err(error("This relay serves the community chat"));
    }
    Ok(Json(
        relay
            .read(
                "room",
                &room,
                p.after,
                p.limit.unwrap_or(50).min(100),
                now_ms(),
            )
            .map_err(error)?,
    ))
}
async fn inbox(
    State(relay): State<Relay>,
    RoutePath(recipient): RoutePath<String>,
    Query(p): Query<Pagination>,
    uri: Uri,
    headers: HeaderMap,
) -> ApiResult<Page> {
    authenticate(&recipient, &uri, &headers)?;
    Ok(Json(
        relay
            .read(
                "recipient",
                &recipient,
                p.after,
                p.limit.unwrap_or(50).min(100),
                now_ms(),
            )
            .map_err(error)?,
    ))
}

fn authenticate(
    recipient: &str,
    uri: &Uri,
    headers: &HeaderMap,
) -> Result<(), (StatusCode, Json<Value>)> {
    decode_array::<32>(&recipient).map_err(error)?;
    let time = headers
        .get("x-paramo1d-time")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.parse().ok())
        .ok_or_else(|| error("Inbox authentication required"))?;
    let signature = headers
        .get("x-paramo1d-signature")
        .and_then(|v| v.to_str().ok())
        .ok_or_else(|| error("Inbox authentication required"))?;
    verify_read(
        recipient,
        uri.path_and_query().map_or(uri.path(), |v| v.as_str()),
        time,
        signature,
        now_ms(),
    )
    .map_err(error)
}

async fn sync(
    State(relay): State<Relay>,
    RoutePath(recipient): RoutePath<String>,
    Query(query): Query<SyncQuery>,
    uri: Uri,
    headers: HeaderMap,
) -> ApiResult<SyncPage> {
    authenticate(&recipient, &uri, &headers)?;
    if query.group_after < 0 || query.inbox_after < 0 || query.wait_ms.unwrap_or(0) > 10_000 {
        return Err(error("Invalid synchronization range"));
    }
    let _permit = relay.readers.try_acquire().map_err(|_| {
        (
            StatusCode::SERVICE_UNAVAILABLE,
            Json(json!({"error":"Delivery is busy. Retry shortly"})),
        )
    })?;
    let mut changes = relay.changes.subscribe();
    let deadline =
        tokio::time::Instant::now() + std::time::Duration::from_millis(query.wait_ms.unwrap_or(0));
    loop {
        let now = now_ms();
        let page = SyncPage {
            group: relay
                .read_limited(
                    "room",
                    LOBBY,
                    query.group_after,
                    30,
                    now,
                    MAX_REPLY_BYTES / 2 - 65536,
                )
                .map_err(error)?,
            inbox: relay
                .read_limited(
                    "recipient",
                    &recipient,
                    query.inbox_after,
                    30,
                    now,
                    MAX_REPLY_BYTES / 2 - 65536,
                )
                .map_err(error)?,
        };
        if !page.group.messages.is_empty()
            || !page.inbox.messages.is_empty()
            || tokio::time::Instant::now() >= deadline
        {
            return Ok(Json(page));
        }
        if tokio::time::timeout_at(deadline, changes.changed())
            .await
            .is_err()
        {
            return Ok(Json(page));
        }
    }
}
async fn groups(State(relay): State<Relay>) -> ApiResult<Value> {
    Ok(Json(json!({"groups":relay.rooms().map_err(error)?})))
}
async fn health() -> impl IntoResponse {
    Json(json!({"service":"paramo1d-relay","protocol":1,"ok":true}))
}
pub fn router(relay: Relay) -> Router {
    Router::new()
        .route("/healthz", get(health))
        .route("/v1/messages", post(publish))
        .route("/v1/groups", get(groups))
        .route("/v1/groups/{room}/messages", get(group))
        .route("/v1/inbox/{recipient}", get(inbox))
        .route("/v1/sync/{recipient}", get(sync))
        .layer(DefaultBodyLimit::max(MAX_ENVELOPE))
        .with_state(relay)
}

#[cfg(test)]
mod tests {
    use super::*;
    use paramo1d_courier::{Identity, Message};
    #[tokio::test]
    async fn synchronization_waits_for_delivery_and_binds_both_cursors() {
        use axum::{body::Body, http::Request};
        use tower::ServiceExt;
        let dir = tempfile::tempdir().unwrap();
        let relay = Relay::open(&dir.path().join("messages.db")).unwrap();
        let alice = Identity::from_seed(&[1; 32]);
        let a = alice.contact("Alice".into(), "o1fixture".into()).unwrap();
        let bob = Identity::from_seed(&[2; 32]);
        let b = bob.contact("Bob".into(), "o1fixture".into()).unwrap();
        let now = now_ms();
        let path = format!(
            "/v1/sync/{}?group_after=0&inbox_after=0&wait_ms=10000",
            b.id
        );
        let signature = bob.read_authorization(&path, now);
        let request = |uri: &str| {
            Request::get(uri)
                .header("x-paramo1d-time", now.to_string())
                .header("x-paramo1d-signature", &signature)
                .body(Body::empty())
                .unwrap()
        };
        let app = router(relay.clone());
        let wrong = path.replace("group_after=0", "group_after=1");
        assert_ne!(
            app.clone().oneshot(request(&wrong)).await.unwrap().status(),
            StatusCode::OK
        );
        let response = tokio::spawn(app.oneshot(request(&path)));
        tokio::task::yield_now().await;
        assert!(!response.is_finished());
        let packet = alice
            .seal(
                a,
                Destination::Direct { contact: b },
                Message::Text {
                    text: "wake without the polling interval".into(),
                },
                now,
            )
            .unwrap();
        relay.publish(packet.clone(), now).unwrap();
        let response = tokio::time::timeout(std::time::Duration::from_secs(2), response)
            .await
            .unwrap()
            .unwrap()
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(response.into_body(), MAX_REPLY_BYTES)
            .await
            .unwrap();
        let page: SyncPage = serde_json::from_slice(&bytes).unwrap();
        assert!(page.group.messages.is_empty());
        assert_eq!(page.inbox.messages.len(), 1);
        assert_eq!(page.inbox.messages[0].envelope.id, packet.id);
        assert!(!String::from_utf8_lossy(&bytes).contains("wake without the polling interval"));
    }
    #[tokio::test]
    async fn synchronization_releases_idle_waiters_and_bounds_capacity() {
        use axum::{body::Body, http::Request};
        use tower::ServiceExt;
        let dir = tempfile::tempdir().unwrap();
        let relay = Relay::open(&dir.path().join("messages.db")).unwrap();
        let id = Identity::from_seed(&[3; 32]);
        let contact = id.contact("Reader".into(), "o1fixture".into()).unwrap();
        let now = now_ms();
        let path = format!(
            "/v1/sync/{}?group_after=0&inbox_after=0&wait_ms=10",
            contact.id
        );
        let request = || {
            Request::get(&path)
                .header("x-paramo1d-time", now.to_string())
                .header("x-paramo1d-signature", id.read_authorization(&path, now))
                .body(Body::empty())
                .unwrap()
        };
        let permits = relay.readers.acquire_many(256).await.unwrap();
        let app = router(relay.clone());
        assert_eq!(
            app.clone().oneshot(request()).await.unwrap().status(),
            StatusCode::SERVICE_UNAVAILABLE
        );
        drop(permits);
        let response =
            tokio::time::timeout(std::time::Duration::from_secs(1), app.oneshot(request()))
                .await
                .unwrap()
                .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        assert_eq!(relay.readers.available_permits(), 256);
    }
    #[test]
    fn queued_messages_survive_restart_deduplicate_and_preserve_cursor() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("messages.db");
        let relay = Relay::open(&path).unwrap();
        let key = Identity::from_seed(&[7; 32]);
        let sender = key.contact("Nemo".into(), "o1test".into()).unwrap();
        let now = now_ms();
        let envelope = key
            .seal(
                sender,
                Destination::Group {
                    room: "parano1d".into(),
                },
                Message::Text {
                    text: "persistent".into(),
                },
                now,
            )
            .unwrap();
        let first = relay.publish(envelope.clone(), now).unwrap();
        assert_eq!(relay.publish(envelope, now).unwrap(), first);
        drop(relay);
        let relay = Relay::open(&path).unwrap();
        let page = relay.read("room", "parano1d", 0, 50, now).unwrap();
        assert_eq!(page.messages.len(), 1);
        assert_eq!(page.cursor, first);
        assert!(relay
            .read("room", "parano1d", first, 50, now)
            .unwrap()
            .messages
            .is_empty());
        assert!(relay
            .read(
                "room",
                "parano1d",
                0,
                50,
                now + paramo1d_courier::MAX_LIFETIME_MS
            )
            .unwrap()
            .messages
            .is_empty());
    }
    #[test]
    fn reports_replace_only_the_same_helpers_older_status() {
        let dir = tempfile::tempdir().unwrap();
        let relay = Relay::open(&dir.path().join("messages.db")).unwrap();
        let now = now_ms();
        let alice = Identity::from_seed(&[1; 32]);
        let a = alice.contact("Alice".into(), "o1fixture".into()).unwrap();
        let bob = Identity::from_seed(&[2; 32]);
        let b = bob.contact("Bob".into(), "o1fixture".into()).unwrap();
        let report = |key: &Identity, contact: paramo1d_courier::Contact, stage: &str, time| {
            key.seal(
                contact,
                Destination::Group { room: LOBBY.into() },
                Message::RelayUpdate {
                    txid: "aa".repeat(32),
                    stage: stage.into(),
                    receipt_hex: None,
                },
                time,
            )
            .unwrap()
        };
        let first = relay
            .publish(report(&alice, a.clone(), "submitted", now), now)
            .unwrap();
        relay
            .publish(report(&bob, b, "submitted", now), now)
            .unwrap();
        let latest = relay
            .publish(report(&alice, a.clone(), "in_mempool", now + 1), now + 1)
            .unwrap();
        assert!(latest > first);
        assert_eq!(
            relay
                .publish(report(&alice, a, "submitted", now), now + 1)
                .unwrap(),
            latest
        );
        let page = relay.read("room", LOBBY, 0, 50, now + 1).unwrap();
        assert_eq!(page.messages.len(), 2);
        assert!(page.messages.iter().any(|d|matches!(d.envelope.public_message().unwrap(),Some(Message::RelayUpdate{stage,..}) if stage=="in_mempool")));
        assert_eq!(
            relay
                .read("room", LOBBY, first, 50, now + 1)
                .unwrap()
                .messages
                .len(),
            2
        );
    }
    #[tokio::test]
    async fn inbox_http_requires_the_exact_signed_path_and_preserves_encryption() {
        use axum::{body::Body, http::Request};
        use tower::ServiceExt;
        let dir = tempfile::tempdir().unwrap();
        let relay = Relay::open(&dir.path().join("messages.db")).unwrap();
        let now = now_ms();
        let alice = Identity::from_seed(&[1; 32]);
        let a = alice.contact("Alice".into(), "o1fixture".into()).unwrap();
        let bob = Identity::from_seed(&[2; 32]);
        let b = bob.contact("Bob".into(), "o1fixture".into()).unwrap();
        let envelope = alice
            .seal(
                a,
                Destination::Direct { contact: b.clone() },
                Message::Text {
                    text: "private delivery fixture".into(),
                },
                now,
            )
            .unwrap();
        let app = router(relay);
        let response = app
            .clone()
            .oneshot(
                Request::post("/v1/messages")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&envelope).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let path = format!("/v1/inbox/{}?after=0", b.id);
        let response = app
            .clone()
            .oneshot(Request::get(&path).body(Body::empty()).unwrap())
            .await
            .unwrap();
        assert_ne!(response.status(), StatusCode::OK);
        let signature = bob.read_authorization(&path, now);
        let response = app
            .clone()
            .oneshot(
                Request::get(&path)
                    .header("x-paramo1d-time", now.to_string())
                    .header("x-paramo1d-signature", &signature)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), MAX_REPLY_BYTES)
            .await
            .unwrap();
        assert!(!String::from_utf8_lossy(&body).contains("private delivery fixture"));
        let page: Page = serde_json::from_slice(&body).unwrap();
        assert_eq!(
            bob.open(&page.messages[0].envelope, now).unwrap(),
            Message::Text {
                text: "private delivery fixture".into()
            }
        );
        let changed = format!("/v1/inbox/{}?after=1", b.id);
        let response = app
            .oneshot(
                Request::get(changed)
                    .header("x-paramo1d-time", now.to_string())
                    .header("x-paramo1d-signature", signature)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_ne!(response.status(), StatusCode::OK);
    }
}
