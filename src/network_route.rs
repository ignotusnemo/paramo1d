//! The protected route uses an authenticated loopback proxy owned by this process.
use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD, Engine};
use futures::future::BoxFuture;
use libp2p::{
    core::transport::{DialOpts, ListenerId, TransportError, TransportEvent},
    multiaddr::Protocol,
    Multiaddr, Transport,
};
use std::{
    io,
    pin::Pin,
    sync::RwLock,
    task::{Context as TaskContext, Poll},
    time::Duration,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio_util::compat::{Compat, TokioAsyncReadCompatExt};

#[derive(Clone, PartialEq, Eq)]
pub struct Route {
    pub port: u16,
    token: String,
}
static ROUTE: RwLock<Option<Route>> = RwLock::new(None);
pub fn current() -> Option<Route> {
    ROUTE.read().expect("route lock").clone()
}
pub fn set(port: Option<u16>, token: &str) -> Result<()> {
    let route = if let Some(port) = port {
        ensure!(
            port >= 1024 && token.len() == 64 && token.bytes().all(|v| v.is_ascii_hexdigit()),
            "Invalid protected route"
        );
        Some(Route {
            port,
            token: token.into(),
        })
    } else {
        None
    };
    *ROUTE.write().expect("route lock") = route;
    Ok(())
}
pub fn client(
    builder: reqwest::blocking::ClientBuilder,
) -> Result<reqwest::blocking::ClientBuilder> {
    Ok(if let Some(route) = current() {
        builder.proxy(
            reqwest::Proxy::all(format!("http://127.0.0.1:{}", route.port))?
                .basic_auth("paramo1d", &route.token),
        )
    } else {
        builder
    })
}
impl Route {
    async fn connect(&self, target: &str) -> io::Result<tokio::net::TcpStream> {
        let mut stream =
            tokio::net::TcpStream::connect((std::net::Ipv4Addr::LOCALHOST, self.port)).await?;
        stream.set_nodelay(true)?;
        let auth = STANDARD.encode(format!("paramo1d:{}", self.token));
        stream.write_all(format!("CONNECT {target} HTTP/1.1\r\nHost: {target}\r\nProxy-Authorization: Basic {auth}\r\n\r\n").as_bytes()).await?;
        let mut header = Vec::new();
        while !header.ends_with(b"\r\n\r\n") {
            if header.len() >= 8192 {
                return Err(io::Error::other(
                    "Protected connection response exceeds limit",
                ));
            };
            header.push(stream.read_u8().await?);
        }
        let status = std::str::from_utf8(&header)
            .unwrap_or("")
            .lines()
            .next()
            .unwrap_or("")
            .split_whitespace()
            .nth(1);
        if status != Some("200") {
            return Err(io::Error::other("Protected connection unavailable"));
        };
        Ok(stream)
    }
}
#[derive(Clone)]
pub struct ProxyTcp(pub Route);
impl Transport for ProxyTcp {
    type Output = Compat<tokio::net::TcpStream>;
    type Error = io::Error;
    type ListenerUpgrade = futures::future::Pending<io::Result<Self::Output>>;
    type Dial = BoxFuture<'static, io::Result<Self::Output>>;
    fn listen_on(
        &mut self,
        _: ListenerId,
        address: Multiaddr,
    ) -> std::result::Result<(), TransportError<Self::Error>> {
        Err(TransportError::MultiaddrNotSupported(address))
    }
    fn remove_listener(&mut self, _: ListenerId) -> bool {
        false
    }
    fn dial(
        &mut self,
        address: Multiaddr,
        _: DialOpts,
    ) -> std::result::Result<Self::Dial, TransportError<Self::Error>> {
        let mut parts = address.iter();
        let host = match parts.next() {
            Some(Protocol::Dns(v) | Protocol::Dns4(v)) => v.to_string(),
            _ => return Err(TransportError::MultiaddrNotSupported(address)),
        };
        let port = match parts.next() {
            Some(Protocol::Tcp(v)) => v,
            _ => return Err(TransportError::MultiaddrNotSupported(address)),
        };
        if !noid_chain::consensus::network::NetworkConfig::mainnet()
            .dns_seeds
            .contains(&host.as_str())
            || port != 9600
        {
            return Err(TransportError::MultiaddrNotSupported(address));
        }
        if parts.next().is_some() {
            return Err(TransportError::MultiaddrNotSupported(address));
        };
        let route = self.0.clone();
        Ok(Box::pin(async move {
            tokio::time::timeout(
                Duration::from_secs(25),
                route.connect(&format!("{host}:{port}")),
            )
            .await
            .map_err(|_| {
                io::Error::new(
                    io::ErrorKind::TimedOut,
                    "Protected peer connection timed out",
                )
            })?
            .map(TokioAsyncReadCompatExt::compat)
        }))
    }
    fn poll(
        self: Pin<&mut Self>,
        _: &mut TaskContext<'_>,
    ) -> Poll<TransportEvent<Self::ListenerUpgrade, Self::Error>> {
        Poll::Pending
    }
}
pub fn transport(
    key: &libp2p::identity::Keypair,
) -> Result<libp2p::core::transport::Boxed<(libp2p::PeerId, libp2p::core::muxing::StreamMuxerBox)>>
{
    let noise = libp2p::noise::Config::new(key).context("P2P transport authentication")?;
    let boxed = if let Some(route) = current() {
        ProxyTcp(route)
            .upgrade(libp2p::core::upgrade::Version::V1Lazy)
            .authenticate(noise)
            .multiplex(libp2p::yamux::Config::default())
            .timeout(Duration::from_secs(30))
            .map(|(id, mux), _| (id, libp2p::core::muxing::StreamMuxerBox::new(mux)))
            .boxed()
    } else {
        libp2p::tcp::tokio::Transport::new(libp2p::tcp::Config::default().nodelay(true))
            .upgrade(libp2p::core::upgrade::Version::V1Lazy)
            .authenticate(noise)
            .multiplex(libp2p::yamux::Config::default())
            .timeout(Duration::from_secs(30))
            .map(|(id, mux), _| (id, libp2p::core::muxing::StreamMuxerBox::new(mux)))
            .boxed()
    };
    Ok(boxed)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[tokio::test]
    async fn protected_stream_keeps_payload_and_authenticates_local_proxy() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let task = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut request = Vec::new();
            while !request.ends_with(b"\r\n\r\n") {
                request.push(stream.read_u8().await.unwrap());
            }
            let request = String::from_utf8(request).unwrap();
            assert!(request.starts_with("CONNECT mseed1.parano1d.org:9600 HTTP/1.1\r\n"));
            assert!(request.contains(&STANDARD.encode(format!("paramo1d:{}", "ab".repeat(32)))));
            stream
                .write_all(b"HTTP/1.1 200 Connection Established\r\n\r\nnoise-payload")
                .await
                .unwrap();
        });
        let route = Route {
            port,
            token: "ab".repeat(32),
        };
        let mut stream = route.connect("mseed1.parano1d.org:9600").await.unwrap();
        let mut body = Vec::new();
        stream.read_to_end(&mut body).await.unwrap();
        assert_eq!(body, b"noise-payload");
        task.await.unwrap();
    }
    #[tokio::test]
    async fn refused_proxy_does_not_open_a_direct_connection() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let task = tokio::spawn(async move {
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut input = Vec::new();
            while !input.ends_with(b"\r\n\r\n") {
                input.push(stream.read_u8().await.unwrap());
            }
            stream
                .write_all(b"HTTP/1.1 403 Forbidden\r\n\r\n")
                .await
                .unwrap();
        });
        assert!(Route {
            port,
            token: "ab".repeat(32)
        }
        .connect("mseed1.parano1d.org:9600")
        .await
        .is_err());
        task.await.unwrap();
    }
}
