use clap::Parser;
use std::{net::SocketAddr, path::PathBuf};
#[derive(Parser)]
struct Arguments {
    #[arg(long, default_value = "127.0.0.1:9711")]
    listen: SocketAddr,
    #[arg(long, default_value = "./relay-data/messages.db")]
    database: PathBuf,
    #[arg(
        long,
        help = "Loopback RPC endpoint for public wallet data and transaction submission"
    )]
    node_rpc: Option<String>,
}
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    let relay = paramo1d_relay::Relay::open(&args.database)?;
    let listener = tokio::net::TcpListener::bind(args.listen).await?;
    eprintln!("Paramo1d delivery listening on {}", listener.local_addr()?);
    let mut router = paramo1d_relay::router(relay);
    if let Some(endpoint) = args.node_rpc {
        router = router.merge(paramo1d_relay::gateway::router(&endpoint)?);
    }
    axum::serve(listener, router)
        .with_graceful_shutdown(async {
            let _ = tokio::signal::ctrl_c().await;
        })
        .await?;
    Ok(())
}
