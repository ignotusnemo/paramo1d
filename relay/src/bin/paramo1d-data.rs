//! Public wallet data from an existing node, with a fixed RPC allowlist.
use clap::Parser;
#[derive(Parser)]
struct Arguments {
    #[arg(long, default_value = "127.0.0.1:9714")]
    listen: std::net::SocketAddr,
    #[arg(long, default_value = "http://127.0.0.1:19601")]
    node_rpc: String,
}
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Arguments::parse();
    anyhow::ensure!(
        args.listen.ip().is_loopback(),
        "Bind the data gateway to loopback"
    );
    let listener = tokio::net::TcpListener::bind(args.listen).await?;
    axum::serve(listener, paramo1d_relay::gateway::router(&args.node_rpc)?)
        .with_graceful_shutdown(async {
            let _ = tokio::signal::ctrl_c().await;
        })
        .await?;
    Ok(())
}
