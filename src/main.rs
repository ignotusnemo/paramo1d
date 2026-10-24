use anyhow::Result;
use clap::{Parser, Subcommand};
use paramo1d::{artifacts, MatrixMode};
use std::path::PathBuf;
mod mobile;

#[derive(Parser)]
#[command(
    name = "paramo1d",
    version,
    about = "Independent Parano1d verification"
)]
struct Arguments {
    #[arg(long, help = "Verification workers. Defaults to all available CPUs")]
    threads: Option<usize>,
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    Profile,
    Run {
        #[arg(long)]
        artifacts: PathBuf,
        #[arg(long)]
        data_dir: PathBuf,
        #[arg(long)]
        once: bool,
    },
    Export {
        #[arg(long)]
        node_data: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        height: Option<u64>,
    },
    Prepare {
        #[arg(long)]
        source: PathBuf,
        #[arg(long)]
        artifacts: PathBuf,
    },
    PrepareCaches {
        #[arg(long)]
        artifacts: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long, value_delimiter = ',')]
        classes: Vec<String>,
    },
    Fetch {
        #[arg(long)]
        rpc: String,
        #[arg(long)]
        origins: PathBuf,
        #[arg(long)]
        output: PathBuf,
    },
    Verify {
        #[arg(long)]
        artifacts: PathBuf,
        #[arg(long)]
        bundle: PathBuf,
        #[arg(long, value_enum, default_value_t = MatrixMode::Streaming)]
        matrix_mode: MatrixMode,
        #[arg(long, default_value_t = 1)]
        repeat: u8,
    },
}

fn main() -> Result<()> {
    let args = Arguments::parse();
    let workers = paramo1d::resolve_workers(args.threads)?;
    rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build_global()?;
    let result = match args.command {
        Command::Export {
            node_data,
            output,
            height,
        } => paramo1d::collector::export(&node_data, &output, height)?,
        Command::Profile => serde_json::to_value(artifacts::profile())?,
        Command::Run {
            artifacts,
            data_dir,
            once,
        } => mobile::run(artifacts, data_dir, once)?,
        Command::Prepare { source, artifacts } => artifacts::prepare(&source, &artifacts)?,
        Command::PrepareCaches {
            artifacts,
            output,
            classes,
        } => artifacts::prepare_selected_caches(&artifacts, &output, &classes)?,
        Command::Fetch {
            rpc,
            origins,
            output,
        } => paramo1d::rpc::fetch(&rpc, &origins, &output)?,
        Command::Verify {
            artifacts,
            bundle,
            matrix_mode,
            repeat,
        } => {
            anyhow::ensure!((1..=8).contains(&repeat), "verification repeat limit");
            if repeat == 1 {
                serde_json::to_value(paramo1d::verify_bundle(&artifacts, &bundle, matrix_mode)?)?
            } else {
                let mut verifier = paramo1d::Verifier::open(&artifacts, matrix_mode)?;
                let results = (0..repeat)
                    .map(|_| verifier.verify_bundle(&bundle))
                    .collect::<Result<Vec<_>>>()?;
                serde_json::to_value(results)?
            }
        }
    };
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
