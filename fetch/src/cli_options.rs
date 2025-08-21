use clap::Parser;

#[derive(Parser, Debug)]
pub struct CliOptions {
    #[arg(long)]
    pub num_concurrent_workers: u64,

    #[arg(long)]
    pub db: String,
    // TODO(vicki):
    // sd-proxy config
    // db string
}
