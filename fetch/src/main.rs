use std::collections::HashSet;
use std::sync::{Arc, RwLock};

use anyhow::Result;
use clap::Parser;
use futures::{StreamExt, stream::FuturesUnordered};

mod cli_options;
mod db;
mod worker;

use cli_options::CliOptions;
use worker::{SharedSet, Worker};

#[tokio::main]
async fn main() -> Result<()> {
    let options = CliOptions::parse();
    let active_fetches: SharedSet<String> =
        Arc::new(RwLock::new(HashSet::new()));

    let mut worker_handles: FuturesUnordered<_> = (0..options
        .num_concurrent_workers)
        .map(|_| {
            let db = options.db.clone();
            let active_fetches = active_fetches.clone();
            tokio::spawn(async move { Worker::spawn(db, active_fetches) })
        })
        .collect();

    while let Some(handle_result) = worker_handles.next().await {
        match handle_result {
            Ok(worker_result) => {
                if let Err(e) = worker_result {
                    eprintln!("worker error: {:?}", e);
                }
            }
            Err(e) => {
                eprintln!("join error: {:?}", e);
            }
        }
    }

    Ok(())
}
