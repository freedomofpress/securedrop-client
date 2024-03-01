use anyhow::Result;
use std::env;

pub fn read(name: &str) -> Result<String> {
    Ok(env::var(name)?)
}
