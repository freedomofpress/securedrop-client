use anyhow::Result;
use std::env;

/// Just a helper function for reading the named variable from the environment, for isomorphism with `config_qubesdb::read()`.
pub fn read(name: &str) -> Result<String> {
    Ok(env::var(name)?)
}
