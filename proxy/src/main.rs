#![deny(clippy::all)]

use anyhow::{bail, Result};
use futures_util::StreamExt;
use reqwest::header::HeaderMap;
use reqwest::redirect::Policy as RedirectPolicy;
use reqwest::{Client, Method, Proxy, Response};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::{self, Read};
use std::io::{BufRead, Write};
use std::process::ExitCode;
use std::str::FromStr;
use std::time::Duration;
use url::Url;

// Expose a different `config` implementation depending on whether the
// `qubesdb` feature is enabled.
#[cfg(feature = "qubesdb")]
mod config_qubesdb;
#[cfg(feature = "qubesdb")]
use config_qubesdb as config;

#[cfg(not(feature = "qubesdb"))]
mod config_env;
#[cfg(not(feature = "qubesdb"))]
use config_env as config;

// This is the only setting we need to read via `config`. Refactor this more
// extensibly if more settings are needed.
const ENV_CONFIG: &str = "SD_PROXY_ORIGIN";
const DISABLE_TOR: &str = "DISABLE_TOR";

// Read a max of 5MB from stdin. This should be much higher than what a
// server w/ 1k sources needs (~300KB), but still low enough to prevent a DoS.
const STDIN_LIMIT: u64 = 5_000_000;
const STREAM_ERROR_BODY_MAX_BYTES: usize = 64 * 1024;

/// Incoming HTTP requests (as JSON) received over stdin
#[derive(Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct IncomingRequest {
    method: String,
    path_query: String,
    stream: bool,
    #[serde(default)]
    headers: HashMap<String, String>,
    body: Option<String>,
    #[serde(default = "default_timeout")]
    timeout: u64, // sec
}

/// Default timeout for requests; serde requires this be a function.  To avoid
/// timeout confusion, clients of this proxy SHOULD either:
/// 1. invoke this proxy with the same or a longer process-level timeout; or
/// 2. explicitly override the timeout at the request level.
fn default_timeout() -> u64 {
    10
}

/// Serialization format for non-streamed HTTP responses
#[derive(Serialize, Debug)]
struct OutgoingResponse {
    status: u16,
    headers: HashMap<String, String>,
    body: String,
}

/// Serialization format for streamed HTTP responses
#[derive(Serialize, Debug)]
struct StreamMetadataResponse {
    status: u16,
    headers: HashMap<String, String>,
}

/// Serialization format for proxy execution errors, always over stderr
#[derive(Serialize, Debug)]
struct ErrorResponse {
    error: String,
}

/// Convert response headers to a `HashMap` for JSON serialization.
///
/// TODO(#1780): support duplicate HTTP headers
fn headers_to_map(resp: &Response) -> Result<HashMap<String, String>> {
    let mut headers = HashMap::new();
    for (name, value) in resp.headers() {
        headers.insert(name.to_string(), value.to_str()?.to_string());
    }
    Ok(headers)
}

/// Convert a non-streamed response to an `OutgoingResponse` and serialize it on stdout.
async fn handle_json_response(resp: Response) -> Result<()> {
    let headers = headers_to_map(&resp)?;
    let outgoing_response = OutgoingResponse {
        status: resp.status().as_u16(),
        headers,
        body: resp.text().await?,
    };
    println!("{}", serde_json::to_string(&outgoing_response)?);
    Ok(())
}

/// Serialize an HTTP error for a stream request without reading an unbounded body.
async fn handle_stream_error_response(resp: Response) -> Result<()> {
    let status = resp.status().as_u16();
    let headers = headers_to_map(&resp)?;
    let mut body = Vec::with_capacity(STREAM_ERROR_BODY_MAX_BYTES + 1);
    let mut stream = resp.bytes_stream();
    while let Some(item) = stream.next().await {
        let item = item?;
        let remaining = STREAM_ERROR_BODY_MAX_BYTES + 1 - body.len();
        body.extend_from_slice(&item[..item.len().min(remaining)]);
        if body.len() > STREAM_ERROR_BODY_MAX_BYTES {
            break;
        }
    }

    let body = if body.len() > STREAM_ERROR_BODY_MAX_BYTES {
        format!(
            "{}\n[response body truncated at {STREAM_ERROR_BODY_MAX_BYTES} bytes]",
            String::from_utf8_lossy(&body[..STREAM_ERROR_BODY_MAX_BYTES])
        )
    } else {
        String::from_utf8_lossy(&body).into_owned()
    };
    let outgoing_response = OutgoingResponse {
        status,
        headers,
        body,
    };
    println!("{}", serde_json::to_string(&outgoing_response)?);
    Ok(())
}

/// Given a `Response` that requires stream processing, forward it to stdout and write its
/// metadata to stderr when complete.
async fn handle_stream_response(resp: Response) -> Result<()> {
    // Get the headers, will be output later but we want to fail early if it's missing/invalid
    let status = resp.status().as_u16();
    let headers = headers_to_map(&resp)?;
    let mut stdout = io::stdout().lock();
    let mut stream = resp.bytes_stream();
    // Stream the response, printing bytes as we receive them
    while let Some(item) = stream.next().await {
        stdout.write_all(&item?)?;
        // TODO: can we flush at smarter intervals?
        stdout.flush()?;
    }
    // Emit the response metadata on stderr.
    eprintln!(
        "{}",
        serde_json::to_string(&StreamMetadataResponse { status, headers })?
    );
    Ok(())
}

/// Read one JSON request from stdin, make it, and emit either a streamed response or JSON.
async fn proxy() -> Result<()> {
    // Get the hostname from the environment or QubesDB
    let origin = config::read(ENV_CONFIG)?;

    // Read incoming request from stdin
    let mut buffer = String::new();
    // Limit stdin to 5MB; this should be much bigger than
    io::stdin()
        .lock()
        .take(STDIN_LIMIT)
        .read_line(&mut buffer)?;
    if buffer.len() == STDIN_LIMIT as usize && !buffer.ends_with('\n') {
        bail!("stdin is over the max bytes ({STDIN_LIMIT}), aborting");
    }
    let incoming_request: IncomingRequest = serde_json::from_str(&buffer)?;
    // We construct the URL by first parsing the origin and then appending the
    // path query. This forces the path query to be part of the path and prevents
    // it from getting itself into the hostname.
    let origin = Url::parse(&origin)?;
    // TODO: Consider just allowlisting a number of API paths instead of relying
    // on the url library to join it properly and avoid type confusion
    let url = origin.join(&incoming_request.path_query)?;
    // n.b. unclear how useful this check is, if Url::parse() is compromised,
    // then why do we trust url.origin()?
    // In any case, we know mixing URL parsers can be a security risk,
    // (c.f. https://daniel.haxx.se/blog/2022/01/10/dont-mix-url-parsers/)
    // and certainly there's no harm in the additional check.
    if url.origin() != origin.origin() {
        bail! {"request would escape configured origin"}
    }

    // Do not follow any redirects
    let mut builder = Client::builder().redirect(RedirectPolicy::none());
    // Ability to disable tor explicitly (for dev/testing purposes)
    if config::read(DISABLE_TOR).is_err() {
        builder = builder
            // the *h* in socks5h has the proxy (i.e. Tor) resolve DNS (*h*ostnames)
            .proxy(Proxy::all("socks5h://127.0.0.1:9150")?);
    }
    let client = builder.build()?;

    let mut req =
        client.request(Method::from_str(&incoming_request.method)?, url);
    let header_map = HeaderMap::try_from(&incoming_request.headers)?;
    req = req
        .headers(header_map)
        .timeout(Duration::from_secs(incoming_request.timeout));
    if let Some(body) = incoming_request.body {
        req = req.body(body);
    }
    // Fire off the request!
    let resp = req.send().await?;
    if incoming_request.stream
        && (resp.status().is_client_error() || resp.status().is_server_error())
    {
        handle_stream_error_response(resp).await?;
    } else if incoming_request.stream {
        handle_stream_response(resp).await?;
    } else {
        handle_json_response(resp).await?;
    }
    Ok(())
}

#[tokio::main(flavor = "current_thread")]
/// Handle one request and exit according to its success or failure.
async fn main() -> ExitCode {
    match proxy().await {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            let mut error = err.to_string();
            if let Some(source) = err.source() {
                error = format!("{}: {}", error, source);
            }
            // Try to serialize into our error format
            let resp = ErrorResponse { error };
            match serde_json::to_string(&resp) {
                Ok(json) => {
                    // Print the error to stderr
                    eprintln!("{json}")
                }
                Err(_) => {
                    // It should be near impossible that an error message
                    // is not JSON serializable, but just handle this corner
                    // case explicitly
                    // TODO: attempt to log underlying error
                    eprintln!(r#"{{"error": "unable to serialize error"}}"#)
                }
            };
            ExitCode::FAILURE
        }
    }
}
