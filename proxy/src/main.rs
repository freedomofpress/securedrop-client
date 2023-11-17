#![deny(clippy::all)]

use anyhow::{bail, Result};
use futures_util::StreamExt;
use reqwest::header::HeaderMap;
use reqwest::Method;
use reqwest::{Client, Response};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::Write;
use std::process::ExitCode;
use std::str::FromStr;
use std::time::Duration;
use std::{env, io};
use url::Url;

const ENV_CONFIG: &str = "SD_PROXY_ORIGIN";

/// Incoming requests (as JSON) received over stdin
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
    timeout: u64,
}

/// Default timeout for requests; serde requires this be a function
fn default_timeout() -> u64 {
    10
}

/// Serialization format for non-streamed requests
#[derive(Serialize, Debug)]
struct OutgoingResponse {
    status: u16,
    headers: HashMap<String, String>,
    body: String,
}

/// In a streamed response, we emit the checksum after the streaming finishes
#[derive(Serialize, Debug)]
struct StreamMetadataResponse {
    headers: HashMap<String, String>,
}

/// Serialization format for errors, always over stderr
#[derive(Serialize, Debug)]
struct ErrorResponse {
    error: String,
}

fn headers_to_map(resp: &Response) -> Result<HashMap<String, String>> {
    let mut headers = HashMap::new();
    for (name, value) in resp.headers() {
        headers.insert(name.to_string(), value.to_str()?.to_string());
    }
    Ok(headers)
}

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

async fn handle_stream_response(resp: Response) -> Result<()> {
    // Get the headers, will be output later but we want to fail early if it's missing/invalid
    let headers = headers_to_map(&resp)?;
    let mut stdout = io::stdout().lock();
    let mut stream = resp.bytes_stream();
    // Stream the response, printing bytes as we receive them
    while let Some(item) = stream.next().await {
        stdout.write_all(&item?)?;
        // TODO: can we flush at smarter intervals?
        stdout.flush()?;
    }
    // Emit the headers as stderr
    eprintln!(
        "{}",
        serde_json::to_string(&StreamMetadataResponse { headers })?
    );
    Ok(())
}

async fn proxy() -> Result<()> {
    // Get the hostname from the environment
    let origin = env::var(ENV_CONFIG)?;
    // Read incoming request from stdin (must be on single line)
    let mut buffer = String::new();
    io::stdin().read_line(&mut buffer)?;
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

    let client = Client::new();
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
    // We return the output in two ways, either a JSON blob or stream the output.
    // JSON is used for HTTP 4xx, 5xx, and all non-stream requests.
    if !incoming_request.stream
        || resp.status().is_client_error()
        || resp.status().is_server_error()
    {
        handle_json_response(resp).await?;
    } else {
        handle_stream_response(resp).await?;
    }
    Ok(())
}

#[tokio::main(flavor = "current_thread")]
async fn main() -> ExitCode {
    match proxy().await {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            // Try to serialize into our error format
            let resp = ErrorResponse {
                error: err.to_string(),
            };
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
