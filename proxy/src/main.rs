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
use std::os::unix::net::UnixDatagram;
use std::process::ExitCode;
use std::str::FromStr;
use std::time::Duration;
use url::Url;

// Expose a different `config` implementation depending on whether the `qubesdb` feature is enabled or not.
#[cfg(feature = "qubesdb")]
mod config_qubesdb;
#[cfg(feature = "qubesdb")]
use config_qubesdb as config;

#[cfg(not(feature = "qubesdb"))]
mod config_env;
#[cfg(not(feature = "qubesdb"))]
use config_env as config;

// This is the only setting we need to read via `config`.  We should refactor this more extensibly if we ever need multiple.
const ENV_CONFIG: &str = "SD_PROXY_ORIGIN";
const DISABLE_TOR: &str = "DISABLE_TOR";

// Read a max of 5MB from stdin. This should be much higher than what a
// server w/ 1k sources needs (~300KB), but still low enough to prevent a DoS.
const STDIN_LIMIT: u64 = 5_000_000;

// Requests are tagged with an X-Request-ID header
const REQUEST_ID_HEADER: &str = "X-Request-ID";

/// Best-effort logger that writes to the local syslog socket, from where
/// messages are forwarded to sd-log by securedrop-log's rsyslog config.
///
/// stdout and stderr are the qrexec protocol channels back to the client, so
/// logs MUST NOT be written to either. If the syslog socket is unavailable
/// (e.g. in dev mode outside Qubes), messages are silently dropped: logging
/// must never fail a request.
struct Syslog {
    socket: Option<UnixDatagram>,
}

// RFC 3164 severities, within facility "user" (1)
const SYSLOG_WARNING: u8 = 4;
const SYSLOG_INFO: u8 = 6;

impl Syslog {
    fn new() -> Self {
        Self::connect("/dev/log")
    }

    fn connect(path: &str) -> Self {
        let socket = UnixDatagram::unbound()
            .ok()
            .filter(|socket| socket.connect(path).is_ok());
        Syslog { socket }
    }

    fn info(&self, message: &str) {
        self.log(SYSLOG_INFO, message);
    }

    fn warn(&self, message: &str) {
        self.log(SYSLOG_WARNING, message);
    }

    fn log(&self, severity: u8, message: &str) {
        if let Some(socket) = &self.socket {
            // RFC 3164 priority: facility "user" (1) * 8 + severity
            let line = format!(
                "<{}>securedrop-proxy[{}]: {}",
                8 + severity,
                std::process::id(),
                message
            );
            let _ = socket.send(line.as_bytes());
        }
    }
}

/// Whether `value` is a well-formed request ID: `req-` followed by a
/// lowercase UUID.  Anything else is stripped by `extract_request_id()` so
/// that a compromised client VM can't inject arbitrary strings into the
/// proxy's and server's logs.
fn valid_request_id(value: &str) -> bool {
    let Some(uuid) = value.strip_prefix("req-") else {
        return false;
    };
    if uuid.len() != 36 {
        return false;
    }
    uuid.chars().enumerate().all(|(i, c)| match i {
        8 | 13 | 18 | 23 => c == '-',
        _ => c.is_ascii_digit() || ('a'..='f').contains(&c),
    })
}

#[derive(Debug, PartialEq)]
enum RequestId {
    Valid(String),
    /// The malformed value, which has been stripped from the request
    Invalid(String),
    Missing,
}

/// Validate the request's X-Request-ID header.  A malformed one is removed
/// from the request: the Inbox always generates well-formed IDs, so a
/// malformed one means a broken (or compromised) client, which the caller
/// should log a warning about.  The request itself still proceeds either
/// way — request IDs are an observability aid, not a gate.
fn extract_request_id(headers: &mut HashMap<String, String>) -> RequestId {
    let Some(key) = headers
        .keys()
        .find(|key| key.eq_ignore_ascii_case(REQUEST_ID_HEADER))
        .cloned()
    else {
        return RequestId::Missing;
    };
    let value = headers[&key].clone();
    if valid_request_id(&value) {
        RequestId::Valid(value)
    } else {
        headers.remove(&key);
        RequestId::Invalid(value)
    }
}

/// The server's echoed X-Request-ID, formatted for appending to a log line.
fn echoed_request_id(resp: &Response) -> String {
    match resp
        .headers()
        .get(REQUEST_ID_HEADER)
        .and_then(|value| value.to_str().ok())
    {
        Some(echoed) => format!(" echoed={echoed}"),
        None => String::new(),
    }
}

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
    headers: HashMap<String, String>,
}

/// Serialization format for errors, always over stderr
#[derive(Serialize, Debug)]
struct ErrorResponse {
    error: String,
}

/// Convert `request::header::HeaderMap` to a `HashMap` that can be serialized to JSON on stdout.
///
/// TODO(#1780): support duplicate HTTP headers
fn headers_to_map(resp: &Response) -> Result<HashMap<String, String>> {
    let mut headers = HashMap::new();
    for (name, value) in resp.headers() {
        headers.insert(name.to_string(), value.to_str()?.to_string());
    }
    Ok(headers)
}

/// Given a `Response` that doesn't require stream processing, convert it to our `OutgoingResponse` and serialize to JSON on stdout.
async fn handle_json_response(
    resp: Response,
    request_id: &str,
    syslog: &Syslog,
) -> Result<()> {
    let headers = headers_to_map(&resp)?;
    let status = resp.status().as_u16();
    let echoed = echoed_request_id(&resp);
    let body = resp.text().await?;
    syslog.info(&format!(
        "{request_id} response: status={status} size={}{echoed}",
        body.len()
    ));
    let outgoing_response = OutgoingResponse {
        status,
        headers,
        body,
    };
    println!("{}", serde_json::to_string(&outgoing_response)?);
    Ok(())
}

/// Given a `Response` that does require stream processing, forward it to stdout as we receive it, and then write the headers to stderr when we're done.
async fn handle_stream_response(
    resp: Response,
    request_id: &str,
    syslog: &Syslog,
) -> Result<()> {
    // Get the headers, will be output later but we want to fail early if it's missing/invalid
    let headers = headers_to_map(&resp)?;
    let status = resp.status().as_u16();
    let echoed = echoed_request_id(&resp);
    let mut size: usize = 0;
    let mut stdout = io::stdout().lock();
    let mut stream = resp.bytes_stream();
    // Stream the response, printing bytes as we receive them
    while let Some(item) = stream.next().await {
        let item = item?;
        size += item.len();
        stdout.write_all(&item)?;
        // TODO: can we flush at smarter intervals?
        stdout.flush()?;
    }
    syslog.info(&format!(
        "{request_id} response: status={status} size={size} stream=true{echoed}"
    ));
    // Emit the headers as stderr
    eprintln!(
        "{}",
        serde_json::to_string(&StreamMetadataResponse { headers })?
    );
    Ok(())
}

/// Read a single JSON-serialized HTTP request from a single line from stdin and reconstruct it, including its URL.  Make the request, and stream the response if requested; otherwise, or in an error condition, return it as JSON.
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
    let mut incoming_request: IncomingRequest = serde_json::from_str(&buffer)?;
    let syslog = Syslog::new();
    let request_id = match extract_request_id(&mut incoming_request.headers) {
        RequestId::Valid(request_id) => request_id,
        RequestId::Invalid(value) => {
            // {:?} escapes control characters so the malformed value can't
            // inject anything into the logs; truncate it for good measure.
            syslog.warn(&format!(
                "stripped invalid X-Request-ID header: {:?}",
                value.chars().take(64).collect::<String>()
            ));
            // Apache-style placeholder in the log lines below
            "-".to_string()
        }
        RequestId::Missing => "-".to_string(),
    };
    syslog.info(&format!(
        "{request_id} request: method={} body_size={}",
        incoming_request.method,
        incoming_request.body.as_deref().map_or(0, str::len)
    ));
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
    let resp = match req.send().await {
        Ok(resp) => resp,
        Err(err) => {
            syslog.warn(&format!("{request_id} request failed: {err}"));
            return Err(err.into());
        }
    };
    // We return the output in two ways, either a JSON blob or stream the output.
    // JSON is used for HTTP 4xx, 5xx, and all non-stream requests.
    if !incoming_request.stream
        || resp.status().is_client_error()
        || resp.status().is_server_error()
    {
        handle_json_response(resp, &request_id, &syslog).await?;
    } else {
        handle_stream_response(resp, &request_id, &syslog).await?;
    }
    Ok(())
}

#[tokio::main(flavor = "current_thread")]
/// Entry-point: Every invocation handles a single request via `proxy()` and exits according to its success or failure.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_request_id() {
        assert!(valid_request_id("req-72d64b57-4632-4d3e-96b0-24a0428f7ec1"));
        // missing prefix
        assert!(!valid_request_id("72d64b57-4632-4d3e-96b0-24a0428f7ec1"));
        // wrong prefix
        assert!(!valid_request_id(
            "seq-72d64b57-4632-4d3e-96b0-24a0428f7ec1"
        ));
        // uppercase hex
        assert!(!valid_request_id(
            "req-72D64B57-4632-4D3E-96B0-24A0428F7EC1"
        ));
        // too short / too long / empty
        assert!(!valid_request_id("req-72d64b57"));
        assert!(!valid_request_id(
            "req-72d64b57-4632-4d3e-96b0-24a0428f7ec1ff"
        ));
        assert!(!valid_request_id(""));
        // non-hex, log-injection attempts
        assert!(!valid_request_id(
            "req-72d64b57-4632-4d3e-96b0-24a0428f7ecz"
        ));
        assert!(!valid_request_id("req-injected\nmessage into the logs!"));
    }

    #[test]
    fn test_extract_request_id_preserves_valid() {
        let valid = "req-72d64b57-4632-4d3e-96b0-24a0428f7ec1";
        // ... under any header-name casing
        for name in [REQUEST_ID_HEADER, "x-request-id"] {
            let mut headers =
                HashMap::from([(name.to_string(), valid.to_string())]);
            assert_eq!(
                extract_request_id(&mut headers),
                RequestId::Valid(valid.to_string())
            );
            assert_eq!(headers.len(), 1);
            assert_eq!(headers[name], valid);
        }
    }

    #[test]
    fn test_extract_request_id_missing() {
        let mut headers =
            HashMap::from([("Accept".to_string(), "*/*".to_string())]);
        assert_eq!(extract_request_id(&mut headers), RequestId::Missing);
        // Other headers are untouched
        assert_eq!(headers.len(), 1);
    }

    #[test]
    fn test_extract_request_id_strips_invalid() {
        let mut headers = HashMap::from([
            (
                REQUEST_ID_HEADER.to_string(),
                "not a request ID".to_string(),
            ),
            ("Accept".to_string(), "*/*".to_string()),
        ]);
        assert_eq!(
            extract_request_id(&mut headers),
            RequestId::Invalid("not a request ID".to_string())
        );
        // The malformed header is removed; other headers are untouched
        assert_eq!(headers.len(), 1);
        assert_eq!(headers["Accept"], "*/*");
    }

    #[test]
    fn test_syslog_message_format() {
        let path = std::env::temp_dir()
            .join(format!("sdproxy-test-syslog-{}", std::process::id()));
        let _ = std::fs::remove_file(&path);
        let receiver = UnixDatagram::bind(&path).unwrap();
        let mut buf = [0u8; 1024];

        let syslog = Syslog::connect(path.to_str().unwrap());

        syslog.info("req-x request: method=GET body_size=0");
        let n = receiver.recv(&mut buf).unwrap();
        let message = std::str::from_utf8(&buf[..n]).unwrap();
        assert!(message.starts_with("<14>securedrop-proxy["));
        assert!(message.ends_with("]: req-x request: method=GET body_size=0"));

        syslog.warn("stripped invalid X-Request-ID header: \"nope\"");
        let n = receiver.recv(&mut buf).unwrap();
        let message = std::str::from_utf8(&buf[..n]).unwrap();
        assert!(message.starts_with("<12>securedrop-proxy["));

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_syslog_unavailable_is_silently_dropped() {
        let syslog = Syslog::connect("/nonexistent/syslog/socket");
        // Must not panic or error
        syslog.info("req-x request: method=GET body_size=0");
    }
}
