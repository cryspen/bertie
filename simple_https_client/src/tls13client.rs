use std::{env, net::TcpStream, str::FromStr};

use anyhow::Context;
use bertie::{tls13utils::*};
use record::AppError;
use simple_https_client::{ciphersuites, tls13client};
use tracing::{error, trace};

/// This is a demo of a simple HTTPS client.
///
/// The client connects to host:port via TCP, executes a TLS 1.3 handshake,
/// sends an encrypted HTTP GET, and prints the servers HTTP response.
fn main() -> anyhow::Result<()> {
    // Setup tracing.
    tracing_subscriber::fmt::init();

    // Obtain host and port from arguments.
    let (host, port) = {
        let mut args = env::args();

        let _ = args.next().context("Unexpected parameter environment.")?;

        let host = args.next().unwrap_or_else(|| "www.google.com".to_string());
        let port = args.next().unwrap_or_else(|| "443".to_string());

        (
            host,
            u16::from_str(&port).context("Failed to parse port number.")?,
        )
    };

    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);

    // FIXME: #51 This is going to go away as soon as Bertie supports multiple
    //        ciphersuites.
    let mut ciphersuites = ciphersuites();
    let mut response_prefix = Vec::new();
    for algorithms in ciphersuites.drain(..) {
        // Initiate HTTPS connection to host:port.
        let stream = TcpStream::connect((host.clone(), port))?;
        stream.set_nodelay(true).expect("set_nodelay call failed");
        trace!(
            host = format!("{}:{}", host, port),
            "Opened TCP connection to host."
        );

        response_prefix = match tls13client(&host, stream, algorithms, &request) {
            Ok((_, _, response_prefix)) => response_prefix,
            Err(e) => {
                // We ignore all errors here for now and keep trying.
                eprintln!("tls13connet failed with {}", e);
                continue;
            }
        };
        break;
    }
    if response_prefix.is_empty() {
        error!("Unable to connect with the configured ciphersuites.");
        return Err(AppError::TLS(UNSUPPORTED_ALGORITHM.into()).into());
    }

    println!("[!] Received HTTP response (prefix):");
    println!("{}", String::from_utf8_lossy(&response_prefix));
    println!("[!] Connection to \"{}:{}\" succeeded.", host, port);

    Ok(())
}
