use std::{env, net::TcpStream, str::FromStr};

use anyhow::Context;
use simple_https_client::tls13client;
use tracing_subscriber;

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

        let host = args.next().unwrap_or("www.google.com".to_string());
        let port = args.next().unwrap_or("443".to_string());

        (
            host,
            u16::from_str(&port).context("Failed to parse port number.")?,
        )
    };

    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);

    // Initiate HTTPS connection to host:port.
    let stream = TcpStream::connect((host.clone(), port))?;

    let (_, _, response_prefix) = tls13client(&host, stream, &request)?;

    println!("[!] Received HTTP response (prefix):");
    println!("{}", String::from_utf8_lossy(&response_prefix));
    println!("[!] Connection to \"{}:{}\" succeeded.", host, port);

    Ok(())
}
