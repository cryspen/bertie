use simple_https_client::tls13client;
use std::{env, str::FromStr};

/// This is a demo of a simple HTTPS client.
///
/// The client connects to host:port via TCP, executes a TLS 1.3 handshake,
/// sends an encrypted HTTP GET, and prints the servers HTTP response.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Obtain host and port from arguments.
    let (host, port) = {
        let mut args = env::args();

        let _ = args.next().ok_or("Unexpected environment.")?;

        let host = args.next().unwrap_or("www.google.com".to_string());
        let port = args.next().unwrap_or("443".to_string());

        (host, u16::from_str(&port)?)
    };

    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);

    // Initiate HTTPS connection to host:port.
    match tls13client(&host, port, &request) {
        Ok((_, _, response_prefix)) => {
            println!("[!] Received HTTP response (prefix):");
            println!("{}", String::from_utf8_lossy(&response_prefix));
            println!("[!] Connection to \"{}:{}\" succeeded.", host, port);
        }
        Err(error) => {
            println!(
                "[!] Connection to \"{}:{}\" failed with ...\n\n\t{}\n\n.",
                host, port, error
            );
        }
    }

    Ok(())
}
