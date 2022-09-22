//! A Simple TLS 1.3 HTTP Server Implementation
//! It waits for a connection at port 443, receives an HTTP "GET /", and prints a constant string
//! WARNING: This code is not in hacspec since it need to use TCP etc.

use anyhow::Context;
use std::str::FromStr;
use std::{env, net::TcpListener, time::Duration};
use tracing_subscriber;

use simple_https_server::tls13server;

pub fn main() -> anyhow::Result<()> {
    // Setup tracing.
    tracing_subscriber::fmt::init();

    // Obtain host and port from arguments.
    let (host, port) = {
        let mut args = env::args();

        let _ = args.next().context("Unexpected parameter environment.")?;

        let host = args.next().unwrap_or("localhost".to_string());
        let port = args.next().unwrap_or("443".to_string());

        (
            host,
            u16::from_str(&port).context("Failed to parse port number.")?,
        )
    };

    let listener = TcpListener::bind((host.as_str(), port)).unwrap();

    for stream in listener.incoming() {
        let mut stream = stream.unwrap();

        let d = Duration::new(15, 0);
        stream
            .set_read_timeout(Some(d))
            .expect("set_read_timeout call failed");
        println!("New connection established!");
        match tls13server(&mut stream, &host) {
            Ok(()) => {
                println!("Connection to {} succeeded\n", host);
            }
            Err(error) => {
                println!("Connection to {} failed with {:?}\n", host, error);
            }
        }
    }

    Ok(())
}
