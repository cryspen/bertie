//! A Simple TLS 1.3 HTTP Server Implementation
//! It waits for a connection at port 443, receives an HTTP "GET /", and prints a constant string
//! WARNING: This code is not in hacspec since it need to use TCP etc.

use std::env;

use simple_https_server::tls13server;

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let host = if args.len() <= 1 {
        "localhost"
    } else {
        &args[1]
    };
    let port = if args.len() <= 2 { "443" } else { &args[2] };
    match tls13server(host, port) {
        Err(x) => {
            println!("Connection to {} failed with {}\n", host, x);
        }
        Ok(()) => {
            println!("Connection to {} succeeded\n", host);
        }
    }
}
