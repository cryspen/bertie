//! A Simple TLS 1.3 HTTP Server Implementation
//! It waits for a connection at port 443, receives an HTTP "GET /", and prints a constant string
//! WARNING: This code is not in hacspec since it need to use TCP etc.

use std::{env, net::TcpListener, time::Duration};

use simple_https_server::tls13server;

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let host = if args.len() <= 1 {
        "localhost"
    } else {
        &args[1]
    };
    let port = if args.len() <= 2 { "443" } else { &args[2] };

    let addr = ["127.0.0.1", port].join(":");

    let listener = TcpListener::bind(addr).unwrap();

    for stream in listener.incoming() {
        let mut stream = stream.unwrap();

        let d = Duration::new(15, 0);
        stream
            .set_read_timeout(Some(d))
            .expect("set_read_timeout call failed");
        println!("New connection established!");
        match tls13server(&mut stream, host) {
            Ok(()) => {
                println!("Connection to {} succeeded\n", host);
            }
            Err(error) => {
                println!("Connection to {} failed with {:?}\n", host, error);
            }
        }
    }
}
