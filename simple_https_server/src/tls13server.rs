//! A Simple TLS 1.3 HTTP Server Implementation
//! It waits for a connection at port 443, receives an HTTP "GET /", and prints a constant string
//! WARNING: This code is not in hacspec since it need to use TCP etc.

use std::{net::TcpListener, time::Duration};

use bertie::{
    stream::BertieStream, tls13crypto::Algorithms,
    tls13crypto::SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519,
};

use clap::Parser;

#[derive(Parser)]
struct Cli {
    /// The hostname, defaults to "localhost"
    host: Option<String>,
    /// Port to listen on, defaults to port 443
    #[arg(short, long)]
    port: Option<u16>,

    /// Algorithms to attempt to accept from a client.
    /// Can be one of the following strings:
    ///   * SHA256_Chacha20Poly1305_RsaPssRsaSha256_X25519
    ///   * SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519
    ///   * SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_P256
    ///   * SHA256_Chacha20Poly1305_RsaPssRsaSha256_P256
    ///   * SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_P256
    ///   * SHA256_Aes128Gcm_EcdsaSecp256r1Sha256_X25519
    ///   * SHA256_Aes128Gcm_RsaPssRsaSha256_P256
    ///   * SHA256_Aes128Gcm_RsaPssRsaSha256_X25519
    ///   * SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_P256
    ///   * SHA384_Aes256Gcm_EcdsaSecp256r1Sha256_X25519
    ///   * SHA384_Aes256Gcm_RsaPssRsaSha256_P256
    ///   * SHA384_Aes256Gcm_RsaPssRsaSha256_X25519
    ///
    /// The default value is SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519.
    #[clap(verbatim_doc_comment)]
    #[arg(short, long)]
    algorithms: Option<String>,
}

pub fn main() -> anyhow::Result<()> {
    // Setup tracing.
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    let host = cli.host.unwrap_or("localhost".to_string());
    let port = cli.port.unwrap_or(443);

    let ciphersuite = cli
        .algorithms
        .map(|s| Algorithms::try_from(s.as_str()).unwrap())
        .unwrap_or(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519);

    let listener = TcpListener::bind((host.as_str(), port)).unwrap();

    for stream in listener.incoming() {
        let stream = stream.unwrap();

        let d = Duration::new(15, 0);
        stream
            .set_read_timeout(Some(d))
            .expect("set_read_timeout call failed");
        println!("New connection established!");
        match BertieStream::server(
            &host,
            port,
            stream,
            ciphersuite,
            "./tests/assets/p256_cert.der",
            "./tests/assets/p256_key.der",
        ) {
            Ok(_server) => {
                println!("Connection to {} succeeded\n", host);
            }
            Err(error) => {
                println!("Connection to {} failed with {:?}\n", host, error);
            }
        }
    }

    Ok(())
}
