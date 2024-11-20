//! # Bertie command line client
//!
//! A simple TLS 1.3 command line client based on Bertie.

use bertie::{
    stream::BertieStream,
    tls13crypto::{Algorithms, SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519},
    tls13utils::*,
};
use rand::thread_rng;
use record::AppError;
use tracing::{error, event, Level};

use clap::Parser;

#[derive(Parser)]
struct Cli {
    /// The host to attempt a connection with, defaults to "www.google.com"
    host: Option<String>,
    /// Port to attempt to connect on, defaults to port 443
    #[arg(short, long)]
    port: Option<u16>,
    /// Algorithms to attempt to propose to server.

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
    ///   * SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519Kyber768Draft00
    ///   * SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519MlKEM76
    ///
    /// The default value is SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519.
    #[clap(verbatim_doc_comment)]
    #[arg(short, long)]
    ciphersuite: Option<String>,
}

/// This is a demo of a simple HTTPS client.
///
/// The client connects to host:port via TCP, executes a TLS 1.3 handshake,
/// sends an encrypted HTTP GET, and prints the servers HTTP response.
fn main() -> anyhow::Result<()> {
    // Setup tracing.
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    let host = cli.host.unwrap_or("www.google.com".to_string());
    let port = cli.port.unwrap_or(443);

    let ciphersuite = cli
        .ciphersuite
        .and_then(|s| Algorithms::try_from(s.as_str()).ok())
        .unwrap_or(SHA256_Chacha20Poly1305_EcdsaSecp256r1Sha256_X25519);

    event!(Level::INFO, "Starting new Client connection ...");
    event!(Level::DEBUG, "  {host}:{port}");
    event!(Level::DEBUG, "  {ciphersuite:#?}");

    // Initiate HTTPS connection to host:port.
    let mut stream = BertieStream::client(&host, port, ciphersuite, &mut thread_rng())
        .expect("Error connecting to server");

    // Send HTTP GET
    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);
    stream
        .write(request.as_bytes())
        .expect("Error writing to Bertie stream");
    let response = stream.read().unwrap().unwrap();
    let response_string = String::from_utf8_lossy(&response);

    if response_string.is_empty() {
        error!("Unable to connect with the configured ciphersuites.");
        return Err(AppError::TLS(UNSUPPORTED_ALGORITHM).into());
    }

    event!(Level::DEBUG, "Received HTTP response");
    event!(Level::DEBUG, "{}", response_string);
    event!(
        Level::INFO,
        "Connection to \"{}:{}\" succeeded.",
        host,
        port
    );

    Ok(())
}
