use std::net::TcpStream;

use bertie::tls13utils::*;
use record::AppError;
use simple_https_client::{ciphersuite_from_str, tls13client};
use tracing::{error, trace};

mod flags {
    xflags::xflags! {
        cmd connect {
            /// The host to attempt a connection with, defaults to "www.google.com"
            optional --host host: String
            /// Port to attempt to connect on, defaults to port 443
            optional --port port: u16
            /// Algorithms to attempt to propose to server.

            /// Can be one of the following strings:
            ///
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
            optional --algorithms algorithms: String
        }
    }
}

/// This is a demo of a simple HTTPS client.
///
/// The client connects to host:port via TCP, executes a TLS 1.3 handshake,
/// sends an encrypted HTTP GET, and prints the servers HTTP response.
#[allow(clippy::never_loop)]
fn main() -> anyhow::Result<()> {
    // Setup tracing.
    tracing_subscriber::fmt::init();

    let flags = flags::Connect::from_env_or_exit();

    let (host, port, algorithms) = {
        let host = flags.host.unwrap_or("www.google.com".to_string());
        let port = flags.port.unwrap_or(443);
        let algorithms = flags.algorithms.map(|s| ciphersuite_from_str(&s).unwrap());
        (host, port, algorithms)
    };

    let request = format!("GET / HTTP/1.1\r\nHost: {}\r\n\r\n", host);

    // Initiate HTTPS connection to host:port.
    let stream = TcpStream::connect((host.clone(), port))?;
    stream.set_nodelay(true).expect("set_nodelay call failed");
    trace!(
        host = format!("{}:{}", host, port),
        algorithms = format!("{:?}", algorithms),
        "Opened TCP connection to host."
    );

    let response_prefix = tls13client(&host, stream, algorithms, &request).map(|r| r.2)?;

    if response_prefix.is_empty() {
        error!("Unable to connect with the configured ciphersuites.");
        return Err(AppError::TLS(UNSUPPORTED_ALGORITHM).into());
    }

    println!("[!] Received HTTP response (prefix):");
    println!("{}", String::from_utf8_lossy(&response_prefix));
    println!("[!] Connection to \"{}:{}\" succeeded.", host, port);

    Ok(())
}
