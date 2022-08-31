// # Bertie BoGo Shim
//
// # Credit
//
// The code is based on rustls' bogo shim ...
//
//     https://github.com/rustls/rustls/blob/main/rustls/examples/internal/bogo_shim.rs
//

use std::{env, net::TcpStream, process};

use simple_https_client::tls13client;
use tracing::Level;

static BOGO_NACK: i32 = 89;

#[derive(Debug)]
struct Options {
    port: u16,
    role: Role,
    key_file: String,
    cert_file: String,
    hostname: String,
    expect_fallback_scsv: bool,
    expect_extended_master_secret: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            port: 0,
            role: Role::Client,
            key_file: "".into(),
            cert_file: "".into(),
            hostname: "example.com".into(),
            expect_fallback_scsv: false,
            expect_extended_master_secret: false,
        }
    }
}

#[derive(Debug)]
enum Role {
    Client,
    Server,
}

const UNHANDLED_ARGUMENTS: &[&str] = &[
    "-advertise-alpn",
    "-async",
    "-check-close-notify",
    "-cipher",
    "-curves",
    "-ech-config-list",
    "-enable-early-data",
    "-enable-ech-grease",
    "-enable-grease",
    "-enable-ocsp-stapling",
    "-enforce-rsa-key-usage",
    "-expect-certificate-types",
    "-expect-cipher-aes",
    "-expect-client-ca-list",
    "-expect-curve-id",
    "-expect-no-session",
    "-expect-peer-cert-file",
    "-expect-peer-signature-algorithm",
    "-expect-peer-verify-pref",
    "-expect-secure-renegotiation",
    "-expect-ticket-supports-early-data",
    "-export-keying-material",
    "-export-traffic-secrets",
    "-fail-cert-callback",
    "-fail-early-callback",
    "-fips-202205",
    "-forbid-renegotiation-after-handshake",
    "-implicit-handshake",
    "-install-cert-compression-algs",
    "-key-update",
    "-ocsp-response",
    "-on-resume-expect-accept-early-data",
    "-on-resume-expect-reject-early-data",
    "-peek-then-read",
    "-psk",
    "-read-with-unfinished-write",
    "-renegotiate-explicit",
    "-renegotiate-freely",
    "-renegotiate-ignore",
    "-renegotiate-once",
    "-require-any-client-certificate",
    "-resume-count",
    "-send-channel-id",
    "-shim-shuts-down",
    "-shim-writes-first",
    "-signing-prefs",
    "-srtp-profiles",
    "-tls-unique",
    "-use-old-client-cert-callback",
    "-verify-fail",
    "-verify-peer",
    "-verify-prefs",
    "-write-settings",
];

fn main() {
    tracing_subscriber::fmt::fmt()
        .with_max_level(Level::DEBUG)
        .init();

    let mut args: Vec<_> = env::args().collect();
    args.remove(0);

    if let Some(arg) = args.get(0) {
        if arg == "-is-handshaker-supported" {
            println!("No");
            process::exit(0);
        }
    }

    println!("Options: {:#?}", args);

    let mut options = Options::default();

    while !args.is_empty() {
        let arg = args.remove(0);
        match arg.as_ref() {
            "-server" => {
                options.role = Role::Server;
                skip_currently(&arg);
            }
            "-key-file" => {
                options.key_file = args.remove(0);
            }
            "-cert-file" => {
                options.cert_file = args.remove(0);
            }
            "-min-version" => {
                skip_currently(&arg);
            }
            "-max-version" => {
                skip_currently(&arg);
            }
            "-host-name" => {
                options.hostname = args.remove(0);
            }
            "-port" => {
                options.port = args.remove(0).parse::<u16>().unwrap();
            }
            "-fallback-scsv" => {
                options.expect_fallback_scsv = true;
                skip_currently(&arg);
            }
            "-expect-extended-master-secret" => {
                options.expect_extended_master_secret = true;
                skip_currently(&arg);
            }
            // -------------------------------------------------------------------------------------
            "-dtls" | "-quic" | "-no-tls13" => {
                skip(&arg);
            }
            "-no-tls1" | "-no-tls11" | "-no-tls12" => {
                ignore(&arg);
            }
            // -------------------------------------------------------------------------------------
            "-max-send-fragment" => {
                skip(&arg);
            }
            arg => {
                if UNHANDLED_ARGUMENTS.contains(&arg) {
                    skip_currently(arg);
                }

                println!("Unhandled argument | \"{}\",", arg);
                process::exit(1);
            }
        }
    }

    println!("{:#?}", options);

    match options.role {
        Role::Client => {
            let addrs = [
                std::net::SocketAddr::from((std::net::Ipv6Addr::LOCALHOST, options.port)),
                std::net::SocketAddr::from((std::net::Ipv4Addr::LOCALHOST, options.port)),
            ];
            let stream = TcpStream::connect(&addrs[..]).expect("Can't connect to BoGo.");

            let _ = tls13client(&options.hostname, stream, "hello");
        }
        Role::Server => {
            unimplemented!()
        }
    }
}

fn skip(due_to: &str) {
    println!("Skipping test due to \"{}\" argument.", due_to);
    process::exit(BOGO_NACK);
}

// TODO: Remove eventually.
fn skip_currently(due_to: &str) {
    println!(
        "Skipping test due to \"{}\" argument. Will be changed in the future.",
        due_to
    );
    process::exit(BOGO_NACK);
}

fn ignore(what: &str) {
    println!("Ignoring \"{}\" argument.", what);
}
