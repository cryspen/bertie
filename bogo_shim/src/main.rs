// # Bertie BoGo Shim
//
// # Credit
//
// The code is based on rustls' bogo shim ...
//
//     https://github.com/rustls/rustls/blob/main/rustls/examples/internal/bogo_shim.rs
//

use std::{env, io::Write, net::TcpStream, process};

use simple_https_client::tls13client;
use simple_https_server::{tls13server, AppError};
use tracing::Level;

static BOGO_NACK: i32 = 89;

#[derive(Debug, Default)]
struct Options {
    port: u16,
    shim_id: u16,
    ipv6: bool,
    role: Role,
    key_file: String,
    cert_file: String,
    hostname: String,
    expect_fallback_scsv: bool,
    expect_extended_master_secret: bool,
}

#[derive(Debug, Default)]
enum Role {
    #[default]
    Client,
    Server,
}

/// When a BoGo test contains one of these parameters, it will be skipped.
/// BoGo will be notified about the skip via the return code BOGO_NACK.
/// (See https://github.com/google/boringssl/blob/master/ssl/test/PORTING.md#unimplemented-features.)
///
/// Note: This list is expected to decrease over time when the Bertie API stabilizes.
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

/// The BoGo shim receives command-line parameters from the BoGo test runner.
/// These arguments are used to configure Bertie for the upcoming test.
///
/// The last step in this shim is always to connect/accept a connection from BoGo --
/// depending if working as a client or server -- and to compare if BoGo and Bertie agree
/// on the outcome of the connection.
///
/// Note: In order to make this work, we will need to adjust the configuration file in assets/config.json.
///
///       Also, many arguments are currently not supported. Thus, we use `skip_currently`
///       to signal to the BoGo test runner that a specific test should be skipped.
fn main() {
    tracing_subscriber::fmt::fmt()
        .with_max_level(Level::INFO)
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
            "-shim-id" => {
                options.shim_id = args.remove(0).parse::<u16>().unwrap();
            }
            "-ipv6" => {
                options.ipv6 = true;
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
                // When an argument is not handled, it must be explicitly ignored.
                if UNHANDLED_ARGUMENTS.contains(&arg) {
                    skip_currently(arg);
                }

                // Otherwise we exit with an error.
                println!("Unhandled argument | \"{}\",", arg);
                process::exit(1);
            }
        }
    }

    println!("{:#?}", options);

    let addrs = [
        std::net::SocketAddr::from((std::net::Ipv6Addr::LOCALHOST, options.port)),
        std::net::SocketAddr::from((std::net::Ipv4Addr::LOCALHOST, options.port)),
    ];
    let mut stream = TcpStream::connect(&addrs[..]).expect("Can't connect to BoGo.");

    stream
        .write_all(&(options.shim_id as u64).to_le_bytes())
        .unwrap();

    match options.role {
        Role::Client => {
            let _ = tls13client(&options.hostname, stream, None, "hello");
        }
        Role::Server => {
            if let Err(e) = tls13server(stream, &options.hostname) {
                match e {
                    AppError::TLS(137) => eprintln!("Wrong TLS protocol version {:?}", e),
                    _ => eprintln!("Bertie server error {:?}", e),
                }
            }
        }
    }
}

// Use this function when an argument will not be supported by Bertie.
fn skip(due_to: &str) {
    println!("Skipping test due to \"{}\" argument.", due_to);
    process::exit(BOGO_NACK);
}

// Use this function when an argument is *currently* not be supported by Bertie.
// Note: This function will eventually be removed.
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
