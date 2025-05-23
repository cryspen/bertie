//! Bertie is a minimal, high-assurance implementation of TLS 1.3
//!
//! It is built upon the following design principles:
//!
//! 1) **Purely functional**: no mutable data structures or externally visible side-effects.
//! 2) **Verification friendly**: written in a way that can be translated to verifiable models
//! 3) **Succinct and minimal**: configured with a single protocol version and cipher suite.
//!
//! In particular, the protocol code in Bertie is passed through the [hax] verification toolchain
//! to generate F* code that can be formally verified for correctness and security.
//!
//! Bertie is a library, which you can add as a dependency in your project.
//! The API for this library is in [tls13api]. To create a Bertie client,
//! you will need to use the methods for the [tls13api::Client] type.
//! Similarly, you will use the methods for [tls13api::Server] to run a Bertie server.
//!
//! For simple examples of how to use these APIs, look at the source code of [tls13client] and
//! [tls13server].
//!
//! [hax]: https://github.com/hacspec/hax
//! [tls13client]: ../tls13client/index.html
//! [tls13server]: ../tls13server/index.html

#![allow(non_upper_case_globals)]
#![allow(unused_variables)]
// FIXME(performance)
#![allow(clippy::large_enum_variant)]
#![allow(clippy::zero_prefixed_literal)]
#![no_std]

#[cfg(feature = "std")]
extern crate std;

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc as std;

mod tls13formats;
mod tls13handshake;
mod tls13record;

pub mod server;
pub mod tls13api;
pub mod tls13cert;
pub mod tls13crypto;
pub mod tls13utils;

pub use tls13api::{Client, Server};
// Debug exports only
pub use tls13formats::{handshake_data::get_hs_type, AlertDescription, AlertLevel, ContentType};

#[cfg(bench)]
pub use tls13formats::{
    bench_client_hello, bench_parse_client_hello, bench_parse_server_certificate,
    bench_parse_server_hello, HandshakeData,
};

#[cfg(all(test, feature = "std"))]
mod test_tls13traces_internal;

// === Public API that is NOT in hacspec

#[cfg(all(feature = "api", feature = "std"))]
pub mod stream;

#[cfg(feature = "test_utils")]
pub mod test_utils;
