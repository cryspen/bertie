#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(unused_variables)]
// hacspec doesn't allow +=
#![allow(clippy::assign_op_pattern)]
// FIXME(performance)
#![allow(clippy::large_enum_variant)]
#![allow(clippy::zero_prefixed_literal)]

mod test_tls13traces_internal;
mod tls13formats;
mod tls13handshake;
mod tls13record;

pub mod tls13utils;
pub use tls13utils::*;
pub mod tls13crypto;
pub use tls13crypto::*;
pub mod tls13cert;
pub use tls13cert::*;
pub mod tls13api;
pub use tls13api::*;
pub use tls13formats::*;

// FIXME: NOT HACSPEC | ONLY FOR DEBUGGING
pub(crate) fn parse_failed() -> TLSError {
    let bt = backtrace::Backtrace::new();
    println!("{:?}", bt);
    PARSE_FAILED
}