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
pub mod tls13api;
pub use tls13api::*;
pub use tls13formats::*;

use hacspec_lib::*;

bytes!(Random, 32);

bytes!(Bytes1, 1);
bytes!(Bytes2, 2);
bytes!(Bytes3, 3);
bytes!(Bytes4, 4);
bytes!(Bytes5, 5);
bytes!(Bytes6, 6);
bytes!(Bytes7, 7);
bytes!(Bytes8, 8);
bytes!(Bytes9, 9);
bytes!(Bytes10, 10);
bytes!(Bytes11, 11);
bytes!(Bytes12, 12);
bytes!(Bytes32, 32);
bytes!(Bytes98, 98);

// FIXME: NOT HACSPEC | ONLY FOR DEBUGGING
pub(crate) fn parse_failed() -> TLSError {
    let bt = backtrace::Backtrace::new();
    println!("{:?}", bt);
    PARSE_FAILED
}
