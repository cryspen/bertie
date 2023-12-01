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

pub mod server;
pub mod tls13api;
pub mod tls13cert;
pub mod tls13crypto;
pub mod tls13utils;

pub use tls13api::{Client, Server};
// Debug exports only
pub use tls13formats::{get_alert_description, get_alert_level, get_hs_type, ContentType};

// === Public API that is NOT in hacspec

#[cfg(feature = "api")]
pub mod stream;

#[cfg(feature = "test_utils")]
pub mod test_utils;
