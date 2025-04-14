//! # Streaming API
//!
//! A streaming API for t13.
//! This is a more usable API that is however NOT VERIFIED.

use self::{client::ClientState, server::ServerState};

mod t13_stream;
mod client;
mod server;

pub use t13_stream::{t13Error, t13Stream, TlsStream};
pub use server::init_db;

/// A t13 Client stream.
pub type t13Client<Stream> = t13Stream<ClientState<Stream>>;
/// A t13 Server stream.
pub type t13Server<Stream> = t13Stream<ServerState<Stream>>;
