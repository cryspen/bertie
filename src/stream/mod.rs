//! # Streaming API
//!
//! A streaming API for Bertie.
//! This is a more usable API that is however NOT VERIFIED.

use self::{client::ClientState, server::ServerState};

mod client;
mod server;
mod stream;

pub use stream::{BertieError, BertieStream, TlsStream};

/// A Bertie Client stream.
pub type BertieClient<Stream> = BertieStream<ClientState<Stream>>;
/// A Bertie Server stream.
pub type BertieServer<Stream> = BertieStream<ServerState<Stream>>;
