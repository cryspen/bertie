//! This crate provides common functionality used in both the `simple_https_client`
//! and `simple_https_server` such as the `RecordStream`, common error types,
//! debug functions, and helpers.

use bertie::TLSError;
pub use debug::{info_record, Hex};
pub use stream::RecordStream;
use thiserror::Error;

mod debug;
mod stream;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("I/O error: {0:?}")]
    Io(std::io::Error),
    #[error("TLS error: {0:?}")]
    TLS(TLSError),
}

impl From<std::io::Error> for AppError {
    fn from(error: std::io::Error) -> Self {
        AppError::Io(error)
    }
}

impl From<TLSError> for AppError {
    fn from(error: TLSError) -> Self {
        AppError::TLS(error)
    }
}
