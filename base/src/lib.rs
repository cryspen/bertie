use bertie::TLSError;
pub use debug::{info_record, Hex};
pub use stream::RecordStream;
use thiserror::Error;

mod debug;
mod stream;

#[derive(Error, Debug)]
pub enum ClientError {
    #[error("I/O error: {0:?}")]
    Io(std::io::Error),
    #[error("TLS error: {0:?}")]
    TLS(TLSError),
}

impl From<std::io::Error> for ClientError {
    fn from(error: std::io::Error) -> Self {
        ClientError::Io(error)
    }
}

impl From<TLSError> for ClientError {
    fn from(error: TLSError) -> Self {
        ClientError::TLS(error)
    }
}
