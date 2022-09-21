use std::io::{Read, Write};

use bertie::{INSUFFICIENT_DATA, PAYLOAD_TOO_LONG};
use hacspec_lib::ByteSeq;
use tracing::{debug, trace};

use crate::{
    debug::{info_record, Hex},
    AppError,
};

#[derive(Debug)]
pub struct RecordStream<Stream>
where
    Stream: Read + Write,
{
    stream: Stream,
    buffer: Vec<u8>,
}

impl<Stream> RecordStream<Stream>
where
    Stream: Read + Write,
{
    pub fn new(stream: Stream) -> Self {
        Self {
            stream,
            buffer: Vec::new(),
        }
    }
}

impl<Stream> RecordStream<Stream>
where
    Stream: Read + Write,
{
    #[tracing::instrument(skip(self))]
    pub fn read_record(&mut self) -> Result<ByteSeq, AppError> {
        // Buffer to read chunks into.
        let mut tmp = [0u8; 4096];

        // ```TLS
        // struct {
        //     ContentType type;
        //     ProtocolVersion legacy_record_version;
        //     uint16 length;
        //     opaque fragment[TLSPlaintext.length];
        // } TLSPlaintext;
        // ```
        loop {
            debug!("Search for TLS record in stream buffer.");
            if self.buffer.len() >= 5 {
                let length = self.buffer[3] as usize * 256 + self.buffer[4] as usize;

                // TODO: Who does this?
                // The length (in bytes) of the following TLSPlaintext.fragment. The length MUST NOT
                // exceed 2^14 bytes. An endpoint that receives a record that exceeds this length
                // MUST terminate the connection with a "record_overflow" alert.
                if length > 16384 {
                    // TODO: Correct error?
                    return Err(PAYLOAD_TOO_LONG.into());
                }

                if self.buffer.len() >= 5 + length {
                    let record = {
                        let record = &self.buffer[..5 + length];
                        info_record(record);
                        ByteSeq::from_public_slice(record)
                    };

                    self.buffer = self.buffer.split_off(5 + length);

                    if !self.buffer.is_empty() {
                        debug!("There is still data in the stream buffer.");
                        trace!(
                            left = %Hex(&self.buffer),
                            "There is still data in the stream buffer (content)."
                        );
                    }

                    return Ok(record);
                }
            }

            debug!("No complete TLS record found in stream buffer.");
            match self.stream.read(&mut tmp)? {
                0 => {
                    debug!("Connection closed.");
                    // TODO: Correct error?
                    return Err(INSUFFICIENT_DATA.into());
                }
                amt => {
                    let data = &tmp[..amt];

                    debug!(amt, "Read data into stream buffer.");
                    trace!(data=%Hex(data), "Read data into stream buffer (content).");

                    self.buffer.extend_from_slice(data);
                }
            }
        }
    }

    #[tracing::instrument(skip(self, record))]
    pub fn write_record(&mut self, record: ByteSeq) -> Result<(), AppError> {
        // Safety: Safe to unwrap().
        let data = hex::decode(record.to_hex()).unwrap();
        self.stream.write_all(&data)?;

        debug!(amt = data.len(), "Wrote data.");
        trace!(data=%Hex(&data), "Wrote data (content).");
        info_record(&data);

        Ok(())
    }
}
