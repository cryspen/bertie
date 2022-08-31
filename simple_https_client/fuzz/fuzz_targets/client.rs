#![no_main]

use std::io::{Cursor, Read, Write};

use libfuzzer_sys::fuzz_target;
use simple_https_client::tls13client;

/// This struct is used to disguise a `&[u8]` as a stream, i.e.,
/// something that implements `Read` and `Write`.
struct Stream<'a> {
    cursor: Cursor<&'a [u8]>,
}

impl<'a> Stream<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self {
            cursor: Cursor::new(data),
        }
    }
}

impl<'a> Read for Stream<'a> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.cursor.read(buf)
    }
}

impl<'a> Write for Stream<'a> {
    /// Fake a successful write.
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fuzz_target!(|data: &[u8]| {
    // We use `Stream` to feed the libFuzzer input (`&[u8]`) into `tls13client()`.
    let stream = Stream::new(data);

    match tls13client("127.0.0.1", stream, "") {
        Ok(_) => {
            panic!("No way! O.o");
        }
        Err(_) => {
            // println!("{:?}", error);
        }
    };
});
