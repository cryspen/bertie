#![no_main]

use std::io::{Cursor, Read, Write};

use libfuzzer_sys::fuzz_target;
use simple_https_client::tls13client;

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
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        // Fake successful write.
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fuzz_target!(|data: &[u8]| {
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
