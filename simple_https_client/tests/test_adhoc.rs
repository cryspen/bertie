//! This test file is used to allow for easy reproduction of crashes that happened
//! during fuzzing.
//!
//! libFuzzer provides a crash-file which content can be pasted here to reproduce the crash
//! with the help of a debugger (and a typical debugging workflow.)

use std::io::{Cursor, Read, Write};

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

#[test]
#[ignore = "Enable this later."]
fn test_adhoc() {
    let tests: &[&[u8]] = &[
        // SERVER_HELLO with length=0
        b"160303000402000000",
        // ...
        b"16030300080200000403034E85",
    ];

    for test in tests {
        let data = hex::decode(test).unwrap();
        let stream = Stream::new(&data);

        let _ = tls13client("127.0.0.1", stream, "");
    }
}
