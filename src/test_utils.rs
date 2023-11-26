use rand::{CryptoRng, RngCore};

pub struct TestRng {
    bytes: Vec<u8>,
}

impl TestRng {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    pub fn raw(&self) -> &[u8] {
        &self.bytes
    }
}

impl RngCore for TestRng {
    fn next_u32(&mut self) -> u32 {
        todo!()
    }

    fn next_u64(&mut self) -> u64 {
        todo!()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.copy_from_slice(self.bytes.drain(0..dest.len()).as_ref());
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        dest.copy_from_slice(self.bytes.drain(0..dest.len()).as_ref());
        Ok(())
    }
}

impl CryptoRng for TestRng {}
