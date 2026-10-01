use crate::std::vec::Vec;
use core::convert::Infallible;
use rand::{TryCryptoRng, TryRng};

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

impl TryRng for TestRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        todo!()
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        todo!()
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Infallible> {
        dest.copy_from_slice(self.bytes.drain(0..dest.len()).as_ref());
        Ok(())
    }
}

impl TryCryptoRng for TestRng {}
