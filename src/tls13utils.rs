use core::ops::Range;

// FIXME: NOT HACSPEC | ONLY FOR DEBUGGING
pub(crate) fn parse_failed() -> TLSError {
    // let bt = backtrace::Backtrace::new();
    // println!("{:?}", bt);
    PARSE_FAILED
}

// Bertie errors
#[derive(Debug, Clone)]
pub enum Error {
    /// Unknown ciphersuite
    UnknownCiphersuite(String),
}

// Local error codes
pub type TLSError = u8;
pub const UNSUPPORTED_ALGORITHM: TLSError = 1u8;
pub const CRYPTO_ERROR: TLSError = 2u8;
pub const INSUFFICIENT_ENTROPY: TLSError = 3u8;
pub const INCORRECT_ARRAY_LENGTH: TLSError = 4u8;

pub const INCORRECT_STATE: TLSError = 128u8;
pub const ZERO_RTT_DISABLED: TLSError = 129u8;
pub const PAYLOAD_TOO_LONG: TLSError = 130u8;
pub const PSK_MODE_MISMATCH: TLSError = 131u8;
pub const NEGOTIATION_MISMATCH: TLSError = 132u8;
pub const PARSE_FAILED: TLSError = 133u8;
pub const INSUFFICIENT_DATA: TLSError = 134u8;
pub const UNSUPPORTED: TLSError = 135u8;
pub const INVALID_COMPRESSION_LIST: TLSError = 136u8;
pub const PROTOCOL_VERSION_ALERT: TLSError = 137u8;
pub const APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: TLSError = 138u8;
pub const MISSING_KEY_SHARE: TLSError = 139u8;
pub const INVALID_SIGNATURE: TLSError = 140u8;
pub const GOT_HANDSHAKE_FAILURE_ALERT: TLSError = 141u8;
pub const DECODE_ERROR: TLSError = 142u8;

pub(crate) fn error_string(c: u8) -> String {
    format!("{}", c)
}

pub(crate) fn tlserr<T>(err: TLSError) -> Result<T, TLSError> {
    let bt = backtrace::Backtrace::new();
    println!("{:?}", bt);
    Err(err)
}

/*
pub(crate) fn check_eq_size(s1: TLSError, s2: usize) -> Result<()> {
    if s1 == s2 {Ok(())}
    else {Err(parse_failed())}
}*/

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U8(u8);
#[cfg(feature = "secret_integers")]
impl core::ops::BitXor for U8 {
    type Output = U8;
    fn bitxor(self, rhs: Self) -> Self::Output {
        U8(self.0 ^ rhs.0)
    }
}
#[cfg(feature = "secret_integers")]
impl From<u8> for U8 {
    fn from(x: u8) -> U8 {
        U8(x)
    }
}
#[cfg(feature = "secret_integers")]
impl U8 {
    pub(crate) fn declassify(&self) -> u8 {
        self.0
    }
}

#[cfg(not(feature = "secret_integers"))]
type U8 = u8;
#[cfg(not(feature = "secret_integers"))]
pub(crate) fn U8(x: u8) -> U8 {
    x
}
#[cfg(not(feature = "secret_integers"))]
impl Declassify for U8 {
    type t = u8;
    fn declassify(&self) -> u8 {
        *self
    }
}

impl From<&u8> for U8 {
    fn from(x: &u8) -> U8 {
        U8(*x)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U16(u16);

impl From<u16> for U16 {
    fn from(x: u16) -> U16 {
        U16(x)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U32(u32);

impl From<u32> for U32 {
    fn from(x: u32) -> U32 {
        U32(x)
    }
}

impl core::ops::Add for U32 {
    type Output = U32;
    fn add(self, y: U32) -> U32 {
        U32(self.0 + y.0)
    }
}

#[derive(Clone, PartialEq, Debug, Default)]
pub struct Bytes(Vec<U8>);

impl From<Vec<u8>> for Bytes {
    fn from(x: Vec<u8>) -> Bytes {
        Bytes(x.iter().map(|x| x.into()).collect())
    }
}

impl Bytes {
    pub fn declassify(&self) -> Vec<u8> {
        self.0.iter().map(|x| x.declassify()).collect()
    }

    /// Convert the bytes into raw bytes
    pub(crate) fn into_raw(self) -> Vec<U8> {
        self.0
    }

    /// Get a reference to the raw bytes.
    pub(crate) fn as_raw(&self) -> &[U8] {
        &self.0
    }
}

impl Bytes {
    pub(crate) fn declassify_array<const C: usize>(&self) -> Result<[u8; C], TLSError> {
        self.declassify()
            .try_into()
            .map_err(|_| INCORRECT_ARRAY_LENGTH)
    }
}

impl From<&[u8]> for Bytes {
    fn from(x: &[u8]) -> Bytes {
        x.to_vec().into()
    }
}

impl From<&[U8]> for Bytes {
    fn from(x: &[U8]) -> Bytes {
        Bytes(x.to_vec())
    }
}

impl<const C: usize> From<[u8; C]> for Bytes {
    fn from(x: [u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

impl<const C: usize> From<&[u8; C]> for Bytes {
    fn from(x: &[u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

impl U32 {
    pub(crate) fn from_be_bytes(x: &Bytes) -> Result<U32, TLSError> {
        Ok(U32(u32::from_be_bytes(x.declassify_array()?)))
    }
    pub(crate) fn as_be_bytes(&self) -> Bytes {
        (self.0.to_be_bytes().to_vec()).into()
    }
    pub(crate) fn declassify(&self) -> u32 {
        self.0
    }
}

impl U16 {
    pub(crate) fn from_be_bytes(x: &Bytes) -> Result<U16, TLSError> {
        Ok(U16(u16::from_be_bytes(x.declassify_array()?)))
    }
    pub(crate) fn as_be_bytes(&self) -> Bytes {
        (self.0.to_be_bytes().to_vec()).into()
    }
    pub(crate) fn declassify(&self) -> u16 {
        self.0
    }
}

pub(crate) fn bytes(x: &[u8]) -> Bytes {
    x.into()
}
pub(crate) fn bytes1(x: u8) -> Bytes {
    [x].into()
}
pub(crate) fn bytes2(x: u8, y: u8) -> Bytes {
    [x, y].into()
}

impl core::ops::Index<usize> for Bytes {
    type Output = U8;
    fn index(&self, x: usize) -> &U8 {
        &self.0[x]
    }
}

mod non_hax {
    use super::{Bytes, U8};

    impl core::ops::IndexMut<usize> for Bytes {
        fn index_mut(&mut self, i: usize) -> &mut U8 {
            &mut self.0[i]
        }
    }

    impl core::ops::IndexMut<core::ops::Range<usize>> for Bytes {
        fn index_mut(&mut self, x: core::ops::Range<usize>) -> &mut [U8] {
            &mut self.0[x]
        }
    }
}

impl core::ops::Index<Range<usize>> for Bytes {
    type Output = [U8];
    fn index(&self, x: Range<usize>) -> &[U8] {
        &self.0[x]
    }
}

impl Bytes {
    pub(crate) fn new() -> Bytes {
        Bytes(Vec::new())
    }
    pub(crate) fn zeroes(len: usize) -> Bytes {
        Bytes(vec![U8(0); len])
    }
    pub(crate) fn with_capacity(len: usize) -> Bytes {
        Bytes(Vec::with_capacity(len))
    }
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub(crate) fn push(&mut self, x: U8) {
        self.0.push(x)
    }
    pub(crate) fn extend_from_slice(&mut self, x: &Bytes) {
        self.0.extend_from_slice(&x.0)
    }

    pub(crate) fn from_slice(s: &[u8]) -> Bytes {
        s.into()
    }

    /// Read a hex string into [`Bytes`].
    pub fn from_hex(s: &str) -> Bytes {
        let s: String = s.split_whitespace().collect();
        if s.len() % 2 == 0 {
            Bytes(
                (0..s.len())
                    .step_by(2)
                    .map(|i| {
                        s.get(i..i + 2)
                            .and_then(|sub| (u8::from_str_radix(sub, 16).ok()).map(U8))
                    })
                    .collect::<Option<Vec<U8>>>()
                    .expect("Not a hex string1"),
            )
        } else {
            unreachable!("Not a hex string2")
        }
    }

    /// Get a hex representation of self as [`String`].
    pub(crate) fn as_hex(&self) -> String {
        let strs: Vec<String> = self
            .0
            .iter()
            .map(|b| format!("{:02x}", b.declassify()))
            .collect();
        strs.join("")
    }

    /// Get a new copy of the given `range` as [`Bytes`].
    pub(crate) fn slice_range(&self, range: Range<usize>) -> Bytes {
        self.0[range].into()
    }

    /// Get a new copy of the given range `[start..start+len]` as [`Bytes`].
    pub(crate) fn slice(&self, start: usize, len: usize) -> Bytes {
        self.0[start..start + len].into()
    }

    /// Concatenate `other` with these bytes and return a copy as [`Bytes`].
    pub fn concat(&self, other: &Bytes) -> Bytes {
        let mut res = Vec::new();
        res.extend_from_slice(&self.0);
        res.extend_from_slice(&other.0);
        Bytes(res)
    }

    /// Update the slice `self[start..start+len] = other[beg..beg+len]` and return
    /// a copy as [`Bytes`].
    pub(crate) fn update_slice(
        &self,
        start: usize,
        other: &Bytes,
        beg: usize,
        len: usize,
    ) -> Bytes {
        let mut res = self.clone();
        for i in 0..len {
            res[start + i] = other[beg + i];
        }
        res
    }
}

/// Convert the bool `b` into a Result.
pub(crate) fn check(b: bool) -> Result<(), TLSError> {
    if b {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

/// Test if [Bytes] `b1` and `b2` have the same value.
pub(crate) fn eq1(b1: U8, b2: U8) -> bool {
    b1.declassify() == b2.declassify()
}

/// Parser function to check if [Bytes] `b1` and `b2` have the same value,
/// returning a [TLSError] otherwise.
pub(crate) fn check_eq1(b1: U8, b2: U8) -> Result<(), TLSError> {
    if eq1(b1, b2) {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

// TODO: This function should short-circuit once hax supports returns within loops
/// Check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions.
pub fn eq(b1: &Bytes, b2: &Bytes) -> bool {
    if b1.len() != b2.len() {
        false
    } else {
        let mut b: bool = true;
        for i in 0..b1.len() {
            if !eq1(b1[i], b2[i]) {
                b = false;
            };
        }
        b
    }
}

/// Parse function to check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
pub(crate) fn check_eq(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    let b = eq(b1, b2);
    if b {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

// TODO: This function should short-circuit once hax supports returns within loops
/// Compare the two provided byte slices.
///
/// Returns `Ok(())` when they are equal, and a [`TLSError`] otherwise.
pub(crate) fn check_mem(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    if b2.len() % b1.len() != 0 {
        Err(parse_failed())
    } else {
        let mut b = false;
        for i in 0..(b2.len() / b1.len()) {
            if eq(b1, &b2.slice_range(i * b1.len()..(i + 1) * b1.len())) {
                b = true;
            }
        }
        if b {
            Ok(())
        } else {
            Err(parse_failed())
        }
    }
}

/// Attempt to TLS encode the `bytes` with [`u8`] length.
///
/// On success, return a new [Bytes] slice such that its first byte encodes the
/// length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in one byte.
pub(crate) fn encode_lbyte(bytes: &Bytes) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 256 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let mut lenb = Bytes::new();
        lenb.push((len as u8).into());
        lenb.extend_from_slice(bytes);
        Ok(lenb)
    }
}

/// Attempt to TLS encode the `bytes` with [`u16`] length.
///
/// On success, return a new [Bytes] slice such that its first two bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in two bytes.
pub(crate) fn encode_lbytes2(bytes: &Bytes) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len = (U16(len as u16)).as_be_bytes();
        let mut lenb = Bytes::new();
        lenb.push(len[0]);
        lenb.push(len[1]);
        lenb.extend_from_slice(bytes);
        Ok(lenb)
    }
}

/// Attempt to TLS encode the `bytes` with [`u24`] length.
///
/// On success, return a new [Bytes] slice such that its first three bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in three bytes.
pub(crate) fn encode_lbytes3(bytes: &Bytes) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 16777216 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len = U32(len as u32).as_be_bytes();
        let mut lenb = Bytes::new();
        lenb.push(len[1]);
        lenb.push(len[2]);
        lenb.push(len[3]);
        lenb.extend_from_slice(bytes);
        Ok(lenb)
    }
}

/// Check if `bytes[1..]` is at least as long as the length encoded by
/// `bytes[0]` in big-endian order.
///
/// On success, return the encoded length. Return a [TLSError] if `bytes` is
/// empty or if the encoded length exceeds the length of the remainder of
/// `bytes`.
pub(crate) fn check_lbyte(bytes: &Bytes) -> Result<usize, TLSError> {
    if bytes.is_empty() {
        Err(parse_failed())
    } else {
        let l = bytes[0].declassify() as usize;
        if bytes.len() - 1 < l {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
///
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
pub(crate) fn check_lbytes2(bytes: &Bytes) -> Result<usize, TLSError> {
    if bytes.len() < 2 {
        Err(parse_failed())
    } else {
        let l0 = bytes[0].declassify() as usize;
        let l1 = bytes[1].declassify() as usize;
        let l = l0 * 256 + l1;
        if bytes.len() - 2 < l {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

/// Check if `bytes[3..]` is at least as long as the length encoded by `bytes[0..3]`
/// in big-endian order.
///
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 3
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
pub(crate) fn check_lbytes3(bytes: &Bytes) -> Result<usize, TLSError> {
    if bytes.len() < 3 {
        Err(parse_failed())
    } else {
        let l0 = bytes[0].declassify() as usize;
        let l1 = bytes[1].declassify() as usize;
        let l2 = bytes[2].declassify() as usize;
        let l = l0 * 65536 + l1 * 256 + l2;
        if bytes.len() - 3 < l {
            Err(parse_failed())
        } else {
            Ok(l)
        }
    }
}

/// Check if `bytes` contains exactly the TLS `u8` length encoded content.
///
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
pub(crate) fn check_lbyte_full(bytes: &Bytes) -> Result<(), TLSError> {
    if check_lbyte(bytes)? + 1 != bytes.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first two bytes.
///
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
pub(crate) fn check_lbytes2_full(bytes: &Bytes) -> Result<(), TLSError> {
    if check_lbytes2(bytes)? + 2 != bytes.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first three bytes.
///
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
pub(crate) fn check_lbytes3_full(bytes: &Bytes) -> Result<(), TLSError> {
    if check_lbytes3(bytes)? + 3 != bytes.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

// Handshake Data
pub struct HandshakeData(pub Bytes);

impl HandshakeData {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn bytes(&self) -> Bytes {
    pub(crate) fn to_bytes(&self) -> Bytes {
        self.0.clone()
    }

    pub(crate) fn concat(self, other: &HandshakeData) -> HandshakeData {
        let mut message1 = self.to_bytes();
        let message2 = other.to_bytes();

        message1.0.extend_from_slice(&message2.0);
        HandshakeData::from(message1)
    }
}

impl From<Bytes> for HandshakeData {
    fn from(value: Bytes) -> Self {
        HandshakeData(value)
    }
}

// Application Data
#[derive(PartialEq)]
pub struct AppData(Bytes);

impl AppData {
    /// Create new application data from raw bytes.
    pub fn new(b: Bytes) -> Self {
        Self(b)
    }

    /// Convert this application data into raw bytes
    pub fn into_raw(self) -> Bytes {
        self.0
    }

    /// Get a reference to the raw bytes.
    pub fn as_raw(&self) -> &Bytes {
        &self.0
    }
}

pub fn random_bytes(len: usize) -> Bytes {
    (0..len)
        .map(|_| rand::random::<u8>())
        .collect::<Vec<u8>>()
        .into()
}
