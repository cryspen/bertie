use core::ops::Range;

#[cfg(feature = "hax-fstar")]
use hax_lib::{attributes, requires};

use crate::std::{format, string::String, vec, vec::Vec};

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

#[allow(dead_code)]
pub(crate) fn error_string(c: u8) -> String {
    format!("{}", c)
}

#[cfg(not(test))]
#[hax_lib::ensures(|result| fstar!("not (Core.Result.Result_Ok? result)"))]
pub(crate) fn tlserr<T>(err: TLSError) -> Result<T, TLSError> {
    Err(err)
}

#[cfg(test)]
pub(crate) fn tlserr<T>(err: TLSError) -> Result<T, TLSError> {
    let bt = backtrace::Backtrace::new();
    Err(err)
}

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U8(pub(crate) u8);
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
    pub(crate) fn declassify(self) -> u8 {
        self.0
    }
}

#[hax_lib::attributes]
#[allow(dead_code)]
pub(crate) trait Declassify<T> {
    #[requires(true)]
    fn declassify(self) -> T;
}

#[cfg(not(feature = "secret_integers"))]
impl Declassify<u8> for u8 {
    fn declassify(self) -> u8 {
        self
    }
}

#[cfg(not(feature = "secret_integers"))]
pub(crate) type U8 = u8;

#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub(crate) const fn U8(x: u8) -> U8 {
    x
}

#[cfg(feature = "secret_integers")]
impl From<&u8> for U8 {
    fn from(x: &u8) -> U8 {
        U8(*x)
    }
}

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U16(pub(crate) u16);

#[cfg(not(feature = "secret_integers"))]
pub(crate) type U16 = u16;

#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub(crate) const fn U16(x: u16) -> U16 {
    x
}

#[cfg(feature = "secret_integers")]
impl From<u16> for U16 {
    fn from(x: u16) -> U16 {
        U16(x)
    }
}

#[cfg(feature = "secret_integers")]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct U32(pub(crate) u32);

#[cfg(feature = "secret_integers")]
impl From<u32> for U32 {
    fn from(x: u32) -> U32 {
        U32(x)
    }
}

#[cfg(feature = "secret_integers")]
impl core::ops::Add for U32 {
    type Output = U32;
    fn add(self, y: U32) -> U32 {
        U32(self.0 + y.0)
    }
}

#[cfg(not(feature = "secret_integers"))]
pub(crate) type U32 = u32;

#[cfg(not(feature = "secret_integers"))]
#[allow(non_snake_case)]
pub(crate) const fn U32(x: u32) -> U32 {
    x
}

#[cfg(not(feature = "secret_integers"))]
impl Declassify<u32> for U32 {
    #[inline(always)]
    fn declassify(self) -> u32 {
        self
    }
}

/// Bytes used in Bertie.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Bytes(Vec<U8>);

#[cfg(feature = "secret_integers")]
impl From<Vec<u8>> for Bytes {
    fn from(x: Vec<u8>) -> Bytes {
        Bytes(x.iter().map(|x| x.into()).collect())
    }
}

#[cfg(feature = "secret_integers")]
impl From<Vec<U8>> for Bytes {
    fn from(x: Vec<U8>) -> Bytes {
        Bytes(x)
    }
}

#[cfg(not(feature = "secret_integers"))]
impl From<Vec<u8>> for Bytes {
    fn from(x: Vec<u8>) -> Bytes {
        Bytes(x)
    }
}

#[cfg_attr(
    feature = "hax-pv",
    proverif::replace("fun ${concat_inner}($:{Bytes}, $:{Bytes}): $:{Bytes} [data].")
)]
pub(crate) fn concat_inner(bytes: Bytes, other: Bytes) -> Bytes {
    let mut result = bytes;
        result.extend_from_slice(&other);
        result
}

#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "
    letfun ${eq_inner}(
        b1 : $:{Bytes}, b2 : $:{Bytes}
       ) =
       b1 = b2. (* This is term equality, which may not be what we want? *)"
    )
)]
fn eq_inner(b1: &Bytes, b2: &Bytes) -> bool {
    eq_slice(&b1.0, &b2.0)
}

#[hax_lib::attributes]
impl Bytes {
    /// Add a prefix to these bytes and return it.
    #[cfg_attr(
        feature = "hax-pv",
        proverif::replace_body("${Bytes::concat}($:{Bytes}_from_bitstring(prefix), self)")
    )]
    #[hax_lib::ensures(|result| result.len() >= self.len() && result.len() - self.len() == prefix.len())]
    pub(crate) fn prefix(self, prefix: &[U8]) -> Self {
        let mut out = Vec::with_capacity(prefix.len() + self.len());

        out.extend_from_slice(prefix);
        out.extend_from_slice(&self.0);

        Bytes(out)
    }

    /// Declassify these bytes and return a copy of [`u8`].
    pub fn declassify(&self) -> Vec<u8> {
        self.0.iter().map(|x| x.declassify()).collect()
    }

    /// Convert the bytes into raw bytes
    #[allow(dead_code)]
    pub(crate) fn into_raw(self) -> Vec<U8> {
        self.0
    }

    /// Get a reference to the raw bytes.
    #[allow(dead_code)]
    #[hax_lib::ensures(|result| fstar!(r#"Seq.length result == Seq.length self._0"#))]
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

#[hax_lib::attributes]
impl From<&[u8]> for Bytes {
    #[hax_lib::ensures(|result| result.len() == x.len())]
    fn from(x: &[u8]) -> Bytes {
        x.to_vec().into()
    }
}

#[cfg(feature = "secret_integers")]
impl From<&[U8]> for Bytes {
    fn from(x: &[U8]) -> Bytes {
        Bytes(x.to_vec())
    }
}

#[hax_lib::attributes]
impl<const C: usize> From<[u8; C]> for Bytes {
    #[hax_lib::ensures(|result| result.len() == C)]
    fn from(x: [u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

#[hax_lib::attributes]
impl<const C: usize> From<&[u8; C]> for Bytes {
    #[hax_lib::ensures(|result| result.len() == C)]
    fn from(x: &[u8; C]) -> Bytes {
        x.to_vec().into()
    }
}

#[cfg(feature = "secret_integers")]
impl U32 {
    pub(crate) fn declassify(&self) -> u32 {
        self.0
    }
}
#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "fun ${u16_as_be_bytes}(nat)
    : bitstring [data]."
    )
)]
pub(crate) fn u16_as_be_bytes(val: U16) -> [U8; 2] {
    #[cfg(not(feature = "secret_integers"))]
    let val = val.to_be_bytes();
    #[cfg(feature = "secret_integers")]
    let val = val.0.to_be_bytes();
    [U8(val[0]), U8(val[1])]
}

pub(crate) fn u32_as_be_bytes(val: U32) -> [U8; 4] {
    #[cfg(not(feature = "secret_integers"))]
    let val = val.to_be_bytes();
    #[cfg(feature = "secret_integers")]
    let val = val.0.to_be_bytes();
    [U8(val[0]), U8(val[1]), U8(val[2]), U8(val[3])]
}

pub(crate) fn u32_from_be_bytes(val: [U8; 4]) -> U32 {
    #[cfg(not(feature = "secret_integers"))]
    let val = u32::from_be_bytes(val);
    #[cfg(feature = "secret_integers")]
    let val = u32::from_be_bytes([
        val[0].declassify(),
        val[1].declassify(),
        val[2].declassify(),
        val[3].declassify(),
    ]);

    U32(val)
}

#[hax_lib::ensures(|result| result.len() == x.len())]
pub(crate) fn bytes(x: &[u8]) -> Bytes {
    x.into()
}

#[hax_lib::ensures(|result| result.len() == 1)]
pub(crate) fn bytes1(x: u8) -> Bytes {
    [x].into()
}

#[hax_lib::ensures(|result| result.len() == 2)]
pub(crate) fn bytes2(x: u8, y: u8) -> Bytes {
    [x, y].into()
}

#[hax_lib::attributes]
impl core::ops::Index<usize> for Bytes {
    type Output = U8;
    #[requires(x < self.0.len())]
    fn index(&self, x: usize) -> &U8 {
        &self.0[x]
    }
}

/// This is needed only for hax, so should likely be guarded by a feature flag.
#[hax_lib::fstar::before(
    interface,
    "[@@ FStar.Tactics.Typeclasses.tcinstance]
let update_at_usize_bytes: Rust_primitives.Hax.update_at_tc t_Bytes usize =
   {
     super_index = impl_21;
     update_at = fun s (i:usize{v i < Seq.length s._0}) x -> Bytes (Seq.upd s._0 (v i) x)
   }"
)]
fn _update_at_usize_bytes_test(b: &mut Bytes) {
    if b.len() > 0 {
        b[0] = U8(0)
    };
}

mod non_hax {
    use super::*;
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

#[hax_lib::attributes]
impl core::ops::Index<Range<usize>> for Bytes {
    type Output = [U8];
    #[requires(x.start <= self.0.len() && x.end <= self.0.len())]
    #[hax_lib::ensures(|result| if x.end >= x.start {result.len() == x.end - x.start} else {result.len() == 0})]
    fn index(&self, x: Range<usize>) -> &[U8] {
        &self.0[x]
    }
}

#[cfg_attr(
    feature = "hax-pv",
    proverif::replace(
        "fun ${check_eq_inner}( $:{Bytes}, $:{Bytes}): bitstring
reduc forall b1 : $:{Bytes};
          ${check_eq_inner}(b1,b1) = ()."
    )
)]
fn check_eq_inner(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    check_eq_slice(b1.as_raw(), b2.as_raw())
}

#[hax_lib::attributes]
impl Bytes {
    /// Create new [`Bytes`].
    #[hax_lib::pv_constructor]
    pub(crate) fn new() -> Bytes {
        Bytes(Vec::new())
    }

    /// Create new [`Bytes`].
    #[hax_lib::ensures(|result| fstar!("Seq.length result._0 == 0"))]
    pub(crate) fn new_alloc(len: usize) -> Bytes {
        Bytes(Vec::with_capacity(len))
    }

    /// Generate `len` bytes of `0`.
    #[hax_lib::pv_constructor]
    #[hax_lib::ensures(|result| fstar!("Seq.length result._0 == v len"))]
    pub(crate) fn zeroes(len: usize) -> Bytes {
        Bytes(vec![U8(0); len])
    }

    /// Get the length of these [`Bytes`].
    #[hax_lib::ensures(|result| fstar!("v result == Seq.length self._0"))]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    /// Push `x` into these [`Bytes`].
    pub(crate) fn push(&mut self, x: U8) {
        self.0.push(x)
    }

    /// Extend `self` with the slice `x`.
    pub(crate) fn extend_from_slice(&mut self, x: &Bytes) {
        self.0.extend_from_slice(&x.0)
    }

    /// Extend `self` with the bytes `x`.
    #[hax_lib::ensures(|_| fstar!("Seq.length self_e_future._0 == Seq.length self._0 + Seq.length x._0"))]
    pub(crate) fn append(&mut self, mut x: Bytes) {
        self.0.append(&mut x.0)
    }

    /// Generate a new [`Bytes`] struct from slice `s`.
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

    /// Get a slice of the given `range`.
    #[hax_lib::requires(fstar!(r#"v ${range.start} <= Seq.length self._0 && v ${range.end} <= Seq.length self._0"#))]
    #[hax_lib::ensures(|result| if range.end >= range.start {result.len() == range.end - range.start} else {result.len() == 0})]
    pub(crate) fn raw_slice(&self, range: Range<usize>) -> &[U8] {
        &self.0[range]
    }

    /// Get a new copy of the given `range` as [`Bytes`].
    #[hax_lib::requires(fstar!(r#"v ${range.start} <= Seq.length self._0 && v ${range.end} <= Seq.length self._0"#))]
    #[hax_lib::ensures(|result| if range.end >= range.start {result.0.len() == range.end - range.start} else {result.0.len() == 0})]
    pub(crate) fn slice_range(&self, range: Range<usize>) -> Bytes {
        self.0[range].into()
    }

    /// Get a new copy of the given range `[start..start+len]` as [`Bytes`].
    #[hax_lib::requires(fstar!(r#"v $start <= Seq.length self._0 && v $start + v len <= Seq.length self._0"#))]
    #[hax_lib::ensures(|result| result.0.len() == len)]
    pub(crate) fn slice(&self, start: usize, len: usize) -> Bytes {
        self.0[start..start + len].into()
    }

    /// Concatenate `other` with these bytes and return a copy as [`Bytes`].
    #[hax_lib::ensures(|result| fstar!("Seq.length result._0 == Seq.length self._0 + Seq.length other._0"))]
    pub fn concat(self, other: Bytes) -> Bytes {
        concat_inner(self, other)
    }

    /// Concatenate `other` with these bytes and return a copy as [`Bytes`].
    pub fn concat_array<const N: usize>(mut self, other: [U8; N]) -> Bytes {
        self.0.extend_from_slice(&other);
        self
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

macro_rules! bytes_concat {
    ($bytes1:expr, $bytes2:expr $(, $bytes:expr)*) => {
        {
            let mut len = $bytes1.len() + $bytes2.len();
            $(
                len += $bytes.len();
            )*
            let mut out = Bytes::new_alloc(len);
            out.append($bytes1);
            out.append($bytes2);
            $(
                out.append($bytes);
            )*
            out
        }
    };
}
pub(crate) use bytes_concat;

#[cfg(feature = "hax-pv")]
use hax_lib::{proverif, pv_constructor};

impl Bytes {
    /// Get a hex representation of self as [`String`].
    #[cfg(test)]
    pub(crate) fn as_hex(&self) -> String {
        let strs: Vec<String> = self
            .0
            .iter()
            .map(|b| format!("{:02x}", b.declassify()))
            .collect();
        strs.join("")
    }
}

/// Convert the bool `b` into a Result.
#[hax_lib::ensures(|result| match result {
                             Result::Ok(()) => b == true,
                              _ => true
                    })]
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
#[allow(dead_code)]
pub(crate) fn check_eq1(b1: U8, b2: U8) -> Result<(), TLSError> {
    if eq1(b1, b2) {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

// TODO: This function should short-circuit once hax supports returns within loops
/// Check if [U8] slices `b1` and `b2` are of the same
/// length and agree on all positions.
pub(crate) fn eq_slice(b1: &[U8], b2: &[U8]) -> bool {
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

// TODO: This function should short-circuit once hax supports returns within loops
/// Check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions.
pub fn eq(b1: &Bytes, b2: &Bytes) -> bool {
    eq_inner(b1, b2)
}

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
#[inline(always)]
pub(crate) fn check_eq_slice(b1: &[U8], b2: &[U8]) -> Result<(), TLSError> {
    let b = eq_slice(b1, b2);
    if b {
        Ok(())
    } else {
        Err(parse_failed())
    }
}

/// Parse function to check if two slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
#[inline(always)]
pub(crate) fn check_eq_with_slice(
    b1: &[U8],
    b2: &[U8],
    start: usize,
    end: usize,
) -> Result<(), TLSError> {
    if start > b2.len() || end > b2.len() || end < start {
        Err(parse_failed())
    } else {
        let b = eq_slice(b1, &b2[start..end]);
        if b {
            Ok(())
        } else {
            Err(parse_failed())
        }
    }
}

/// Parse function to check if [Bytes] slices `b1` and `b2` are of the same
/// length and agree on all positions, returning a [TLSError] otherwise.
#[inline(always)]
pub(crate) fn check_eq(b1: &Bytes, b2: &Bytes) -> Result<(), TLSError> {
    check_eq_inner(b1, b2)
}

// TODO: This function should short-circuit once hax supports returns within loops
/// Compare the two provided byte slices.
///
/// Returns `Ok(())` when they are equal, and a [`TLSError`] otherwise.
pub(crate) fn check_mem(b1: &[U8], b2: &[U8]) -> Result<(), TLSError> {
    if b2.len() % b1.len() != 0 {
        Err(parse_failed())
    } else {
        let mut b = false;
        for i in 0..(b2.len() / b1.len()) {
            if eq_slice(b1, &b2[i * b1.len()..(i + 1) * b1.len()]) {
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
#[hax_lib::pv_constructor]
#[hax_lib::ensures(|result| match result {
                                    Result::Ok(lenb) => bytes.len() < 256 && lenb.len() >= 1 && lenb.len() - 1 == bytes.len(),
                                    _ => true})]
pub(crate) fn encode_length_u8(bytes: &[U8]) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 256 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let mut lenb = Bytes::new_alloc(1 + bytes.len());
        lenb.push(U8(len as u8));
        lenb.0.extend_from_slice(bytes);
        Ok(lenb)
    }
}

/// Attempt to TLS encode the `bytes` with [`u16`] length.
///
/// On success, return a new [Bytes] slice such that its first two bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in two bytes.
#[hax_lib::ensures(|result| match result {
                                    Result::Ok(lenb) => bytes.len() < 65536 && lenb.len() >= 2 && lenb.len() - 2 == bytes.len(),
                                    _ => true})]
pub(crate) fn encode_length_u16(mut bytes: Bytes) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len = u16_as_be_bytes(U16(len as u16));
        let mut lenb = Bytes::new_alloc(2 + bytes.len());
        lenb.push(len[0]);
        lenb.push(len[1]);
        lenb.0.append(&mut bytes.0);
        Ok(lenb)
    }
}

/// Attempt to TLS encode the `bytes` with [`u24`] length.
///
/// On success, return a new [Bytes] slice such that its first three bytes encode the
/// big-endian length of `bytes` and the remainder equals `bytes`. Return a [TLSError] if
/// the length of `bytes` exceeds what can be encoded in three bytes.
#[hax_lib::ensures(|result| match result {
                                    Result::Ok(lenb) => bytes.len() < 16777216 && lenb.len() >= 3 && lenb.len() - 3 == bytes.len(),
                                    _ => true})]
pub(crate) fn encode_length_u24(bytes: &Bytes) -> Result<Bytes, TLSError> {
    let len = bytes.len();
    if len >= 16777216 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let len = u32_as_be_bytes(U32(len as u32));
        let mut lenb = Bytes::new_alloc(3 + bytes.len());
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
#[hax_lib::ensures(|result| match result {
    Result::Ok(l) => bytes.len() >= 1 && bytes.len() - 1 >= l && l < 256,
    _ => true
})]
pub(crate) fn length_u8_encoded(bytes: &[U8]) -> Result<usize, TLSError> {
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
#[inline(always)]
#[hax_lib::ensures(|result| match result {
    Result::Ok(l) => bytes.len() >= 2 && bytes.len() - 2 >= l && l < 65536,
    _ => true
})]
pub(crate) fn length_u16_encoded_slice(bytes: &[U8]) -> Result<usize, TLSError> {
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

/// Check if `bytes[2..]` is at least as long as the length encoded by `bytes[0..2]`
/// in big-endian order.
///
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 2
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
#[inline(always)]
#[hax_lib::ensures(|result| match result {
    Result::Ok(l) => bytes.len() >= 2 && bytes.len() - 2 >= l && l < 65536,
    _ => true
})]
pub(crate) fn length_u16_encoded(bytes: &[U8]) -> Result<usize, TLSError> {
    length_u16_encoded_slice(bytes)
}

/// Check if `bytes[3..]` is at least as long as the length encoded by `bytes[0..3]`
/// in big-endian order.
///
/// On success, return the encoded length. Return a [TLSError] if `bytes` is less than 3
/// bytes long or if the encoded length exceeds the length of the remainder of
/// `bytes`.
#[inline(always)]
#[hax_lib::ensures(|result| match result {
                                Result::Ok(l) => bytes.len() >= 3 && bytes.len() - 3 >= l && l < 16777216,
                                _ => true
                            })]
pub(crate) fn length_u24_encoded(bytes: &[U8]) -> Result<usize, TLSError> {
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

#[hax_lib::ensures(|result| match result {
                                    Result::Ok(_) => bytes.len() >= 1 && bytes.len() <= 256,
                                    _ => true})]
pub(crate) fn check_length_encoding_u8_slice(bytes: &[U8]) -> Result<(), TLSError> {
    if length_u8_encoded(bytes)? + 1 != bytes.len() {
        Err(parse_failed())
    } else {
        Ok(())
    }
}

/// Check if `bytes` contains exactly the TLS `u8` length encoded content.
///
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
#[hax_lib::ensures(|result| match result {
                                    Result::Ok(_) => bytes.len() >= 1 && bytes.len() <= 256,
                                    _ => true})]
pub(crate) fn check_length_encoding_u8(bytes: &Bytes) -> Result<(), TLSError> {
    check_length_encoding_u8_slice(bytes.as_raw())
}

#[inline(always)]
#[hax_lib::ensures(|result| match result {
                                    Result::Ok(_) => bytes.len() >= 2 && bytes.len() <= 65537,
                                    _ => true})]
pub(crate) fn check_length_encoding_u16_slice(bytes: &[U8]) -> Result<(), TLSError> {
    if length_u16_encoded(bytes)? + 2 != bytes.len() {
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
#[hax_lib::ensures(|result| match result {
                                Result::Ok(_) => bytes.len() >= 2 && bytes.len() <= 65537,
                                _ => true})]
pub(crate) fn check_length_encoding_u16(bytes: &Bytes) -> Result<(), TLSError> {
    check_length_encoding_u16_slice(bytes.as_raw())
}

/// Check if `bytes` contains exactly as many bytes of content as encoded by its
/// first three bytes.
///
/// Returns `Ok(())` if there are no bytes left, and a [`TLSError`] if there are
/// more bytes in the `bytes`.
#[hax_lib::ensures(|result| match result {
                                Result::Ok(_) => bytes.len() >= 3 && bytes.len() <= 16777218,
                                _ => true})]
pub(crate) fn check_length_encoding_u24(bytes: &[U8]) -> Result<(), TLSError> {
    if length_u24_encoded(bytes)? + 3 != bytes.len() {
        Err(parse_failed())
    } else {
        Ok(())
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

impl From<&[u8]> for AppData {
    fn from(value: &[u8]) -> Self {
        Self(value.into())
    }
}

impl<const N: usize> From<&[u8; N]> for AppData {
    fn from(value: &[u8; N]) -> Self {
        Self(value.into())
    }
}

impl From<Vec<u8>> for AppData {
    fn from(value: Vec<u8>) -> Self {
        Self(value.into())
    }
}

impl From<Bytes> for AppData {
    fn from(value: Bytes) -> Self {
        Self(value)
    }
}

pub fn random_bytes(len: usize) -> Bytes {
    (0..len)
        .map(|_| rand::random::<u8>())
        .collect::<Vec<u8>>()
        .into()
}
