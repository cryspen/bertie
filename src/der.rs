//! DER encoding of ECDSA signatures (`ECDSA-Sig-Value`).
//!
//! The specification is written from the standards, independently of Bertie's encoder and parser.
//! The implementation is proved against P1-P4 and the round trip in F* via hax.
//!
//! Sources: ITU-T X.690 (clauses 8.1.2, 8.1.3, 8.3, 10.1) and RFC 5480 §2.2.3 / RFC 3279 §2.2.3:
//!
//! ```text
//! ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }
//! ```
//!
//! Wire layout: `30 L 02 Lr R 02 Ls S` (`30` = SEQUENCE, `02` = INTEGER, X.690 §8.1.2).
//!
//! ## Clause map
//!
//! | Spec function / clause | Source | What it says |
//! |---|---|---|
//! | `der_uint_valid`: `c` non-empty | X.690 §8.3.1 | INTEGER contents are one or more octets |
//! | `der_uint_valid`: `c[0] < 0x80` | X.690 §8.3.2, §8.3.3 | two's complement; top bit 0 means non-negative |
//! | `der_uint_valid`: not (`c[0]==00` and `c[1]<80`) | X.690 §8.3.2 | first octet and bit 8 of the second octet must not both be 0 (minimal) |
//! | `be_value` | X.690 §8.3.3 | big-endian value of the contents, as a mathematical integer (`hax_lib::int::Int`) |
//! | `der_sig_valid`: `b[0]==0x30`, `b[2]==0x02`, `b[4+Lr]==0x02` | X.690 §8.1.2; RFC 5480 §2.2.3 | tags of the SEQUENCE and the two INTEGERs |
//! | `der_sig_valid`: `L`, `Lr`, `Ls` `< 0x80` | X.690 §8.1.3.3, §8.1.3.4, §10.1 | definite length, short form; DER requires the shortest form, and any length `< 128` has the short form |
//! | `der_sig_valid`: `L == 4+Lr+Ls`, `len(b) == 6+Lr+Ls`, `Lr`/`Ls` count `R`/`S` | X.690 §8.1.3.5 | each length equals the number of contents octets; no trailing octets |
//! | `der_sig_valid`: `be_value(R)==r`, `be_value(S)==s` | RFC 5480 §2.2.3 | the INTEGERs carry r and s |
//! | `der_sig_valid`: `r,s < 2^256` | RFC 5480 (P-256 field size) | the raw `r||s` form has 32 bytes each; 2^256 is the largest range that form can carry |
//!
//! `r = 0` or `s = 0` is DER-valid (`02 01 00`). Rejecting them is a verification matter, not an
//! encoding one, so the encoding spec has no check against the curve order.
//!
//! ## Properties
//!
//! - **P1 encoder correct**: `encode_ecdsa_signature(raw)` with `len(raw)==64` returns `Ok(b)` with
//!   `der_sig_valid(b, be_value(raw[0..32]), be_value(raw[32..64]))` (`encoder_correct`; never `Err`).
//! - **P2 parser sound**: `Ok(x)` implies `len(x)==64` and `der_sig_valid(der, be_value(x[0..32]), be_value(x[32..64]))`
//!   (`parser_sound`).
//! - **P3 parser complete**: for all `r, s`, `der_sig_valid(der, r, s)` implies `Ok(x)` with
//!   `len(x)==64`, `be_value(x[0..32])==r`, `be_value(x[32..64])==s` (`parser_complete`, a `forall`).
//! - **P4 uniqueness**: `der_sig_valid(b1,r,s) && der_sig_valid(b2,r,s)` implies `b1 == b2`
//!   (`der_sig_unique`, with `requires`/`ensures`).
//!
//! The round trip `decode_ecdsa_signature(encode_ecdsa_signature(raw)) == Ok(raw)` for any
//! 64-byte `raw` is proved by `der_roundtrip`, using `be_value_prefix_injective` and `uint_unique`.
//!
//! P1 + P2 + P3 + P4 rule out the original bug class: P1 forces the encoder's output to be the unique
//! valid encoding, and P3 forces the parser to accept it; a shared mistake in both (as in the old code)
//! contradicts the spec, because the spec does not refer to either.
//!
//! ## Choices a reviewer should check
//!
//! 1. **Positional layout.** `der_sig_valid` locates `R` and `S` from the length octets (`Lr` at
//!    `b[3]`, `Ls` at `b[5+Lr]`). This is the TLV structure itself, not a parsing strategy; with all
//!    lengths in short form the layout is forced.
//! 2. **`r,s < 2^256` is part of the encoding spec.** Together with short-form-only lengths this means a
//!    DER-valid signature has `Lr, Ls <= 33` and `L <= 70`. A DER signature with a larger INTEGER is
//!    not "valid" here, so P3 does not require the parser to accept it. Rejecting it is what a 32-byte
//!    `r||s` interface needs.
//! 3. **Spec predicates are executable Rust, but only with `--cfg hax`.** Outside `cfg(hax)`,
//!    `hax_lib::int::Int` is a one-byte dummy (hax-lib 0.4.2 `dummy.rs`). The spec tests therefore run
//!    with `RUSTFLAGS='--cfg hax'`; the unit tests are gated on `cfg(all(test, hax))`.
//! 4. **Interface opacity.** hax emits the spec predicates as `val ... : Pure bool True (fun _ -> True)`
//!    in `Bertie.Der.fsti`, so other modules see only the contracts on `encode_`/`decode_`, not
//!    the bodies. The byte-level round trip is proved in `der_roundtrip`. The `certificate_verify`
//!    round trip at the `Bytes` level still relies on its `defensive` runtime check because the
//!    conversions in `tls13utils` have no functional specification.
//! 5. **Termination of `be_value_prefix`.** A plain `decreases(n)` on a `usize` is rejected by F*; the
//!    measure is `n.to_int()`.
//! 6. **Types.** The functions take `&[u8]` and return `Vec<u8>`, not Bertie's `Bytes`/`U8`. The
//!    `tls13formats` wrapper converts at the boundary; that conversion lives in `tls13utils`, which hax
//!    extracts as an interface only, so it is trusted.

#![cfg_attr(not(hax), allow(dead_code, unused_imports))]
#![allow(clippy::if_same_then_else)]

use hax_lib::int::{Int, ToInt};
use hax_lib::{Prop, ToProp};

use crate::std::{vec, vec::Vec};
use crate::tls13utils::{TLSError, INVALID_SIGNATURE};

/// Length of a P-256 signature in the raw `r || s` form.
pub const RAW_SIGNATURE_LEN: usize = 64;

/// 2^256: the bound on `r` and `s` for a signature over a 256-bit curve.
#[hax_lib::ensures(|bound| bound > 0u8.to_int())]
pub fn two_pow_256() -> Int {
    256u16.to_int().pow2()
}

/// The big-endian unsigned value of the first `n` bytes of `c`.
#[hax_lib::requires(n <= c.len())]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix(c: &[u8], n: usize) -> Int {
    if n == 0 {
        0u8.to_int()
    } else {
        be_value_prefix(c, n - 1) * 256u16.to_int() + c[n - 1].to_int()
    }
}

/// The big-endian unsigned value of `c`.
pub fn be_value(c: &[u8]) -> Int {
    be_value_prefix(c, c.len())
}

/// `c` is the contents of a DER INTEGER that encodes a non-negative number minimally.
///
/// - non-empty: X.690 §8.3.1 (contents are one or more octets);
/// - `c[0] < 0x80`: the leading bit is 0, so the two's-complement value is non-negative
///   (X.690 §8.3.2 / §8.3.3);
/// - no redundant leading `00`: the first octet and the bit 8 of the second octet must not
///   both be 0 (X.690 §8.3.2). With `c[0] == 0x00` the second octet's top bit must be 1,
///   so a `00` is allowed only where it is needed for the sign.
pub fn der_uint_valid(c: &[u8]) -> bool {
    if c.is_empty() {
        false
    } else if c[0] >= 0x80 {
        false
    } else if c.len() > 1 {
        !(c[0] == 0x00 && c[1] < 0x80)
    } else {
        true
    }
}

/// `b` is exactly the DER encoding of `ECDSA-Sig-Value { r, s }` with `r, s < 2^256`.
///
/// `30 L 02 Lr R 02 Ls S`, each length in short definite form and equal to the number of
/// contents octets that follow it (X.690 §8.1.3.3 and §8.1.3.4, DER §10.1: the shortest form;
/// every length here is below 128 so only the short form is minimal), no trailing octets,
/// `R` and `S` minimal non-negative INTEGER contents, and their values equal to `r` and `s`.
pub fn der_sig_valid(b: &[u8], r: Int, s: Int) -> bool {
    if b.len() < 8 {
        return false;
    }
    let r_len = b[3] as usize;
    if b.len() < 6 + r_len {
        return false;
    }
    let s_len = b[5 + r_len] as usize;
    let r_bytes = &b[4..4 + r_len];
    if b.len() != 6 + r_len + s_len {
        return false;
    }
    let s_bytes = &b[6 + r_len..];
    b[0] == 0x30
        && b[1] < 0x80
        && b[1] as usize == 4 + r_len + s_len
        && b[2] == 0x02
        && b[3] < 0x80
        && b[4 + r_len] == 0x02
        && b[5 + r_len] < 0x80
        && der_uint_valid(r_bytes)
        && der_uint_valid(s_bytes)
        && be_value(r_bytes) == r
        && be_value(s_bytes) == s
        && r < two_pow_256()
        && s < two_pow_256()
}

/// P1 as a predicate on the encoder's result for the raw input `raw` (`r || s`, 32 bytes each).
#[hax_lib::requires(raw.len() == RAW_SIGNATURE_LEN)]
pub fn encoder_correct(raw: &[u8], result: &Result<Vec<u8>, TLSError>) -> bool {
    match result {
        Ok(b) => der_sig_valid(b, be_value(&raw[0..32]), be_value(&raw[32..64])),
        Err(_) => false,
    }
}

/// P2 as a predicate on the parser's result for the DER input `der`.
pub fn parser_sound(der: &[u8], result: &Result<Vec<u8>, TLSError>) -> bool {
    match result {
        Ok(x) => {
            x.len() == RAW_SIGNATURE_LEN
                && der_sig_valid(der, be_value(&x[0..32]), be_value(&x[32..64]))
        }
        Err(_) => true,
    }
}

/// P3 as a proposition on the parser's result for the DER input `der`: every `(r, s)` for
/// which `der` is a valid encoding is returned, as 32-byte big-endian halves.
pub fn parser_complete(der: &[u8], result: &Result<Vec<u8>, TLSError>) -> Prop {
    hax_lib::forall(|r: Int| {
        hax_lib::forall(|s: Int| {
            hax_lib::implies(
                der_sig_valid(der, r, s),
                match result {
                    Ok(x) => {
                        x.len() == RAW_SIGNATURE_LEN
                            && be_value(&x[0..32]) == r
                            && be_value(&x[32..64]) == s
                    }
                    Err(_) => false,
                },
            )
        })
    })
}

// ---------------------------------------------------------------------------------------
// Proof support. Everything below `cfg(hax)` exists only for extraction and F* checking.
// ---------------------------------------------------------------------------------------

/// 256^n.
#[cfg(hax)]
#[hax_lib::ensures(|p| p >= 1u8.to_int())]
#[hax_lib::decreases(n.to_int())]
fn pow256(n: usize) -> Int {
    if n == 0 {
        1u8.to_int()
    } else {
        pow256(n - 1) * 256u16.to_int()
    }
}

/// `pow256` is monotone.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires(k <= m)]
#[hax_lib::ensures(|_| pow256(m) >= pow256(k))]
#[hax_lib::decreases(m.to_int())]
fn pow256_mono(m: usize, k: usize) {
    if m > k {
        pow256_mono(m - 1, k);
    }
}

/// `pow256(n) = 2^(8n)`.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 10 --z3rlimit 100 --split_queries always")]
#[hax_lib::requires(n <= 64)]
#[hax_lib::ensures(|_| pow256(n) == (n.to_int() * 8u8.to_int()).pow2())]
#[hax_lib::decreases(n.to_int())]
fn pow256_is_pow2(n: usize) {
    if n > 0 {
        pow256_is_pow2(n - 1);
    }
}

/// `256^32 = 2^256`.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::ensures(|_| pow256(32) == two_pow_256())]
fn pow256_32_is_bound() {
    pow256_is_pow2(32);
}

/// The first `k` bytes of `a` are zero.
#[cfg(hax)]
fn zero_prefix(a: &[u8], k: usize) -> Prop {
    hax_lib::forall(|i: usize| hax_lib::implies(i < k && i < a.len(), a[i] == 0))
}

/// `b[i] == a[k + i]` for the first `m` bytes of `b`.
#[cfg(hax)]
fn shifted_eq(a: &[u8], k: usize, b: &[u8], m: Int) -> Prop {
    hax_lib::forall(|i: usize| {
        hax_lib::implies(
            i.to_int() < m && i < b.len() && k.to_int() + i.to_int() < a.len().to_int(),
            b[i] == a[k + i],
        )
    })
}

/// A big-endian value is non-negative and below 256^n.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires(n <= c.len())]
#[hax_lib::ensures(|_| be_value_prefix(c, n) >= 0u8.to_int() && be_value_prefix(c, n) < pow256(n))]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix_bound(c: &[u8], n: usize) {
    if n > 0 {
        be_value_prefix_bound(c, n - 1);
    }
}

/// A value whose first octet is non-zero is at least 256^(n-1).
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires(n >= 1 && n <= c.len() && (if c.len() > 0 { c[0] >= 1 } else { false }))]
#[hax_lib::ensures(|_| be_value_prefix(c, n) >= pow256(n - 1))]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix_lower_bound(c: &[u8], n: usize) {
    if n > 1 {
        be_value_prefix_lower_bound(c, n - 1);
    }
}

/// Dropping `k` leading zero octets, or padding with `k`, does not change the value:
/// the `n` octets of `a` (the first `k` being zero) have the value of the `n - k` octets of `b`
/// when `b[i] == a[k + i]`.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 150")]
#[hax_lib::requires(
    (k <= n && n <= a.len() && n.to_int() - k.to_int() <= b.len().to_int())
        .to_prop()
        .and(zero_prefix(a, k))
        .and(shifted_eq(a, k, b, n.to_int() - k.to_int()))
)]
#[hax_lib::ensures(|_| be_value_prefix(a, n) == be_value_prefix(b, n - k))]
#[hax_lib::decreases(n.to_int())]
fn be_value_shift(a: &[u8], b: &[u8], n: usize, k: usize) {
    if n > 0 {
        if n == k {
            be_value_shift(a, b, n - 1, k - 1);
        } else {
            be_value_shift(a, b, n - 1, k);
        }
    }
}

/// Index of the first non-zero octet of `buf[i..32]`, or 32.
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 100")]
#[hax_lib::requires((buf.len() == 33 && i >= 1 && i <= 32).to_prop().and(zero_prefix(buf, i)))]
#[hax_lib::ensures(|z| (i <= z && z <= 32).to_prop()
    .and(zero_prefix(buf, z))
    .and((if z < 32 { buf[z] != 0 } else { true }).to_prop()))]
#[hax_lib::decreases(32u8.to_int() - i.to_int())]
fn skip_zeros(buf: &[u8], i: usize) -> usize {
    if i < 32 {
        if buf[i] == 0 {
            skip_zeros(buf, i + 1)
        } else {
            i
        }
    } else {
        i
    }
}

// ---------------------------------------------------------------------------------------
// Encoder
// ---------------------------------------------------------------------------------------

/// The contents octets of the minimal DER INTEGER for the 32-octet big-endian value `h`:
/// the value is prefixed with `00`, leading zeros are dropped, and a single `00` is kept
/// only where the sign bit needs it (or for the value zero).
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 200")]
#[hax_lib::requires(h.len() == 32)]
#[hax_lib::ensures(|c| der_uint_valid(c.as_slice()) && c.len() <= 33 && be_value(c.as_slice()) == be_value(h))]
fn encode_uint(h: &[u8]) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::with_capacity(33);
    buf.push(0u8);
    buf.extend_from_slice(h);
    let z = skip_zeros(buf.as_slice(), 1);
    let j = if buf[z] >= 0x80 { z - 1 } else { z };
    let c = buf[j..].to_vec();
    #[cfg(hax)]
    {
        be_value_shift(buf.as_slice(), h, 33, 1);
        be_value_shift(buf.as_slice(), c.as_slice(), 33, j);
    }
    c
}

/// P1: DER-encode a raw 64-byte `r || s`.
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 400 --split_queries always")]
#[hax_lib::requires(raw.len() == RAW_SIGNATURE_LEN)]
#[hax_lib::ensures(|result| encoder_correct(raw, &result))]
pub fn encode_ecdsa_signature(raw: &[u8]) -> Result<Vec<u8>, TLSError> {
    let r = encode_uint(&raw[0..32]);
    let s = encode_uint(&raw[32..64]);
    let mut out: Vec<u8> = Vec::with_capacity(6 + r.len() + s.len());
    out.push(0x30);
    out.push((4 + r.len() + s.len()) as u8);
    out.push(0x02);
    out.push(r.len() as u8);
    out.extend_from_slice(r.as_slice());
    out.push(0x02);
    out.push(s.len() as u8);
    out.extend_from_slice(s.as_slice());
    #[cfg(hax)]
    {
        be_value_shift(&out[4..4 + r.len()], r.as_slice(), r.len(), 0);
        be_value_shift(&out[6 + r.len()..], s.as_slice(), s.len(), 0);
        be_value_prefix_bound(&raw[0..32], 32);
        be_value_prefix_bound(&raw[32..64], 32);
        pow256_32_is_bound();
    }
    Ok(out)
}

// ---------------------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------------------

/// The 32-octet big-endian form of the INTEGER contents `c`, or `Err` when the value does not
/// fit in 256 bits.
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 300")]
#[hax_lib::requires(der_uint_valid(c))]
#[hax_lib::ensures(|res| match res {
    Ok(v) => v.len() == 32 && be_value(v.as_slice()) == be_value(c),
    Err(_) => be_value(c) >= two_pow_256(),
})]
fn uint_to_32_bytes(c: &[u8]) -> Result<Vec<u8>, TLSError> {
    let start = if c.len() > 1 && c[0] == 0 { 1 } else { 0 };
    let n = c.len() - start;
    let cs = &c[start..];
    #[cfg(hax)]
    be_value_shift(c, cs, c.len(), start);
    if n > 32 {
        #[cfg(hax)]
        {
            be_value_prefix_lower_bound(cs, n);
            pow256_mono(n - 1, 32);
            pow256_32_is_bound();
        }
        Err(INVALID_SIGNATURE)
    } else {
        let mut v: Vec<u8> = vec![0u8; 32 - n];
        v.extend_from_slice(cs);
        #[cfg(hax)]
        be_value_shift(v.as_slice(), cs, 32, 32 - n);
        Ok(v)
    }
}

/// P2 and P3: decode a DER `ECDSA-Sig-Value` into the raw 64-byte `r || s`.
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 400")]
#[hax_lib::ensures(|result| parser_sound(der, &result).to_prop().and(parser_complete(der, &result)))]
pub fn decode_ecdsa_signature(der: &[u8]) -> Result<Vec<u8>, TLSError> {
    if der.len() < 8 {
        return Err(INVALID_SIGNATURE);
    }
    let r_len = der[3] as usize;
    if der.len() < 6 + r_len {
        return Err(INVALID_SIGNATURE);
    }
    let s_len = der[5 + r_len] as usize;
    if der.len() != 6 + r_len + s_len {
        return Err(INVALID_SIGNATURE);
    }
    let r_bytes = &der[4..4 + r_len];
    let s_bytes = &der[6 + r_len..];
    let well_formed = der[0] == 0x30
        && der[1] < 0x80
        && der[1] as usize == 4 + r_len + s_len
        && der[2] == 0x02
        && der[3] < 0x80
        && der[4 + r_len] == 0x02
        && der[5 + r_len] < 0x80
        && der_uint_valid(r_bytes)
        && der_uint_valid(s_bytes);
    if !well_formed {
        return Err(INVALID_SIGNATURE);
    }
    let r = uint_to_32_bytes(r_bytes)?;
    let s = uint_to_32_bytes(s_bytes)?;
    let mut out: Vec<u8> = Vec::with_capacity(RAW_SIGNATURE_LEN);
    out.extend_from_slice(r.as_slice());
    out.extend_from_slice(s.as_slice());
    #[cfg(hax)]
    {
        be_value_shift(&out[0..32], r.as_slice(), 32, 0);
        be_value_shift(&out[32..64], s.as_slice(), 32, 0);
        be_value_prefix_bound(&out[0..32], 32);
        be_value_prefix_bound(&out[32..64], 32);
        pow256_32_is_bound();
    }
    Ok(out)
}

/// `a` and `b` agree on their first `n` octets.
#[cfg(hax)]
fn agree(a: &[u8], b: &[u8], n: usize) -> Prop {
    hax_lib::forall(|i: usize| hax_lib::implies(i < n && i < a.len() && i < b.len(), a[i] == b[i]))
}

/// A value whose first octet is below 0x80 is below 128 * 256^(n-1).
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires(n >= 1 && n <= c.len() && (if c.len() > 0 { c[0] < 0x80 } else { false }))]
#[hax_lib::ensures(|_| be_value_prefix(c, n) < 128u8.to_int() * pow256(n - 1))]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix_upper_128(c: &[u8], n: usize) {
    if n > 1 {
        be_value_prefix_upper_128(c, n - 1);
    }
}

/// A value whose first octet is at least 0x80 is at least 128 * 256^(n-1).
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires(n >= 1 && n <= c.len() && (if c.len() > 0 { c[0] >= 0x80 } else { false }))]
#[hax_lib::ensures(|_| be_value_prefix(c, n) >= 128u8.to_int() * pow256(n - 1))]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix_lower_128(c: &[u8], n: usize) {
    if n > 1 {
        be_value_prefix_lower_128(c, n - 1);
    }
}

/// A minimal INTEGER of `n` octets has a value in `[L(n), 128 * 256^(n-1))` where
/// `L(1) = 0` and `L(n) = 128 * 256^(n-2)`; these intervals are disjoint for different `n`.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 200")]
#[hax_lib::requires(c.len() >= 1 && der_uint_valid(c))]
#[hax_lib::ensures(|_| (be_value(c) < 128u8.to_int() * pow256(c.len() - 1)).to_prop()
    .and((if c.len() >= 2 { be_value(c) >= 128u8.to_int() * pow256(c.len() - 2) } else { true }).to_prop()))]
fn uint_range(c: &[u8]) {
    be_value_prefix_upper_128(c, c.len());
    if c[0] != 0 {
        be_value_prefix_lower_bound(c, c.len());
    } else if c.len() >= 2 {
        let d = &c[1..];
        be_value_shift(c, d, c.len(), 1);
        be_value_prefix_lower_128(d, c.len() - 1);
    }
}

/// Equal values of minimal INTEGERs imply equal lengths.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 100")]
#[hax_lib::requires(c1.len() >= 1 && c2.len() >= 1 && der_uint_valid(c1) && der_uint_valid(c2) && be_value(c1) == be_value(c2))]
#[hax_lib::ensures(|_| c1.len() == c2.len())]
fn uint_len_unique(c1: &[u8], c2: &[u8]) {
    uint_range(c1);
    uint_range(c2);
    if c1.len() < c2.len() {
        pow256_mono(c2.len() - 2, c1.len() - 1);
    } else if c2.len() < c1.len() {
        pow256_mono(c1.len() - 2, c2.len() - 1);
    }
}

/// `be_value` is injective on equal-length slices.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 100")]
#[hax_lib::requires(n <= a.len() && n <= b.len() && be_value_prefix(a, n) == be_value_prefix(b, n))]
#[hax_lib::ensures(|_| agree(a, b, n))]
#[hax_lib::decreases(n.to_int())]
fn be_value_prefix_injective(a: &[u8], b: &[u8], n: usize) {
    if n > 0 {
        be_value_prefix_injective(a, b, n - 1);
    }
}

/// Two minimal INTEGERs with the same value are the same octets.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 100")]
#[hax_lib::requires(c1.len() >= 1 && c2.len() >= 1 && der_uint_valid(c1) && der_uint_valid(c2) && be_value(c1) == be_value(c2))]
#[hax_lib::ensures(|_| (c1.len() == c2.len()).to_prop().and(agree(c1, c2, c1.len())))]
fn uint_unique(c1: &[u8], c2: &[u8]) {
    uint_len_unique(c1, c2);
    be_value_prefix_injective(c1, c2, c1.len());
}

/// Instantiates `agree` at one index.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 50")]
#[hax_lib::requires((i < n && i < a.len() && i < b.len()).to_prop().and(agree(a, b, n)))]
#[hax_lib::ensures(|_| a[i] == b[i])]
fn agree_elim(a: &[u8], b: &[u8], n: usize, i: usize) {}

/// P4: the DER encoding of a given `(r, s)` is unique. This is what makes P1-P3 rule
/// out the non-minimal-integer bug class: two different byte strings cannot both be valid.
///
/// The R and S contents are equal by `uint_unique`; the remaining octets are fixed by the
/// definition of `der_sig_valid`. The closing `fstar!` only turns pointwise equality into
/// sequence equality (`FStar.Seq.lemma_eq_elim`); it adds no hypotheses.
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 100")]
#[hax_lib::requires(der_sig_valid(b1, r, s) && der_sig_valid(b2, r, s))]
#[hax_lib::ensures(|_| b1 == b2)]
pub fn der_sig_unique(b1: &[u8], b2: &[u8], r: Int, s: Int) {
    #[cfg(hax)]
    {
        let rl1 = b1[3] as usize;
        let rl2 = b2[3] as usize;
        let r1 = &b1[4..4 + rl1];
        let r2 = &b2[4..4 + rl2];
        uint_unique(r1, r2);
        let sl1 = b1[5 + rl1] as usize;
        let sl2 = b2[5 + rl2] as usize;
        let s1 = &b1[6 + rl1..];
        let s2 = &b2[6 + rl2..];
        uint_unique(s1, s2);
        hax_lib::fstar!(
            r#"(let aux (i: nat{i < Seq.length b1 /\ i < Seq.length b2})
    : Lemma (Seq.index b1 i == Seq.index b2 i) =
  if i >= 4 && i < 4 + v rl1
  then (let _ = agree_elim r1 r2 (Core_models.Slice.impl__len #u8 r1) (mk_usize (i - 4)) in ())
  else if i >= 6 + v rl1
  then (let _ = agree_elim s1 s2 (Core_models.Slice.impl__len #u8 s1) (mk_usize (i - 6 - v rl1)) in ())
  else ()
in
FStar.Classical.forall_intro aux;
FStar.Seq.lemma_eq_intro b1 b2;
FStar.Seq.lemma_eq_elim b1 b2)"#
        );
    }
}

/// Round trip: decoding the encoding of `raw` returns `raw`. It follows from
/// P1 (the encoding is valid for the values of the halves), P3 (the decoder returns 32-byte
/// halves with those values) and the injectivity of `be_value` on equal-length slices.
#[cfg(hax)]
#[hax_lib::fstar::options("--fuel 2 --z3rlimit 200 --split_queries always")]
#[hax_lib::requires(raw.len() == RAW_SIGNATURE_LEN)]
#[hax_lib::ensures(|_| match encode_ecdsa_signature(raw) {
    Ok(b) => match decode_ecdsa_signature(b.as_slice()) {
        Ok(x) => x.as_slice() == raw,
        Err(_) => false,
    },
    Err(_) => false,
})]
pub fn der_roundtrip(raw: &[u8]) {
    if let Ok(b) = encode_ecdsa_signature(raw) {
        if let Ok(x) = decode_ecdsa_signature(b.as_slice()) {
            let xa = x.as_slice();
            let xr = &xa[0..32];
            let rr = &raw[0..32];
            let xs = &xa[32..64];
            let rs = &raw[32..64];
            be_value_prefix_injective(xr, rr, 32);
            be_value_prefix_injective(xs, rs, 32);
            hax_lib::fstar!(
                r#"(let aux (i: nat{i < Seq.length xa /\ i < Seq.length raw})
    : Lemma (Seq.index xa i == Seq.index raw i) =
  if i < 32
  then (let _ = agree_elim xr rr (mk_usize 32) (mk_usize i) in ())
  else (let _ = agree_elim xs rs (mk_usize 32) (mk_usize (i - 32)) in ())
in
FStar.Classical.forall_intro aux;
FStar.Seq.lemma_eq_intro xa raw;
FStar.Seq.lemma_eq_elim xa raw)"#
            );
        }
    }
}

// `hax_lib::int::Int` is a one-byte stub unless compiled with `--cfg hax`, so the executable
// spec checks only run there: RUSTFLAGS='--cfg hax' cargo test --lib der::
#[cfg(all(test, hax))]
mod tests {
    use super::*;
    use crate::std::{format, string::String, vec, vec::Vec};

    fn from_hex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    /// The spec predicate over all `(r, s)`: if `b` has the `30 L 02 Lr R 02 Ls S` layout then
    /// `r` and `s` are forced to be the values of `R` and `S`, so these are the only witnesses.
    fn der_sig_valid_for_some_values(b: &[u8]) -> bool {
        if b.len() < 8 || b.len() < 6 + b[3] as usize {
            return false;
        }
        let r_len = b[3] as usize;
        let s_len = b[5 + r_len] as usize;
        if b.len() != 6 + r_len + s_len {
            return false;
        }
        let r = be_value(&b[4..4 + r_len]);
        let s = be_value(&b[6 + r_len..]);
        der_sig_valid(b, r, s)
    }

    #[test]
    fn known_answers_from_x690() {
        let valid = [
            "3006020101020101",     // r = 1, s = 1
            "3006020100020100",     // r = s = 0: DER-valid, rejected only by verification
            "300702027fff020100",   // r = 0x7fff
            "3007020200ff020100",   // r = 0xff needs the sign octet
            "30080202008002020080", // r = s = 0x80
            "30260221008000000000000000000000000000000000000000000000000000000000000000020101", // r = 2^255 needs 33 octets, s = 1
        ];
        for h in valid {
            assert!(der_sig_valid_for_some_values(&from_hex(h)), "{h}");
        }
        let invalid = [
            "3006020101020101ff",   // trailing octet
            "3006020002020102",     // empty INTEGER contents
            "300702020001020101",   // redundant leading 00 on r
            "30080203000080020101", // two leading 00 on r = 0x80
            "3006020180020101",     // negative r: top bit set, no sign octet
            "308006020101020101",   // BER indefinite length
            "308106020101020101",   // long-form length where short form is required
            "3106020101020101",     // SET instead of SEQUENCE
            "3006030101020101",     // BIT STRING instead of INTEGER
            "3005020101020101",     // SEQUENCE length too small
        ];
        for h in invalid {
            assert!(!der_sig_valid_for_some_values(&from_hex(h)), "{h}");
        }
    }

    #[test]
    fn spec_distinguishes_values() {
        let b = from_hex("3006020101020102");
        assert!(der_sig_valid(&b, 1u8.to_int(), 2u8.to_int()));
        assert!(!der_sig_valid(&b, 2u8.to_int(), 1u8.to_int()));
        let big = two_pow_256();
        let b = from_hex("3006020101020101");
        assert!(!der_sig_valid(&b, big, 1u8.to_int()));
    }
}
