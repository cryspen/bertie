//! Outside checks for `der.rs`: Wycheproof through Bertie's real parse-then-verify path, and a
//! differential test against independent DER implementations (RustCrypto `der`, `p256`/`ecdsa`,
//! rustls-webpki). None of this is proof; it is evidence from code that is not ours.

use std::collections::BTreeMap;
use std::format;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::string::{String, ToString};
use std::vec;
use std::vec::Vec;

use rand::{Rng, SeedableRng};
use rustls_pki_types::SignatureVerificationAlgorithm;

use crate::der as bertie_der;
use crate::tls13crypto::{
    verify, AeadAlgorithm, Algorithms, HashAlgorithm, KemScheme, PublicVerificationKey,
    SignatureScheme,
};
use crate::tls13formats::{
    handshake_data::{HandshakeData, HandshakeType},
    parse_certificate_verify,
};
use crate::tls13utils::Bytes;

fn from_hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn ecdsa_algorithms() -> Algorithms {
    Algorithms::new(
        HashAlgorithm::SHA256,
        AeadAlgorithm::Aes128Gcm,
        SignatureScheme::EcdsaSecp256r1Sha256,
        KemScheme::Secp256r1,
        false,
        false,
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    Accepted,
    RejectedAtParse,
    RejectedAtVerify,
    Panicked,
}

/// Bertie's real path for a CertificateVerify signature: wrap the DER bytes in a CertificateVerify
/// handshake message, `parse_certificate_verify` (which calls `bertie_der::decode_ecdsa_signature`), then
/// `tls13crypto::verify` (libcrux P-256).
fn bertie_parse_then_verify(pk_xy: &[u8], msg: &[u8], der_sig: &[u8]) -> Outcome {
    let run = || {
        let algs = ecdsa_algorithms();
        let mut body = vec![0x04, 0x03, (der_sig.len() >> 8) as u8, der_sig.len() as u8];
        body.extend_from_slice(der_sig);
        let hd = HandshakeData::from_bytes(HandshakeType::CertificateVerify, &Bytes::from(body))
            .unwrap();
        let raw = match parse_certificate_verify(&algs, &hd) {
            Ok(raw) => raw,
            Err(_) => return Outcome::RejectedAtParse,
        };
        let pk = PublicVerificationKey::EcDsa(Bytes::from(pk_xy));
        match verify(
            &SignatureScheme::EcdsaSecp256r1Sha256,
            &pk,
            &Bytes::from(msg),
            &raw,
        ) {
            Ok(()) => Outcome::Accepted,
            Err(_) => Outcome::RejectedAtVerify,
        }
    };
    catch_unwind(AssertUnwindSafe(run)).unwrap_or(Outcome::Panicked)
}

#[test]
fn wycheproof_through_parse_then_verify() {
    let text = include_str!("../tests/wycheproof/ecdsa_secp256r1_sha256_test.json");
    let json: serde_json::Value = serde_json::from_str(text).unwrap();
    let mut by_class: BTreeMap<(String, Outcome), usize> = BTreeMap::new();
    let mut by_flag: BTreeMap<(String, String), usize> = BTreeMap::new();
    let mut wrong = Vec::new();
    let mut total = 0;
    for group in json["testGroups"].as_array().unwrap() {
        let uncompressed = from_hex(group["publicKey"]["uncompressed"].as_str().unwrap());
        assert_eq!(uncompressed.len(), 65);
        assert_eq!(uncompressed[0], 4);
        let pk_xy = &uncompressed[1..];
        for t in group["tests"].as_array().unwrap() {
            total += 1;
            let tc_id = t["tcId"].as_u64().unwrap();
            let result = t["result"].as_str().unwrap().to_string();
            let outcome = bertie_parse_then_verify(
                pk_xy,
                &from_hex(t["msg"].as_str().unwrap()),
                &from_hex(t["sig"].as_str().unwrap()),
            );
            *by_class.entry((result.clone(), outcome)).or_default() += 1;
            let flags: Vec<String> = t["flags"]
                .as_array()
                .unwrap()
                .iter()
                .map(|f| f.as_str().unwrap().to_string())
                .collect();
            for f in &flags {
                let verdict = if outcome == Outcome::Accepted {
                    "accepted"
                } else {
                    "rejected"
                };
                *by_flag
                    .entry((f.clone(), format!("{result}/{verdict}")))
                    .or_default() += 1;
            }
            let is_wrong = match result.as_str() {
                "valid" => outcome != Outcome::Accepted,
                "invalid" => outcome == Outcome::Accepted || outcome == Outcome::Panicked,
                _ => outcome == Outcome::Panicked,
            };
            if is_wrong {
                wrong.push(format!(
                    "tcId {tc_id} {flags:?} result={result} outcome={outcome:?} ({})",
                    t["comment"].as_str().unwrap()
                ));
            }
        }
    }
    std::println!("WYCHEPROOF-REAL-PATH total={total}");
    for ((class, outcome), n) in &by_class {
        std::println!("WYCHEPROOF-REAL-PATH class={class} outcome={outcome:?} count={n}");
    }
    for ((flag, verdict), n) in &by_flag {
        std::println!("WYCHEPROOF-REAL-PATH flag={flag} {verdict} count={n}");
    }
    std::println!("WYCHEPROOF-REAL-PATH wrong_verdicts={}", wrong.len());
    for w in &wrong {
        std::println!("WRONG {w}");
    }
    assert_eq!(total, 484);
    assert!(wrong.is_empty(), "wrong verdicts: {wrong:?}");
}

// ---- independent DER reference (RustCrypto `der`) ----

fn reference_encode(raw: &[u8]) -> Vec<u8> {
    use der::asn1::{AnyRef, UintRef};
    use der::{Encode, Tag};
    let r = UintRef::new(&raw[..32]).unwrap().to_der().unwrap();
    let s = UintRef::new(&raw[32..]).unwrap().to_der().unwrap();
    let body = [r, s].concat();
    AnyRef::new(Tag::Sequence, &body).unwrap().to_der().unwrap()
}

/// Strict DER decode with the `der` crate; returns the stripped big-endian `r` and `s`.
fn reference_decode(sig: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
    use der::asn1::{AnyRef, UintRef};
    use der::{Decode, Reader, SliceReader, Tag, Tagged};
    let any = AnyRef::from_der(sig).ok()?;
    if any.tag() != Tag::Sequence {
        return None;
    }
    let mut reader = SliceReader::new(any.value()).ok()?;
    let r = UintRef::decode(&mut reader).ok()?;
    let s = UintRef::decode(&mut reader).ok()?;
    reader.finish(()).ok()?;
    Some((r.as_bytes().to_vec(), s.as_bytes().to_vec()))
}

fn strip(b: &[u8]) -> &[u8] {
    let first = b.iter().position(|x| *x != 0).unwrap_or(b.len() - 1);
    &b[first..]
}

fn check_against_reference(raw: &[u8]) -> Result<Vec<u8>, String> {
    let ours =
        bertie_der::encode_ecdsa_signature(raw).map_err(|_| format!("encode failed {raw:02x?}"))?;
    let theirs = reference_encode(raw);
    if ours != theirs {
        return Err(format!(
            "encode mismatch for {raw:02x?}: ours {ours:02x?} ref {theirs:02x?}"
        ));
    }
    let (r, s) = reference_decode(&ours).ok_or_else(|| format!("reference rejects {ours:02x?}"))?;
    if r != strip(&raw[..32]) || s != strip(&raw[32..]) {
        return Err(format!("reference decode value mismatch for {raw:02x?}"));
    }
    match bertie_der::decode_ecdsa_signature(&ours) {
        Ok(back) if back == raw => Ok(ours),
        other => Err(format!(
            "our decode of our encoding {other:?} != {raw:02x?}"
        )),
    }
}

/// 32-byte halves: `zeros` leading zero octets followed by `tail`.
fn half(zeros: usize, tail: u8, rng: &mut impl Rng) -> [u8; 32] {
    let mut h = [0u8; 32];
    for (i, b) in h.iter_mut().enumerate().skip(zeros) {
        *b = match tail {
            0 => rng.random(),
            t => t,
        };
        if i == zeros && *b == 0 {
            *b = 1;
        }
    }
    h
}

fn edge_halves(rng: &mut impl Rng) -> Vec<[u8; 32]> {
    let mut v = vec![[0u8; 32], [0xff; 32]];
    for zeros in 0..=31 {
        for tail in [0x00, 0x01, 0x7f, 0x80, 0xff] {
            v.push(half(zeros, tail, rng));
        }
    }
    let mut one = [0u8; 32];
    one[31] = 1;
    v.push(one);
    v
}

#[test]
fn differential_edge_cases() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xDE12);
    let halves = edge_halves(&mut rng);
    let (mut n, mut mismatches) = (0usize, Vec::new());
    for r in &halves {
        for s in &halves {
            let raw = [r.as_slice(), s.as_slice()].concat();
            n += 1;
            if let Err(e) = check_against_reference(&raw) {
                mismatches.push(e);
            }
        }
    }
    std::println!(
        "DIFFERENTIAL-EDGE inputs={n} mismatches={}",
        mismatches.len()
    );
    assert!(
        mismatches.is_empty(),
        "{:?}",
        &mismatches[..mismatches.len().min(3)]
    );
}

#[test]
fn differential_one_million_random() {
    const TOTAL: usize = 1_000_000;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x00B3_271E);
    let (mut mismatches, mut short_halves) = (Vec::new(), 0usize);
    for i in 0..TOTAL {
        let mut raw = [0u8; 64];
        rng.fill(&mut raw[..]);
        if i % 2 == 1 {
            // biased half: force 0..=32 leading zero octets in each half so short integers are common
            for h in 0..2 {
                let zeros = rng.random_range(0..=32usize);
                raw[h * 32..h * 32 + zeros].fill(0);
            }
        }
        short_halves += (raw[0] == 0) as usize + (raw[32] == 0) as usize;
        if let Err(e) = check_against_reference(&raw) {
            mismatches.push(e);
            if mismatches.len() > 10 {
                break;
            }
        }
    }
    std::println!(
        "DIFFERENTIAL-RANDOM inputs={TOTAL} halves_with_leading_zero_octet={short_halves} mismatches={}",
        mismatches.len()
    );
    assert!(
        mismatches.is_empty(),
        "{:?}",
        &mismatches[..mismatches.len().min(3)]
    );
}

/// The old encoder's rule (fixed 32-byte halves, `00` prepended on a set
/// top bit, redundant leading zeros never stripped). Written here only as a negative control.
fn legacy_style_encode(raw: &[u8]) -> Vec<u8> {
    let int = |half: &[u8]| {
        let mut v = Vec::new();
        if half[0] & 0x80 != 0 {
            v.push(0);
        }
        v.extend_from_slice(half);
        [vec![0x02, v.len() as u8], v].concat()
    };
    let body = [int(&raw[..32]), int(&raw[32..])].concat();
    [vec![0x30, body.len() as u8], body].concat()
}

#[test]
fn webpki_accepts_every_real_signature_we_encode() {
    use p256::ecdsa::{signature::Signer, Signature, SigningKey};
    const SIGNATURES: usize = 100_000;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x5167);
    let sk = SigningKey::from_bytes(&[0x42u8; 32].into()).unwrap();
    let pk = sk.verifying_key().to_encoded_point(false);
    let webpki_alg = webpki::ring::ECDSA_P256_SHA256;
    let (mut short, mut ours_rejected, mut legacy_rejected, mut legacy_short_rejected) =
        (0usize, Vec::new(), 0usize, 0usize);
    for _ in 0..SIGNATURES {
        let mut msg = [0u8; 48];
        rng.fill(&mut msg[..]);
        let sig: Signature = sk.sign(&msg);
        let raw = sig.to_bytes();
        let is_short = raw[0] == 0 || raw[32] == 0;
        short += is_short as usize;
        let ours = bertie_der::encode_ecdsa_signature(&raw).unwrap();
        if webpki_alg
            .verify_signature(pk.as_bytes(), &msg, &ours)
            .is_err()
        {
            ours_rejected.push(format!("{raw:02x?}"));
        }
        let legacy = legacy_style_encode(&raw);
        if webpki_alg
            .verify_signature(pk.as_bytes(), &msg, &legacy)
            .is_err()
        {
            legacy_rejected += 1;
            legacy_short_rejected += is_short as usize;
        }
        // The same signature must also pass Bertie's own parse-then-verify path.
        assert_eq!(
            bertie_parse_then_verify(&pk.as_bytes()[1..], &msg, &ours),
            Outcome::Accepted
        );
    }
    std::println!(
        "WEBPKI signatures={SIGNATURES} with_leading_zero_octet_half={short} \
         fixed_encoder_rejected_by_webpki={} \
         legacy_style_encoder_rejected_by_webpki={legacy_rejected} (of which short-half={legacy_short_rejected})",
        ours_rejected.len()
    );
    assert!(
        ours_rejected.is_empty(),
        "{:?}",
        &ours_rejected[..ours_rejected.len().min(3)]
    );
    assert!(short > 0);
}

#[test]
fn ecdsa_crate_agrees_on_in_range_values() {
    use p256::ecdsa::Signature;
    let mut rng = rand::rngs::StdRng::seed_from_u64(0xEC5A);
    let (mut compared, mut skipped) = (0usize, 0usize);
    for _ in 0..200_000 {
        let mut raw = [0u8; 64];
        rng.fill(&mut raw[..]);
        let zeros = rng.random_range(0..=3usize);
        raw[..zeros].fill(0);
        match Signature::from_slice(&raw) {
            Ok(sig) => {
                compared += 1;
                assert_eq!(
                    sig.to_der().as_bytes(),
                    bertie_der::encode_ecdsa_signature(&raw).unwrap()
                );
            }
            Err(_) => skipped += 1,
        }
    }
    std::println!("ECDSA-CRATE compared={compared} out_of_range_skipped={skipped}");
    assert!(compared > 100_000);
}
