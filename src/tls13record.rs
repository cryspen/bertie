// TLS 1.3 Record Layer Computations

use crate::tls13crypto::*;
use crate::tls13formats::*;
use crate::tls13utils::*;
use crate::tls13keyscheduler::key_schedule::TagKey;

/* CipherStates Exported by the TLS 1.3 Handshake */
pub struct ClientCipherState0(AeadAlgorithm, AeadKeyIV, u64, TagKey);

/// Build the initial client cipher state.
pub(crate) fn client_cipher_state0(
    ae: AeadAlgorithm,
    kiv: AeadKeyIV,
    c: u64,
    k: TagKey,
) -> ClientCipherState0 {
    ClientCipherState0(ae, kiv, c, k)
}

/// The AEAD state of the server with the key, iv, and counter.
pub struct ServerCipherState0 {
    key_iv: AeadKeyIV,
    counter: u64,
    early_exporter_ms: TagKey,
}

/// Create the initial cipher state for the server.
pub(crate) fn server_cipher_state0(
    key_iv: AeadKeyIV,
    counter: u64,
    early_exporter_ms: TagKey,
) -> ServerCipherState0 {
    ServerCipherState0 {
        key_iv,
        counter,
        early_exporter_ms,
    }
}

/// Duplex cipher state with hello keys.
pub struct DuplexCipherStateH {
    sender_key_iv: AeadKeyIV,
    sender_counter: u64,
    receiver_key_iv: AeadKeyIV,
    receiver_counter: u64,
}

impl DuplexCipherStateH {
    /// Create a new state
    pub(crate) fn new(
        sender_key_iv: AeadKeyIV,
        sender_counter: u64,
        receiver_key_iv: AeadKeyIV,
        receiver_counter: u64,
    ) -> Self {
        Self {
            sender_key_iv,
            sender_counter,
            receiver_key_iv,
            receiver_counter,
        }
    }
}

pub struct DuplexCipherState1(AeadAlgorithm, AeadKeyIV, u64, AeadKeyIV, u64, TagKey);

/// Create the next cipher state.
pub(crate) fn duplex_cipher_state1(
    ae: AeadAlgorithm,
    kiv1: AeadKeyIV,
    c1: u64,
    kiv2: AeadKeyIV,
    c2: u64,
    k: TagKey,
) -> DuplexCipherState1 {
    DuplexCipherState1(ae, kiv1, c1, kiv2, c2, k)
}

/// Derive the AEAD IV with counter `n`
fn derive_iv_ctr(iv: &AeadIV, n: u64) -> AeadIV {
    let counter: Bytes = n.to_be_bytes().into();
    let mut iv_ctr = AeadIV::zeroes(iv.len());
    for i in 0..iv.len() - 8 {
        iv_ctr[i] = iv[i];
    }
    for i in 0..8 {
        iv_ctr[i + iv.len() - 8] = iv[i + iv.len() - 8] ^ counter[i];
    }
    iv_ctr
}

/// Encrypt the record `payload` with the given `key_iv`.
pub(crate) fn encrypt_record_payload(
    key_iv: &AeadKeyIV,
    n: u64,
    ct: ContentType,
    payload: Bytes,
    pad: usize,
) -> Result<Bytes, TLSError> {
    let iv_ctr = derive_iv_ctr(&key_iv.iv, n);
    let inner_plaintext = payload.concat(bytes1(ct as u8)).concat(Bytes::zeroes(pad));
    let clen = inner_plaintext.len() + 16;
    if clen <= 65536 {
        let clenb = (clen as u16).to_be_bytes();
        let ad = [23, 3, 3, clenb[0], clenb[1]].into();
        let cip = aead_encrypt(&key_iv.key, &iv_ctr, &inner_plaintext, &ad)?;
        let rec = ad.concat(cip);
        Ok(rec)
    } else {
        Err(PAYLOAD_TOO_LONG)
    }
}

fn padlen(b: &Bytes, n: usize) -> usize {
    if n > 0 && b[n - 1].declassify() == 0 {
        1 + padlen(b, n - 1)
    } else {
        0
    }
}

/// AEAD decrypt the record `ciphertext`
fn decrypt_record_payload(
    kiv: &AeadKeyIV,
    n: u64,
    ciphertext: &Bytes,
) -> Result<(ContentType, Bytes), TLSError> {
    let iv_ctr = derive_iv_ctr(&kiv.iv, n);
    let clen = ciphertext.len() - 5;
    if clen <= 65536 && clen > 16 {
        let clen_bytes = (clen as u16).to_be_bytes();
        let ad = [23, 3, 3, clen_bytes[0], clen_bytes[1]].into();
        check_eq(&ad, &ciphertext.slice_range(0..5))?;

        let cip = ciphertext.slice_range(5..ciphertext.len());
        let plain = aead_decrypt(&kiv.key, &iv_ctr, &cip, &ad)?;

        let payload_len = plain.len() - padlen(&plain, plain.len()) - 1;
        let ct = ContentType::try_from_u8(plain[payload_len].declassify())?;
        let payload = plain.slice_range(0..payload_len);
        Ok((ct, payload))
    } else {
        Err(PAYLOAD_TOO_LONG)
    }
}

/* Record Encryption/Decryption API */

/// Encrypt 0-RTT `payload`.
/// TODO: Implement 0-RTT
#[allow(dead_code)]
fn encrypt_zerortt(
    payload: AppData,
    pad: usize,
    st: ClientCipherState0,
) -> Result<(Bytes, ClientCipherState0), TLSError> {
    let ClientCipherState0(ae, kiv, n, exp) = st;
    let rec = encrypt_record_payload(
        &kiv,
        n,
        ContentType::ApplicationData,
        payload.into_raw(),
        pad,
    )?;
    Ok((rec, ClientCipherState0(ae, kiv, n + 1, exp)))
}

/// Decrypt 0-RTT `ciphertext`.
/// TODO: Implement 0-RTT
#[allow(dead_code)]
pub fn decrypt_zerortt(
    ciphertext: &Bytes,
    state: ServerCipherState0,
) -> Result<(AppData, ServerCipherState0), TLSError> {
    let (ct, payload) = decrypt_record_payload(&state.key_iv, state.counter, ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((
        AppData::new(payload),
        ServerCipherState0 {
            key_iv: state.key_iv,
            counter: state.counter + 1,
            early_exporter_ms: state.early_exporter_ms,
        },
    ))
}

/// Encrypt the `payload` [`HandshakeData`].
///
/// Returns the ciphertext, new [`DuplexCipherStateH`] if successful, or a
/// [`TLSError`] otherwise.
pub(crate) fn encrypt_handshake(
    payload: handshake_data::HandshakeData,
    pad: usize,
    mut state: DuplexCipherStateH,
) -> Result<(Bytes, DuplexCipherStateH), TLSError> {
    let payload = payload.to_bytes();

    let rec = encrypt_record_payload(
        &state.sender_key_iv,
        state.sender_counter,
        ContentType::Handshake,
        payload,
        pad,
    )?;

    state.sender_counter += 1;
    Ok((rec, state))
}

/// Decrypt a handshake message.
pub(crate) fn decrypt_handshake(
    ciphertext: &Bytes,
    mut state: DuplexCipherStateH,
) -> Result<(handshake_data::HandshakeData, DuplexCipherStateH), TLSError> {
    let (ct, payload) =
        decrypt_record_payload(&state.receiver_key_iv, state.receiver_counter, ciphertext)?;
    if ct == ContentType::Alert {
        Result::<(handshake_data::HandshakeData, DuplexCipherStateH), TLSError>::Err(
            GOT_HANDSHAKE_FAILURE_ALERT,
        )
    } else {
        check(ct == ContentType::Handshake)?;
        state.receiver_counter += 1;
        Ok((handshake_data::HandshakeData::from(payload), state))
    }
}

pub fn encrypt_data(
    payload: AppData,
    pad: usize,
    st: DuplexCipherState1,
) -> Result<(Bytes, DuplexCipherState1), TLSError> {
    let DuplexCipherState1(ae, kiv, n, x, y, exp) = st;
    let rec = encrypt_record_payload(
        &kiv,
        n,
        ContentType::ApplicationData,
        payload.into_raw(),
        pad,
    )?;
    Ok((rec, DuplexCipherState1(ae, kiv, n + 1, x, y, exp)))
}

pub fn decrypt_data_or_hs(
    ciphertext: &Bytes,
    st: DuplexCipherState1,
) -> Result<(ContentType, Bytes, DuplexCipherState1), TLSError> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct, payload) = decrypt_record_payload(&kiv, n, ciphertext)?;
    Ok((ct, payload, DuplexCipherState1(ae, x, y, kiv, n + 1, exp)))
}
pub fn decrypt_data(
    ciphertext: &Bytes,
    st: DuplexCipherState1,
) -> Result<(AppData, DuplexCipherState1), TLSError> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct, payload) = decrypt_record_payload(&kiv, n, ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((
        AppData::new(payload),
        DuplexCipherState1(ae, x, y, kiv, n + 1, exp),
    ))
}
