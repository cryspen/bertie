use rand::{CryptoRng, RngCore};

use crate::{
    server::{lookup_db, ServerDB, ServerInfo},
    tls13cert::{cert_public_key, rsa_public_key, verification_key_from_cert},
    tls13crypto::{
        hkdf_expand, hkdf_extract, hmac_tag, hmac_verify, kem_decap, kem_encap, kem_keygen, sign,
        sign_rsa, verify, zero_key, AeadAlgorithm, AeadKey, AeadKeyIV, Algorithms, Digest,
        HashAlgorithm, KemSk, Key, MacKey, Psk, Random, SignatureScheme,
    },
    tls13formats::{handshake_data::HandshakeData, *},
    tls13record::*,
    tls13utils::*,
};

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

/// Get the hash of an empty byte slice.
fn hash_empty(algorithm: &HashAlgorithm) -> Result<Digest, TLSError> {
    algorithm.hash(&Bytes::new())
}

/// HKDF expand with a `label`.
fn hkdf_expand_label(
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: Bytes,
    context: &Bytes,
    len: usize,
) -> Result<Key, TLSError> {
    if len >= 65536 {
        Err(PAYLOAD_TOO_LONG)
    } else {
        let lenb = u16_as_be_bytes(U16(len as u16));
        let tls13_label = Bytes::from_slice(&LABEL_TLS13).concat(label);
        let info = encode_length_u8(tls13_label.as_raw())?
            .concat(encode_length_u8(context.as_raw())?)
            .prefix(&lenb);
        hkdf_expand(hash_algorithm, key, &info, len)
    }
}

pub fn derive_secret(
    hash_algorithm: &HashAlgorithm,
    key: &Key,
    label: Bytes,
    transcript_hash: &Digest,
) -> Result<Key, TLSError> {
    hkdf_expand_label(
        hash_algorithm,
        key,
        label,
        transcript_hash,
        hash_algorithm.hash_len(),
    )
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    let early_secret = hkdf_extract(ha, k, &zero_key(ha))?;
    derive_secret(
        ha,
        &early_secret,
        bytes(&LABEL_RES_BINDER),
        &hash_empty(ha)?,
    )
}

/// Derive an AEAD key and iv.
pub(crate) fn derive_aead_key_iv(
    hash_algorithm: &HashAlgorithm,
    aead_algorithm: &AeadAlgorithm,
    key: &Key,
) -> Result<AeadKeyIV, TLSError> {
    let sender_write_key = hkdf_expand_label(
        hash_algorithm,
        key,
        bytes(&LABEL_KEY),
        &Bytes::new(),
        aead_algorithm.key_len(),
    )?;
    let sender_write_iv = hkdf_expand_label(
        hash_algorithm,
        key,
        bytes(&LABEL_IV),
        &Bytes::new(),
        aead_algorithm.iv_len(),
    )?;
    Ok(AeadKeyIV::new(
        AeadKey::new(sender_write_key, *aead_algorithm),
        sender_write_iv,
    ))
}

/// Derive 0-RTT AEAD keys.
pub(crate) fn derive_0rtt_keys(
    hash_algorithm: &HashAlgorithm,
    aead_algoorithm: &AeadAlgorithm,
    key: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, Key), TLSError> {
    let early_secret = hkdf_extract(hash_algorithm, key, &zero_key(hash_algorithm))?;
    let client_early_traffic_secret =
        derive_secret(hash_algorithm, &early_secret, bytes(&LABEL_C_E_TRAFFIC), tx)?;
    let early_exporter_master_secret = derive_secret(
        hash_algorithm,
        &early_secret,
        bytes(&LABEL_E_EXP_MASTER),
        tx,
    )?;
    let sender_write_key_iv = derive_aead_key_iv(
        hash_algorithm,
        aead_algoorithm,
        &client_early_traffic_secret,
    )?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &Key) -> Result<MacKey, TLSError> {
    hkdf_expand_label(
        ha,
        k,
        bytes(&LABEL_FINISHED),
        &Bytes::new(),
        ha.hmac_tag_len(),
    )
}

/// Derive the handshake keys and master secret.
pub(crate) fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    shared_secret: &Key,
    psko: &Option<Psk>,
    transcript_hash: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, Key), TLSError> {
    let psk = if let Some(k) = psko {
        k.clone()
    } else {
        zero_key(ha)
    };
    let early_secret = hkdf_extract(ha, &psk, &zero_key(ha))?;
    let digest_emp = hash_empty(ha)?;
    let derived_secret = derive_secret(ha, &early_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let handshake_secret = hkdf_extract(ha, shared_secret, &derived_secret)?;
    let client_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        bytes(&LABEL_C_HS_TRAFFIC),
        transcript_hash,
    )?;
    let server_handshake_traffic_secret = derive_secret(
        ha,
        &handshake_secret,
        bytes(&LABEL_S_HS_TRAFFIC),
        transcript_hash,
    )?;
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    let master_secret_ = derive_secret(ha, &handshake_secret, bytes(&LABEL_DERIVED), &digest_emp)?;
    let master_secret = hkdf_extract(ha, &zero_key(ha), &master_secret_)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ))
}

/// Derive the application keys and master secret.
pub(crate) fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<(AeadKeyIV, AeadKeyIV, Key), TLSError> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&LABEL_C_AP_TRAFFIC), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&LABEL_S_AP_TRAFFIC), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, bytes(&LABEL_EXP_MASTER), tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub(crate) fn derive_rms(
    ha: &HashAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Result<Key, TLSError> {
    derive_secret(ha, master_secret, bytes(&LABEL_RES_MASTER), tx)
}

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_psk_skip_server_signature" below */

pub struct ClientPostClientHello(Random, Algorithms, KemSk, Option<Psk>, Transcript);
pub struct ClientPostServerHello(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ClientPostClientFinished(Random, Random, Algorithms, Key, Transcript);

pub fn algs_post_client_hello(st: &ClientPostClientHello) -> Algorithms {
    st.1
}
pub fn algs_post_server_hello(st: &ClientPostServerHello) -> Algorithms {
    st.2
}
pub fn algs_post_client_finished(st: &ClientPostClientFinished) -> Algorithms {
    st.2
}

/// Server state after processing the client hello.
pub struct ServerPostClientHello {
    client_randomness: Random,
    ciphersuite: Algorithms,
    session_id: Bytes,
    gx: Bytes,
    server: ServerInfo,
    transcript: Transcript,
}

/// Server state after generating the server hello.
pub struct ServerPostServerHello {
    client_random: Random,
    server_random: Random,
    ciphersuite: Algorithms,
    server: ServerInfo,
    master_secret: Key,
    cfk: MacKey,
    sfk: MacKey,
    transcript: Transcript,
}

pub struct ServerPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ServerPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ServerPostClientFinished(Random, Random, Algorithms, Key, Transcript);

/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript Digestes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

fn build_client_hello(
    ciphersuite: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    let tx = Transcript::new(ciphersuite.hash());
    let mut client_random = [0u8; 32];
    rng.fill_bytes(&mut client_random);
    let (kem_sk, kem_pk) = kem_keygen(ciphersuite.kem(), rng)?;
    let (client_hello, trunc_len) =
        client_hello(&ciphersuite, client_random.into(), &kem_pk, sn, &tkt)?;
    let (nch, cipher0, tx_ch) =
        compute_psk_binder_zero_rtt(ciphersuite, client_hello, trunc_len, &psk, tx)?;
    Ok((
        nch,
        cipher0,
        ClientPostClientHello(client_random.into(), ciphersuite, kem_sk, psk, tx_ch),
    ))
}

fn compute_psk_binder_zero_rtt(
    algs0: Algorithms,
    ch: HandshakeData,
    trunc_len: usize,
    psk: &Option<Psk>,
    tx: Transcript,
) -> Result<(HandshakeData, Option<ClientCipherState0>, Transcript), TLSError> {
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: _ks,
        psk_mode,
        zero_rtt,
    } = algs0;
    match (psk_mode, psk, trunc_len as u8) {
        (true, Some(k), _) => {
            let th_trunc = tx.transcript_hash_without_client_hello(&ch, trunc_len)?;
            let mk = derive_binder_key(&ha, k)?;
            let binder = hmac_tag(&ha, &mk, &th_trunc)?;
            let nch = set_client_hello_binder(&algs0, &Some(binder), ch, Some(trunc_len))?;
            let tx_ch = tx.add(&nch);
            if zero_rtt {
                let th = tx_ch.transcript_hash()?;
                let (aek, key) = derive_0rtt_keys(&ha, &ae, k, &th)?;
                let cipher0 = Some(client_cipher_state0(ae, aek, 0, key));
                Ok((nch, cipher0, tx_ch))
            } else {
                Ok((nch, None, tx_ch))
            }
        }
        (false, None, 0) => {
            let tx_ch = tx.add(&ch);
            Ok((ch, None, tx_ch))
        }
        _ => Err(PSK_MODE_MISMATCH),
    }
}

fn put_server_hello(
    handshake: &HandshakeData,
    state: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    let ClientPostClientHello(client_random, ciphersuite, sk, psk, tx) = state;

    let (sr, ct) = parse_server_hello(&ciphersuite, handshake)?;
    let tx = tx.add(handshake);
    let shared_secret = kem_decap(ciphersuite.kem, &ct, &sk)?;
    let th = tx.transcript_hash()?;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(
        &ciphersuite.hash,
        &ciphersuite.aead,
        &shared_secret,
        &psk,
        &th,
    )?;

    Ok((
        DuplexCipherStateH::new(chk, 0, shk, 0),
        ClientPostServerHello(client_random, sr, ciphersuite, ms, cfk, sfk, tx),
    ))
}

fn put_server_signature(
    encrypted_extensions: &HandshakeData,
    server_certificate: &HandshakeData,
    server_certificate_verify: &HandshakeData,
    handshake_state: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    let ClientPostServerHello(
        client_random,
        server_random,
        algorithms,
        master_secret,
        client_finished_key,
        server_finished_key,
        transcript,
    ) = handshake_state;
    if !algorithms.psk_mode() {
        parse_encrypted_extensions(&algorithms, encrypted_extensions)?;
        let transcript = transcript.add(encrypted_extensions);
        let certificate = parse_server_certificate(server_certificate)?;
        let transcript = transcript.add(server_certificate);
        let transcript_hash_server_certificate = transcript.transcript_hash()?;
        let spki = verification_key_from_cert(&certificate)?;
        let cert_pk = cert_public_key(&certificate, &spki)?;
        let cert_signature = parse_certificate_verify(&algorithms, server_certificate_verify)?;
        let sigval = (Bytes::from_slice(&PREFIX_SERVER_SIGNATURE))
            .concat(transcript_hash_server_certificate);
        verify(&algorithms.signature(), &cert_pk, &sigval, &cert_signature)?;
        let transcript = transcript.add(server_certificate_verify);
        Ok(ClientPostCertificateVerify(
            client_random,
            server_random,
            algorithms,
            master_secret,
            client_finished_key,
            server_finished_key,
            transcript,
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn put_psk_skip_server_signature(
    encrypted_extensions: &HandshakeData,
    handshake_state: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    let ClientPostServerHello(
        client_random,
        server_random,
        algorithms,
        master_secret,
        client_finished_key,
        server_finished_key,
        transcript,
    ) = handshake_state;
    if algorithms.psk_mode() {
        parse_encrypted_extensions(&algorithms, encrypted_extensions)?;
        let transcript = transcript.add(encrypted_extensions);
        Ok(ClientPostCertificateVerify(
            client_random,
            server_random,
            algorithms,
            master_secret,
            client_finished_key,
            server_finished_key,
            transcript,
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn put_server_finished(
    server_finished: &HandshakeData,
    handshake_state: ClientPostCertificateVerify,
) -> Result<(DuplexCipherState1, ClientPostServerFinished), TLSError> {
    let ClientPostCertificateVerify(
        client_random,
        server_random,
        algorithms,
        master_secret,
        client_finished_key,
        server_finished_key,
        transcript,
    ) = handshake_state;
    let Algorithms {
        hash,
        aead,
        signature,
        kem,
        psk_mode,
        zero_rtt,
    } = algorithms;
    let transcript_hash = transcript.transcript_hash()?;
    let verify_data = parse_finished(server_finished)?;
    hmac_verify(&hash, &server_finished_key, &transcript_hash, &verify_data)?;
    let transcript = transcript.add(server_finished);
    let transcript_hash_server_finished = transcript.transcript_hash()?;
    let (cak, sak, exp) = derive_app_keys(
        &hash,
        &aead,
        &master_secret,
        &transcript_hash_server_finished,
    )?;
    let cipher1 = duplex_cipher_state1(aead, cak, 0, sak, 0, exp);
    Ok((
        cipher1,
        ClientPostServerFinished(
            client_random,
            server_random,
            algorithms,
            master_secret,
            client_finished_key,
            transcript,
        ),
    ))
}

fn get_client_finished(
    handshake_state: ClientPostServerFinished,
) -> Result<(HandshakeData, ClientPostClientFinished), TLSError> {
    let ClientPostServerFinished(
        client_random,
        server_random,
        algorithms,
        master_secret,
        client_finished_key,
        transcript,
    ) = handshake_state;
    let transcript_hash = transcript.transcript_hash()?;
    let verify_data = hmac_tag(&algorithms.hash(), &client_finished_key, &transcript_hash)?;
    let client_finished = finished(&verify_data)?;
    let transcript = transcript.add(&client_finished);
    let transcript_hash = transcript.transcript_hash()?;
    let resumption_master_secret =
        derive_rms(&algorithms.hash(), &master_secret, &transcript_hash)?;
    Ok((
        client_finished,
        ClientPostClientFinished(
            client_random,
            server_random,
            algorithms,
            resumption_master_secret,
            transcript,
        ),
    ))
}

// Client-Side Handshake API: Usable by Quic and TLS
// client_init -> (encrypt_zerortt)* ->
// client_set_params -> (encrypt_handshake | decrypt_handshake)* ->
// client_finish -> (encrypt_data | decrypt_data)*

pub fn client_init(
    algs: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    build_client_hello(algs, sn, tkt, psk, rng)
}

/// Update the client state after generating the client hello message.
pub(crate) fn client_set_params(
    payload: &HandshakeData,
    st: ClientPostClientHello,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    put_server_hello(payload, st)
}

pub fn client_finish(
    payload: &HandshakeData,
    handshake_state: ClientPostServerHello,
) -> Result<(HandshakeData, DuplexCipherState1, ClientPostClientFinished), TLSError> {
    match algs_post_server_hello(&handshake_state).psk_mode() {
        false => {
            let (
                encrypted_extensions,
                server_certificate,
                server_certificate_verify,
                server_finished,
            ) = payload.to_four()?;
            let client_state_certificate_verify = put_server_signature(
                &encrypted_extensions,
                &server_certificate,
                &server_certificate_verify,
                handshake_state,
            )?;
            let (cipher, client_state_server_finished) =
                put_server_finished(&server_finished, client_state_certificate_verify)?;
            let (client_finished, client_state) =
                get_client_finished(client_state_server_finished)?;
            Ok((client_finished, cipher, client_state))
        }
        true => {
            let (encrypted_extensions, server_finished) = payload.to_two()?;
            let client_state_certificate_verify =
                put_psk_skip_server_signature(&encrypted_extensions, handshake_state)?;
            let (cipher, client_state_server_finished) =
                put_server_finished(&server_finished, client_state_certificate_verify)?;
            let (client_finished, client_state) =
                get_client_finished(client_state_server_finished)?;
            Ok((client_finished, cipher, client_state))
        }
    }
}

/* TLS 1.3 Server Side Handshake Functions */

fn put_client_hello(
    ciphersuite: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
) -> Result<(Option<ServerCipherState0>, ServerPostClientHello), TLSError> {
    let (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) =
        parse_client_hello(&ciphersuite, ch)?;
    let tx = Transcript::new(ciphersuite.hash());
    let th_trunc = tx.transcript_hash_without_client_hello(ch, trunc_len)?;
    let transcript = tx.add(ch);
    let th = transcript.transcript_hash()?;
    let server = lookup_db(ciphersuite, &db, &sni, &tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(ciphersuite, th, th_trunc, &server.psk_opt, bindero)?;
    Ok((
        cipher0,
        ServerPostClientHello {
            client_randomness,
            ciphersuite,
            session_id,
            gx,
            server,
            transcript,
        },
    ))
}

/// Process the PSK binder for 0-RTT
fn process_psk_binder_zero_rtt(
    ciphersuite: Algorithms,
    th_trunc: Digest,
    th: Digest,
    psko: &Option<Psk>,
    bindero: Option<Bytes>,
) -> Result<Option<ServerCipherState0>, TLSError> {
    match (ciphersuite.psk_mode, psko, bindero) {
        (true, Some(k), Some(binder)) => {
            let mk = derive_binder_key(&ciphersuite.hash, k)?;
            hmac_verify(&ciphersuite.hash, &mk, &th_trunc, &binder)?;
            if ciphersuite.zero_rtt {
                let (key_iv, early_exporter_ms) =
                    derive_0rtt_keys(&ciphersuite.hash, &ciphersuite.aead, k, &th)?;
                let cipher0 = Some(server_cipher_state0(key_iv, 0, early_exporter_ms));
                Ok(cipher0)
            } else {
                Ok(None)
            }
        }
        (false, None, None) => Ok(None),
        _ => Err(PSK_MODE_MISMATCH),
    }
}

fn get_server_hello(
    state: ServerPostClientHello,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(HandshakeData, DuplexCipherStateH, ServerPostServerHello), TLSError> {
    let mut server_random = [0u8; 32];
    rng.fill_bytes(&mut server_random);
    let (shared_secret, gy) = kem_encap(state.ciphersuite.kem, &state.gx, rng)?;
    let sh = server_hello(
        &state.ciphersuite,
        server_random.into(),
        &state.session_id,
        &gy,
    )?;
    let transcript = state.transcript.add(&sh);
    let transcript_hash = transcript.transcript_hash()?;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(
        &state.ciphersuite.hash,
        &state.ciphersuite.aead,
        &shared_secret,
        &state.server.psk_opt,
        &transcript_hash,
    )?;
    Ok((
        sh,
        DuplexCipherStateH::new(shk, 0, chk, 0),
        ServerPostServerHello {
            client_random: state.client_randomness,
            server_random: server_random.into(),
            ciphersuite: state.ciphersuite,
            server: state.server,
            master_secret: ms,
            cfk,
            sfk,
            transcript,
        },
    ))
}

fn get_server_signature(
    state: ServerPostServerHello,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        HandshakeData,
        HandshakeData,
        ServerPostCertificateVerify,
    ),
    TLSError,
> {
    let ee = encrypted_extensions(&state.ciphersuite)?;
    let transcript = state.transcript.add(&ee);
    if !state.ciphersuite.psk_mode() {
        let sc = server_certificate(&state.ciphersuite, &state.server.cert)?;
        let transcript = transcript.add(&sc);
        let transcript_hash = transcript.transcript_hash()?;
        let sigval = Bytes::from_slice(&PREFIX_SERVER_SIGNATURE).concat(transcript_hash);
        let sig = match state.ciphersuite.signature() {
            SignatureScheme::EcdsaSecp256r1Sha256 => sign(
                &state.ciphersuite.signature(),
                &state.server.sk,
                &sigval,
                rng,
            )?,
            SignatureScheme::RsaPssRsaSha256 => {
                // To avoid cyclic dependencies between the modules we pull out
                // the values from the RSA certificate here.
                // We could really read this from the key as well.
                let (cert_scheme, cert_slice) = verification_key_from_cert(&state.server.cert)?;
                let pk = rsa_public_key(&state.server.cert, cert_slice)?;
                sign_rsa(
                    &state.server.sk,
                    &pk.modulus,
                    &pk.exponent,
                    cert_scheme,
                    &sigval,
                    rng,
                )?
            }
            SignatureScheme::ED25519 => unimplemented!(),
        };
        let scv = certificate_verify(&state.ciphersuite, &sig)?;
        let transcript = transcript.add(&scv);
        Ok((
            ee,
            sc,
            scv,
            ServerPostCertificateVerify(
                state.client_random,
                state.server_random,
                state.ciphersuite,
                state.master_secret,
                state.cfk,
                state.sfk,
                transcript,
            ),
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_skip_server_signature(
    st: ServerPostServerHello,
) -> Result<(HandshakeData, ServerPostCertificateVerify), TLSError> {
    let ServerPostServerHello {
        client_random: cr,
        server_random: sr,
        ciphersuite: algs,
        server,
        master_secret: ms,
        cfk,
        sfk,
        transcript: tx,
    } = st;
    if algs.psk_mode() {
        let ee = encrypted_extensions(&algs)?;
        let tx = tx.add(&ee);
        Ok((
            ee,
            ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx),
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_server_finished(
    st: ServerPostCertificateVerify,
) -> Result<(HandshakeData, DuplexCipherState1, ServerPostServerFinished), TLSError> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx) = st;
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _sa,
        kem: _gn,
        psk_mode: _psk_mode,
        zero_rtt: _zero_rtt,
    } = algs;
    let th_scv = tx.transcript_hash()?;
    let vd = hmac_tag(&ha, &sfk, &th_scv)?;
    let sfin = finished(&vd)?;
    let tx = tx.add(&sfin);
    let th_sfin = tx.transcript_hash()?;
    let (cak, sak, exp) = derive_app_keys(&ha, &ae, &ms, &th_sfin)?;
    let cipher1 = duplex_cipher_state1(ae, sak, 0, cak, 0, exp);
    Ok((
        sfin,
        cipher1,
        ServerPostServerFinished(cr, sr, algs, ms, cfk, tx),
    ))
}

fn put_client_finished(
    cfin: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk, tx) = st;
    let th = tx.transcript_hash()?;
    let vd = parse_finished(cfin)?;
    hmac_verify(&algs.hash(), &cfk, &th, &vd)?;
    let tx = tx.add(cfin);
    let th = tx.transcript_hash()?;
    let rms = derive_rms(&algs.hash(), &ms, &th)?;
    Ok(ServerPostClientFinished(cr, sr, algs, rms, tx))
}

// Server-Side Handshake API: Usable by Quic and TLS
// server_init -> (decrypt_zerortt)* | (encrypt_handshake | decrypt_handshake)* ->
// server_finish -> (encrypt_data | decrypt_data)*

#[allow(clippy::type_complexity)]
pub fn server_init(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<
    (
        HandshakeData,
        HandshakeData,
        Option<ServerCipherState0>,
        DuplexCipherStateH,
        DuplexCipherState1,
        ServerPostServerFinished,
    ),
    TLSError,
> {
    let (cipher0, st) = put_client_hello(algs, ch, db)?;
    let (sh, cipher_hs, st) = get_server_hello(st, rng)?;
    match algs.psk_mode() {
        false => {
            let (ee, sc, scv, st) = get_server_signature(st, rng)?;
            let (sfin, cipher1, st) = get_server_finished(st)?;
            let flight = ee.concat(&sc).concat(&scv).concat(&sfin);
            Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
        }
        true => {
            let (ee, st) = get_skip_server_signature(st)?;
            let (sfin, cipher1, st) = get_server_finished(st)?;
            let flight = ee.concat(&sfin);
            Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
        }
    }
}

pub fn server_finish(
    cf: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    put_client_finished(cf, st)
}
