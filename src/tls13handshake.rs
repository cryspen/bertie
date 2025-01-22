use rand::{CryptoRng, RngCore};

use crate::{
    server::{lookup_db, ServerDB, ServerInfo},
    tls13cert::{cert_public_key, rsa_public_key, verification_key_from_cert},
    tls13crypto::{
        hmac_tag, hmac_verify, kem_decap, kem_encap, kem_keygen, sign, sign_rsa, verify,
        Algorithms, Digest, KemSk, Key, MacKey, Psk, Random, SignatureScheme,
    },
    tls13formats::{handshake_data::HandshakeData, *},
    tls13keyscheduler::{key_schedule::*, *},
    tls13record::*,
    tls13utils::*,
};

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_psk_skip_server_signature" below */

pub struct ClientPostClientHello(Random, Algorithms, KemSk, Option<Psk>, Transcript);
pub struct ClientPostServerHello(
    Random,
    Random,
    Algorithms,
    TagKey,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ClientPostCertificateVerify(
    Random,
    Random,
    Algorithms,
    TagKey,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ClientPostServerFinished(Random, Random, Algorithms, TagKey, MacKey, Transcript);
// We do not use most of this state, but we keep the unused parts for verification purposes.
#[allow(dead_code)]
pub struct ClientPostClientFinished(Random, Random, Algorithms, TagKey, Transcript);

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
    master_secret: TagKey,
    cfk: MacKey,
    sfk: MacKey,
    transcript: Transcript,
}

pub struct ServerPostCertificateVerify(
    Random,
    Random,
    Algorithms,
    TagKey,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ServerPostServerFinished(Random, Random, Algorithms, TagKey, MacKey, Transcript);
// We do not use most of this state, but we keep the unsused parts for verification purposes.
#[allow(dead_code)]
pub struct ServerPostClientFinished(Random, Random, Algorithms, TagKey, Transcript);

/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript Digestes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

fn build_client_hello(
    ciphersuite: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut (impl CryptoRng + RngCore),
    ks: &mut TLSkeyscheduler,
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
        compute_psk_binder_zero_rtt(ciphersuite, client_hello, trunc_len, &psk, tx, ks)?;
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
    ks: &mut TLSkeyscheduler,
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
            let psk_key = TagKey {
                alg: ha,
                tag: TLSnames::PSK,
                val: k.clone(),
            };
            let th_trunc = tx.transcript_hash_without_client_hello(&ch, trunc_len)?;
            let mk = derive_binder_key(&ha, &psk_key, ks)?;
            let binder =
                xpd(
                    &TagKey {
                        alg: ha,
                        val: mk,
                        tag: TLSnames::Bind,
                    },
                    vec![].into(),
                    &th_trunc,
                )?
            .val;
            let nch = set_client_hello_binder(&algs0, &Some(binder), ch, Some(trunc_len))?;
            let tx_ch = tx.add(&nch);
            if zero_rtt {
                let th = tx_ch.transcript_hash()?;
                let (aek, key) = derive_0rtt_keys(&ha, &ae, &psk_key, &th, ks)?;
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
        &TagKey {
            alg: ciphersuite.hash,
            tag: TLSnames::KEM,
            val: shared_secret,
        },
        &psk.map(|x| TagKey {
            alg: ciphersuite.hash,
            tag: TLSnames::PSK,
            val: x,
        }),
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
    ks: &mut TLSkeyscheduler,
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    build_client_hello(algs, sn, tkt, psk, rng, ks)
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
    ks: &mut TLSkeyscheduler,
) -> Result<(Option<ServerCipherState0>, ServerPostClientHello), TLSError> {
    let (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) =
        parse_client_hello(&ciphersuite, ch)?;
    let tx = Transcript::new(ciphersuite.hash());
    let th_trunc = tx.transcript_hash_without_client_hello(ch, trunc_len)?;
    let transcript = tx.add(ch);
    let th = transcript.transcript_hash()?;
    let server = lookup_db(ciphersuite, &db, &sni, &tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(ciphersuite, th_trunc, th, &server.psk_opt, bindero, ks)?;
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
    ks: &mut TLSkeyscheduler,
) -> Result<Option<ServerCipherState0>, TLSError> {
    match (ciphersuite.psk_mode, psko, bindero) {
        (true, Some(k), Some(binder)) => {
            let psk_key = TagKey {
                alg: ciphersuite.hash,
                tag: TLSnames::PSK,
                val: k.clone(),
            };
            let mk = derive_binder_key(&ciphersuite.hash, &psk_key, ks)?;
            hmac_verify(&ciphersuite.hash, &mk, &th_trunc, &binder)?;
            if ciphersuite.zero_rtt {
                let (key_iv, early_exporter_ms) =
                    derive_0rtt_keys(&ciphersuite.hash, &ciphersuite.aead, &psk_key, &th, ks)?;
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
        &TagKey {
            alg: state.ciphersuite.hash,
            tag: TLSnames::KEM,
            val: shared_secret,
        },
        &state.server.psk_opt.clone().map(|x| TagKey {
            alg: state.ciphersuite.hash,
            tag: TLSnames::PSK,
            val: x,
        }),
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

fn get_rsa_signature(
    cert: &Bytes,
    sk: &Bytes,
    sigval: &Bytes,
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Bytes, TLSError> {
    // To avoid cyclic dependencies between the modules we pull out
    // the values from the RSA certificate here.
    // We could really read this from the key as well.
    let (cert_scheme, cert_slice) = verification_key_from_cert(cert)?;
    let pk = rsa_public_key(cert, cert_slice)?;
    sign_rsa(sk, &pk.modulus, &pk.exponent, cert_scheme, sigval, rng)
}

fn get_server_signature_no_psk(
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
    let sc = server_certificate(&state.ciphersuite, &state.server.cert)?;
    let transcript = transcript.add(&sc);
    let transcript_hash = transcript.transcript_hash()?;
    let sigval = Bytes::from_slice(&PREFIX_SERVER_SIGNATURE).concat(transcript_hash);
    let sig = (match state.ciphersuite.signature() {
        SignatureScheme::EcdsaSecp256r1Sha256 => sign(
            &state.ciphersuite.signature(),
            &state.server.sk,
            &sigval,
            rng,
        ),
        SignatureScheme::RsaPssRsaSha256 => {
            get_rsa_signature(&state.server.cert, &state.server.sk, &sigval, rng)
        }
        SignatureScheme::ED25519 => Err(UNSUPPORTED_ALGORITHM),
    })?;
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
    if !state.ciphersuite.psk_mode() {
        get_server_signature_no_psk(state, rng)
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_skip_server_signature_no_psk(
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
    let ee = encrypted_extensions(&algs)?;
    let tx = tx.add(&ee);
    Ok((
        ee,
        ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx),
    ))
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
    } = &st;
    if algs.psk_mode() {
        get_skip_server_signature_no_psk(st)
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
pub fn server_init_no_psk(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut (impl CryptoRng + RngCore),
    ks: &mut TLSkeyscheduler,
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
    let (cipher0, st) = put_client_hello(algs, ch, db, ks)?;
    let (sh, cipher_hs, st) = get_server_hello(st, rng)?;

    let (ee, sc, scv, st) = get_server_signature(st, rng)?;
    let (sfin, cipher1, st) = get_server_finished(st)?;
    let flight = ee.concat(&sc).concat(&scv).concat(&sfin);
    Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
}

#[allow(clippy::type_complexity)]
pub fn server_init_psk(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut (impl CryptoRng + RngCore),
    ks: &mut TLSkeyscheduler,
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
    let (cipher0, st) = put_client_hello(algs, ch, db, ks)?;
    let (sh, cipher_hs, st) = get_server_hello(st, rng)?;

    let (ee, st) = get_skip_server_signature(st)?;
    let (sfin, cipher1, st) = get_server_finished(st)?;
    let flight = ee.concat(&sfin);
    Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
}

#[allow(clippy::type_complexity)]
pub fn server_init(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut (impl CryptoRng + RngCore),
    ks: &mut TLSkeyscheduler,
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
    match algs.psk_mode() {
        false => server_init_no_psk(algs, ch, db, rng, ks),
        true => server_init_psk(algs, ch, db, rng, ks),
    }
}

pub fn server_finish(
    cf: &HandshakeData,
    st: ServerPostServerFinished,
) -> Result<ServerPostClientFinished, TLSError> {
    put_client_finished(cf, st)
}
