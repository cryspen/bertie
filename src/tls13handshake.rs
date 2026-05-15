use rand::CryptoRng;

use crate::{
    crypto_provider::BertieCrypto,
    server::{lookup_db, ServerDB, ServerInfo, ServerPubInfo},
    tls13cert::{cert_public_key, rsa_public_key, verification_key_from_cert},
    tls13crypto::{
        Algorithms, Digest, KemSk, MacKey, Psk, Random, SignatureScheme,
    },
    tls13formats::{handshake_data::HandshakeData, *},
    tls13keyscheduler::{
        key_schedule::{TLSnames::*, *},
        *,
    },
    tls13record::*,
    tls13utils::*,
};

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS. */

pub struct ClientPostClientHello(
    Random,
    Algorithms,
    ServerPubInfo,
    KemSk,
    Option<Psk>,
    Transcript,
);
pub struct ClientPostServerHello(
    Random,
    Random,
    Algorithms,
    ServerPubInfo,
    Handle,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ClientPostCertificateVerify(
    Random,
    Random,
    Algorithms,
    ServerPubInfo,
    Handle,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ClientPostServerFinished(
    Random,
    Random,
    Algorithms,
    ServerPubInfo,
    Handle,
    MacKey,
    Transcript,
);
#[allow(dead_code)]
pub struct ClientPostClientFinished(
    Random,
    Random,
    Algorithms,
    ServerPubInfo,
    Handle,
    Transcript,
);

pub fn algs_post_client_hello(st: &ClientPostClientHello) -> Algorithms {
    st.1
}
pub fn algs_post_server_hello(st: &ClientPostServerHello) -> Algorithms {
    st.2
}
pub fn algs_post_client_finished(st: &ClientPostClientFinished) -> Algorithms {
    st.2
}

pub fn server_info_post_client_hello(st: &ClientPostClientHello) -> ServerPubInfo {
    st.2.clone()
}
pub fn server_info_post_server_hello(st: &ClientPostServerHello) -> ServerPubInfo {
    st.3.clone()
}
pub fn server_info_post_client_finished(st: &ClientPostClientFinished) -> ServerPubInfo {
    st.3.clone()
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
    master_secret: Handle,
    cfk: MacKey,
    sfk: MacKey,
    transcript: Transcript,
}

pub struct ServerPostCertificateVerify(
    Random,
    Random,
    Algorithms,
    Handle,
    MacKey,
    MacKey,
    Transcript,
);
pub struct ServerPostServerFinished(Random, Random, Algorithms, Handle, MacKey, Transcript);
#[allow(dead_code)]
pub struct ServerPostClientFinished(Random, Random, Algorithms, Handle, Transcript);

/* TLS 1.3 Client Side Handshake Functions */

fn build_client_hello<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    ciphersuite: Algorithms,
    server_name: &Bytes,
    session_ticket: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut R,
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
    let (kem_sk, kem_pk) = crypto.kem_keygen(ciphersuite.kem(), rng)?;
    let (client_hello, trunc_len) = client_hello(
        &ciphersuite,
        bytes(&client_random),
        &kem_pk,
        server_name,
        &session_ticket,
    )?;
    let (nch, cipher0, tx_ch) =
        compute_psk_binder_zero_rtt(crypto, ciphersuite, client_hello, trunc_len, &psk, tx, ks)?;
    Ok((
        nch,
        cipher0,
        ClientPostClientHello(
            client_random.into(),
            ciphersuite,
            ServerPubInfo {
                server_name: server_name.clone(),
                certificate: None,
                public_key: None,
                session_ticket,
            },
            kem_sk,
            psk,
            tx_ch,
        ),
    ))
}

#[hax_lib::requires(trunc_len <= ch.len())]
fn compute_psk_binder_zero_rtt<C: BertieCrypto>(
    crypto: &C,
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
            let psk_handle = Handle {
                name: PSK,
                alg: ha,
                level: 0,
            };
            set_by_handle(ks, &psk_handle, k.clone());

            let th_trunc = tx.transcript_hash_without_client_hello(crypto, &ch, trunc_len)?;
            let mk_handle = derive_binder_key(crypto, &ha, &psk_handle, ks)?;

            let binder_handle = XPD(crypto, ks, Binder, 0, &mk_handle, true, &th_trunc)?;
            let binder = tagkey_from_handle(ks, &binder_handle)?.val;

            let nch = set_client_hello_binder(&algs0, &Some(binder), ch, Some(trunc_len))?;
            let tx_ch = tx.add(&nch);
            if zero_rtt {
                let th = tx_ch.transcript_hash(crypto)?;
                let (aek, handle) = derive_0rtt_keys(crypto, &ha, &ae, &psk_handle, &th, ks)?;
                let key = tagkey_from_handle(ks, &handle)?;
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

fn put_server_hello<C: BertieCrypto>(
    crypto: &C,
    handshake: &HandshakeData,
    state: ClientPostClientHello,
    ks: &mut TLSkeyscheduler,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    let ClientPostClientHello(client_random, ciphersuite, server_info, sk, psk, tx) = state;

    let (sr, ct) = parse_server_hello(&ciphersuite, handshake)?;
    let tx = tx.add(handshake);
    let shared_secret = crypto.kem_decap(ciphersuite.kem, &ct, &sk)?;
    let th = tx.transcript_hash(crypto)?;

    let shared_secret_handle = Handle {
        name: KEM,
        alg: ciphersuite.hash,
        level: 0,
    };
    set_by_handle(ks, &shared_secret_handle, shared_secret);

    let psk_handle = match psk {
        Some(bytes) => {
            let handle = Handle {
                name: PSK,
                alg: ciphersuite.hash,
                level: 0,
            };
            set_by_handle(ks, &handle, bytes);
            Some(handle)
        }
        None => None,
    };

    let (ch_handle, sh_handle, ms_handle) = derive_hk_handles(
        crypto,
        &ciphersuite.hash,
        &shared_secret_handle,
        &psk_handle,
        &th,
        ks,
    )?;

    let (chk, shk, cfk, sfk) = derive_hk_ms(
        crypto,
        &ciphersuite.hash,
        &ciphersuite.aead,
        &ch_handle,
        &sh_handle,
        ks,
    )?;

    Ok((
        DuplexCipherStateH::new(chk, 0, shk, 0),
        ClientPostServerHello(
            client_random,
            sr,
            ciphersuite,
            server_info,
            ms_handle,
            cfk,
            sfk,
            tx,
        ),
    ))
}

fn put_server_signature<C: BertieCrypto>(
    crypto: &C,
    encrypted_extensions: &HandshakeData,
    server_certificate: &HandshakeData,
    server_certificate_verify: &HandshakeData,
    handshake_state: ClientPostServerHello,
) -> Result<ClientPostCertificateVerify, TLSError> {
    let ClientPostServerHello(
        client_random,
        server_random,
        algorithms,
        server_info,
        master_secret_handle,
        client_finished_key,
        server_finished_key,
        transcript,
    ) = handshake_state;
    if !algorithms.psk_mode() {
        parse_encrypted_extensions(&algorithms, encrypted_extensions)?;
        let transcript = transcript.add(encrypted_extensions);
        let certificate = parse_server_certificate(server_certificate)?;
        let transcript = transcript.add(server_certificate);
        let transcript_hash_server_certificate = transcript.transcript_hash(crypto)?;
        let spki = verification_key_from_cert(&certificate)?;
        let public_key = cert_public_key(&certificate, &spki)?;
        let cert_signature = parse_certificate_verify(&algorithms, server_certificate_verify)?;
        let sigval = (Bytes::from_slice(&PREFIX_SERVER_SIGNATURE))
            .concat(transcript_hash_server_certificate);
        crypto.verify(
            &algorithms.signature(),
            &public_key,
            &sigval,
            &cert_signature,
        )?;
        let transcript = transcript.add(server_certificate_verify);
        Ok(ClientPostCertificateVerify(
            client_random,
            server_random,
            algorithms,
            ServerPubInfo {
                server_name: server_info.server_name,
                certificate: Some(certificate),
                public_key: Some(public_key),
                session_ticket: server_info.session_ticket,
            },
            master_secret_handle,
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
        server_info,
        master_secret_handle,
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
            server_info,
            master_secret_handle,
            client_finished_key,
            server_finished_key,
            transcript,
        ))
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn put_server_finished<C: BertieCrypto>(
    crypto: &C,
    server_finished: &HandshakeData,
    handshake_state: ClientPostCertificateVerify,
    ks: &mut TLSkeyscheduler,
) -> Result<(DuplexCipherState1, ClientPostServerFinished), TLSError> {
    let ClientPostCertificateVerify(
        client_random,
        server_random,
        algorithms,
        server_info,
        master_secret_handle,
        client_finished_key,
        server_finished_key,
        transcript,
    ) = handshake_state;
    let Algorithms {
        hash,
        aead,
        signature: _,
        kem: _,
        psk_mode: _,
        zero_rtt: _,
    } = algorithms;
    let transcript_hash = transcript.transcript_hash(crypto)?;
    let verify_data = parse_finished(server_finished)?;
    crypto.hmac_verify(&hash, &server_finished_key, &transcript_hash, &verify_data)?;
    let transcript = transcript.add(server_finished);
    let transcript_hash_server_finished = transcript.transcript_hash(crypto)?;
    let (ca_handle, sa_handle, exp_handle) = derive_app_handles(
        crypto,
        &hash,
        &master_secret_handle,
        &transcript_hash_server_finished,
        ks,
    )?;
    let (cak, sak) = derive_app_keys(crypto, &hash, &aead, &ca_handle, &sa_handle, ks)?;
    let exp = tagkey_from_handle(ks, &exp_handle)?;

    let cipher1 = duplex_cipher_state1(aead, cak, 0, sak, 0, exp);
    Ok((
        cipher1,
        ClientPostServerFinished(
            client_random,
            server_random,
            algorithms,
            server_info,
            master_secret_handle,
            client_finished_key,
            transcript,
        ),
    ))
}

fn get_client_finished<C: BertieCrypto>(
    crypto: &C,
    handshake_state: ClientPostServerFinished,
    ks: &mut TLSkeyscheduler,
) -> Result<(HandshakeData, ClientPostClientFinished), TLSError> {
    let ClientPostServerFinished(
        client_random,
        server_random,
        algorithms,
        server_info,
        master_secret_handle,
        client_finished_key,
        transcript,
    ) = handshake_state;
    let transcript_hash = transcript.transcript_hash(crypto)?;
    let verify_data = crypto.hmac_tag(&algorithms.hash(), &client_finished_key, &transcript_hash)?;
    let client_finished = finished(&verify_data)?;
    let transcript = transcript.add(&client_finished);
    let transcript_hash = transcript.transcript_hash(crypto)?;
    let resumption_master_secret = derive_rms(
        crypto,
        &algorithms.hash(),
        &master_secret_handle,
        &transcript_hash,
        ks,
    )?;
    Ok((
        client_finished,
        ClientPostClientFinished(
            client_random,
            server_random,
            algorithms,
            server_info,
            resumption_master_secret,
            transcript,
        ),
    ))
}

// Client-Side Handshake API.

pub fn client_init<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    algs: Algorithms,
    sn: &Bytes,
    tkt: Option<Bytes>,
    psk: Option<Psk>,
    rng: &mut R,
    ks: &mut TLSkeyscheduler,
) -> Result<
    (
        HandshakeData,
        Option<ClientCipherState0>,
        ClientPostClientHello,
    ),
    TLSError,
> {
    build_client_hello(crypto, algs, sn, tkt, psk, rng, ks)
}

pub(crate) fn client_set_params<C: BertieCrypto>(
    crypto: &C,
    payload: &HandshakeData,
    st: ClientPostClientHello,
    ks: &mut TLSkeyscheduler,
) -> Result<(DuplexCipherStateH, ClientPostServerHello), TLSError> {
    put_server_hello(crypto, payload, st, ks)
}

pub fn client_finish<C: BertieCrypto>(
    crypto: &C,
    payload: &HandshakeData,
    handshake_state: ClientPostServerHello,
    ks: &mut TLSkeyscheduler,
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
                crypto,
                &encrypted_extensions,
                &server_certificate,
                &server_certificate_verify,
                handshake_state,
            )?;
            let (cipher, client_state_server_finished) = put_server_finished(
                crypto,
                &server_finished,
                client_state_certificate_verify,
                ks,
            )?;
            let (client_finished, client_state) =
                get_client_finished(crypto, client_state_server_finished, ks)?;
            Ok((client_finished, cipher, client_state))
        }
        true => {
            let (encrypted_extensions, server_finished) = payload.to_two()?;
            let client_state_certificate_verify =
                put_psk_skip_server_signature(&encrypted_extensions, handshake_state)?;
            let (cipher, client_state_server_finished) = put_server_finished(
                crypto,
                &server_finished,
                client_state_certificate_verify,
                ks,
            )?;
            let (client_finished, client_state) =
                get_client_finished(crypto, client_state_server_finished, ks)?;
            Ok((client_finished, cipher, client_state))
        }
    }
}

/* TLS 1.3 Server Side Handshake Functions */

fn put_client_hello<C: BertieCrypto>(
    crypto: &C,
    ciphersuite: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    ks: &mut TLSkeyscheduler,
) -> Result<(Option<ServerCipherState0>, ServerPostClientHello), TLSError> {
    let (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) =
        parse_client_hello(&ciphersuite, ch)?;
    let tx = Transcript::new(ciphersuite.hash());
    let th_trunc = tx.transcript_hash_without_client_hello(crypto, ch, trunc_len)?;
    let transcript = tx.add(ch);
    let th = transcript.transcript_hash(crypto)?;
    let server = lookup_db(ciphersuite, &db, &sni, &tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(
        crypto,
        ciphersuite,
        th_trunc,
        th,
        &server.psk_opt,
        bindero,
        ks,
    )?;
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
fn process_psk_binder_zero_rtt<C: BertieCrypto>(
    crypto: &C,
    ciphersuite: Algorithms,
    th_trunc: Digest,
    th: Digest,
    psko: &Option<Psk>,
    bindero: Option<Bytes>,
    ks: &mut TLSkeyscheduler,
) -> Result<Option<ServerCipherState0>, TLSError> {
    match (ciphersuite.psk_mode, psko, bindero) {
        (true, Some(k), Some(binder_in)) => {
            let _ = binder_in;
            let psk_handle = Handle {
                name: PSK,
                alg: ciphersuite.hash,
                level: 0,
            };
            set_by_handle(ks, &psk_handle, k.clone());

            let mk_handle = derive_binder_key(crypto, &ciphersuite.hash, &psk_handle, ks)?;
            let mk = tagkey_from_handle(ks, &mk_handle)?.val;

            let binder_handle = XPD(crypto, ks, Binder, 0, &mk_handle, true, &th_trunc)?;
            let binder = tagkey_from_handle(ks, &binder_handle)?.val;

            crypto.hmac_verify(&ciphersuite.hash, &mk, &th_trunc, &binder)?;
            if ciphersuite.zero_rtt {
                let (key_iv, early_exporter_ms_handle) = derive_0rtt_keys(
                    crypto,
                    &ciphersuite.hash,
                    &ciphersuite.aead,
                    &psk_handle,
                    &th,
                    ks,
                )?;
                let early_exporter_ms = tagkey_from_handle(ks, &early_exporter_ms_handle)?;
                Ok(Some(server_cipher_state0(key_iv, 0, early_exporter_ms)))
            } else {
                Ok(None)
            }
        }
        (false, None, None) => Ok(None),
        _ => Err(PSK_MODE_MISMATCH),
    }
}

fn get_server_hello<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    state: ServerPostClientHello,
    rng: &mut R,
    ks: &mut TLSkeyscheduler,
) -> Result<(HandshakeData, DuplexCipherStateH, ServerPostServerHello), TLSError> {
    let mut server_random = [0u8; 32];
    rng.fill_bytes(&mut server_random);
    let (shared_secret, gy) = crypto.kem_encap(state.ciphersuite.kem, &state.gx, rng)?;

    let shared_secret_handle = Handle {
        name: KEM,
        alg: state.ciphersuite.hash,
        level: 0,
    };
    set_by_handle(ks, &shared_secret_handle, shared_secret);

    let sh = server_hello(
        &state.ciphersuite,
        bytes(&server_random),
        &state.session_id,
        &gy,
    )?;
    let transcript = state.transcript.add(&sh);
    let transcript_hash = transcript.transcript_hash(crypto)?;

    let psk_handle = state.server.psk_opt.clone();
    let psk_handle = match psk_handle {
        Some(bytes) => {
            let handle = Handle {
                name: PSK,
                alg: state.ciphersuite.hash,
                level: 0,
            };
            set_by_handle(ks, &handle, bytes);
            Some(handle)
        }
        None => None,
    };

    let (ch_handle, sh_handle, ms_handle) = derive_hk_handles(
        crypto,
        &state.ciphersuite.hash,
        &shared_secret_handle,
        &psk_handle,
        &transcript_hash,
        ks,
    )?;

    let (chk, shk, cfk, sfk) = derive_hk_ms(
        crypto,
        &state.ciphersuite.hash,
        &state.ciphersuite.aead,
        &ch_handle,
        &sh_handle,
        ks,
    )?;
    Ok((
        sh,
        DuplexCipherStateH::new(shk, 0, chk, 0),
        ServerPostServerHello {
            client_random: state.client_randomness,
            server_random: server_random.into(),
            ciphersuite: state.ciphersuite,
            server: state.server,
            master_secret: ms_handle,
            cfk,
            sfk,
            transcript,
        },
    ))
}

fn get_rsa_signature<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    cert: &Bytes,
    sk: &Bytes,
    sigval: &Bytes,
    rng: &mut R,
) -> Result<Bytes, TLSError> {
    let (cert_scheme, cert_slice) = verification_key_from_cert(cert)?;
    let pk = rsa_public_key(cert, cert_slice)?;
    crypto.sign_rsa(sk, &pk.modulus, &pk.exponent, cert_scheme, sigval, rng)
}

fn get_server_signature_no_psk<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    state: ServerPostServerHello,
    rng: &mut R,
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
    let transcript_hash = transcript.transcript_hash(crypto)?;
    let sigval = Bytes::from_slice(&PREFIX_SERVER_SIGNATURE).concat(transcript_hash);
    let sig = (match state.ciphersuite.signature() {
        SignatureScheme::EcdsaSecp256r1Sha256 => crypto.sign(
            &state.ciphersuite.signature(),
            &state.server.sk,
            &sigval,
            rng,
        ),
        SignatureScheme::RsaPssRsaSha256 => {
            get_rsa_signature(crypto, &state.server.cert, &state.server.sk, &sigval, rng)
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

fn get_server_signature<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    state: ServerPostServerHello,
    rng: &mut R,
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
        get_server_signature_no_psk(crypto, state, rng)
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
        server: _,
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
    if st.ciphersuite.psk_mode() {
        get_skip_server_signature_no_psk(st)
    } else {
        Err(PSK_MODE_MISMATCH)
    }
}

fn get_server_finished<C: BertieCrypto>(
    crypto: &C,
    st: ServerPostCertificateVerify,
    ks: &mut TLSkeyscheduler,
) -> Result<(HandshakeData, DuplexCipherState1, ServerPostServerFinished), TLSError> {
    let ServerPostCertificateVerify(cr, sr, algs, ms_handle, cfk, sfk, tx) = st;
    let Algorithms {
        hash: ha,
        aead: ae,
        signature: _,
        kem: _,
        psk_mode: _,
        zero_rtt: _,
    } = algs;
    let th_scv = tx.transcript_hash(crypto)?;
    let vd = crypto.hmac_tag(&ha, &sfk, &th_scv)?;
    let sfin = finished(&vd)?;
    let tx = tx.add(&sfin);
    let th_sfin = tx.transcript_hash(crypto)?;
    let (ca_handle, sa_handle, exp_handle) =
        derive_app_handles(crypto, &ha, &ms_handle, &th_sfin, ks)?;
    let (cak, sak) = derive_app_keys(crypto, &ha, &ae, &ca_handle, &sa_handle, ks)?;
    let exp = tagkey_from_handle(ks, &exp_handle)?;
    let cipher1 = duplex_cipher_state1(ae, sak, 0, cak, 0, exp);
    Ok((
        sfin,
        cipher1,
        ServerPostServerFinished(cr, sr, algs, ms_handle, cfk, tx),
    ))
}

fn put_client_finished<C: BertieCrypto>(
    crypto: &C,
    cfin: &HandshakeData,
    st: ServerPostServerFinished,
    ks: &mut TLSkeyscheduler,
) -> Result<ServerPostClientFinished, TLSError> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk, tx) = st;
    let th = tx.transcript_hash(crypto)?;
    let vd = parse_finished(cfin)?;
    crypto.hmac_verify(&algs.hash(), &cfk, &th, &vd)?;
    let tx = tx.add(cfin);
    let th = tx.transcript_hash(crypto)?;
    let rms = derive_rms(crypto, &algs.hash(), &ms, &th, ks)?;
    Ok(ServerPostClientFinished(cr, sr, algs, rms, tx))
}

// Server-Side Handshake API.

#[allow(clippy::type_complexity)]
pub fn server_init_no_psk<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut R,
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
    let (cipher0, st) = put_client_hello(crypto, algs, ch, db, ks)?;
    let (sh, cipher_hs, st) = get_server_hello(crypto, st, rng, ks)?;

    let (ee, sc, scv, st) = get_server_signature(crypto, st, rng)?;
    let (sfin, cipher1, st) = get_server_finished(crypto, st, ks)?;
    let flight = ee.concat(&sc).concat(&scv).concat(&sfin);
    Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
}

#[allow(clippy::type_complexity)]
pub fn server_init_psk<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut R,
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
    let (cipher0, st) = put_client_hello(crypto, algs, ch, db, ks)?;
    let (sh, cipher_hs, st) = get_server_hello(crypto, st, rng, ks)?;

    let (ee, st) = get_skip_server_signature(st)?;
    let (sfin, cipher1, st) = get_server_finished(crypto, st, ks)?;
    let flight = ee.concat(&sfin);

    Ok((sh, flight, cipher0, cipher_hs, cipher1, st))
}

#[allow(clippy::type_complexity)]
pub fn server_init<C: BertieCrypto, R: CryptoRng>(
    crypto: &C,
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
    rng: &mut R,
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
        false => server_init_no_psk(crypto, algs, ch, db, rng, ks),
        true => server_init_psk(crypto, algs, ch, db, rng, ks),
    }
}

pub fn server_finish<C: BertieCrypto>(
    crypto: &C,
    cf: &HandshakeData,
    st: ServerPostServerFinished,
    ks: &mut TLSkeyscheduler,
) -> Result<ServerPostClientFinished, TLSError> {
    put_client_finished(crypto, cf, st, ks)
}

#[cfg(feature = "hax-pv")]
mod proverif_extra {
    use crate::tls13utils::Bytes;

    #[hax_lib::proverif::replace("")]
    fn f() {
        let _b = Bytes::new();
    }
}
