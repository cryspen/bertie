// Import hacspec and all needed definitions.
use hacspec_lib::*;
use hacspec_cryptolib::*;
use crate::tls13utils::*;
use crate::tls13formats::*;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

pub fn hash_empty(ha: &HashAlgorithm) -> Res<Digest> {
    match hash(ha, &empty()) {
        Ok(h) => Res::<Digest>::Ok(h),
        Err(_) => Res::<Digest>::Err(crypto_error),
    }
    //Ok(HASH::from_seq(&sha256_empty))
}
pub fn hkdf_expand_label(
    ha: &HashAlgorithm,
    k: &Key,
    label: &Bytes,
    context: &Bytes,
    len: usize,
    ) -> Res<Key> {
    if len >= 65536 {
        Err(payload_too_long)
    } else {
        let lenb = bytes(&U16_to_be_bytes(U16(len as u16)));
        let tls13_label = label_tls13.concat(label);
        let info = lenb
            .concat(&lbytes1(&tls13_label)?)
            .concat(&lbytes1(context)?);
        match hkdf_expand(&ha, k, &info, len as usize) {
            Ok(k) => Res::<Key>::Ok(k),
            Err(_) => Res::<Key>::Err(crypto_error),
        }
    }
}

pub fn derive_secret(ha: &HashAlgorithm, k: &Key, label: &Bytes, tx: &Digest) -> Res<Key> {
    hkdf_expand_label(ha, k, label, &bytes(tx), hash_len(ha))
}

pub fn derive_binder_key(ha: &HashAlgorithm, k: &Key) -> Res<MacKey> {
    let early_secret = hkdf_extract(&ha, k, &zero_key(ha))?;
    let mk = derive_secret(
        ha,
        &early_secret,
        &bytes(&label_res_binder),
        &hash_empty(ha)?,
    )?;
    Ok(MacKey::from_seq(&mk))
}

pub fn derive_aead_key_iv(ha: &HashAlgorithm, ae: &AeadAlgorithm, k: &Key) -> Res<AeadKeyIV> {
    let sender_write_key = hkdf_expand_label(ha, k, &bytes(&label_key), &empty(), ae_key_len(ae))?;
    let sender_write_iv = hkdf_expand_label(ha, k, &bytes(&label_iv), &empty(), ae_iv_len(ae))?;
    Ok((
        AeadKey::from_seq(&sender_write_key),
        AeadIv::from_seq(&sender_write_iv),
    ))
}

pub fn derive_0rtt_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    k: &Key,
    tx: &Digest,
) -> Res<(AeadKeyIV, Key)> {
    let early_secret = hkdf_extract(&ha, k, &zero_key(ha))?;
    let client_early_traffic_secret =
        derive_secret(ha, &early_secret, &bytes(&label_c_e_traffic), tx)?;
    let early_exporter_master_secret =
        derive_secret(ha, &early_secret, &bytes(&label_c_e_traffic), tx)?;
    let sender_write_key_iv = derive_aead_key_iv(ha, ae, &client_early_traffic_secret)?;
    Ok((sender_write_key_iv, early_exporter_master_secret))
}

pub fn derive_finished_key(ha: &HashAlgorithm, k: &Key) -> Res<MacKey> {
    Ok(hkdf_expand_label(
        ha,
        k,
        &bytes(&label_finished),
        &empty(),
        hmac_tag_len(ha),
    )?)
}

pub fn derive_hk_ms(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    gxy: &Key,
    psko: &Option<PSK>,
    tx: &Digest,
) -> Res<(AeadKeyIV, AeadKeyIV, MacKey, MacKey, Key)> {
    let psk = if let Some(k) = psko {
        Key::from_seq(k)
    } else {
        zero_key(ha)
    };
    let early_secret = hkdf_extract(&ha, &psk, &zero_key(ha))?;
    let Digest_emp = hash_empty(ha)?;
    let derived_secret = derive_secret(ha, &early_secret, &bytes(&label_derived), &Digest_emp)?;
    //    println!("derived secret: {}", derived_secret.to_hex());
    let handshake_secret = hkdf_extract(&ha, gxy, &derived_secret)?;
    //    println!("handshake secret: {}", handshake_secret.to_hex());
    let client_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &bytes(&label_c_hs_traffic), tx)?;
    //    println!("c h ts: {}", client_handshake_traffic_secret.to_hex());
    let server_handshake_traffic_secret =
        derive_secret(ha, &handshake_secret, &bytes(&label_s_hs_traffic), tx)?;
    //   println!("s h ts: {}", server_handshake_traffic_secret.to_hex());
    let client_finished_key = derive_finished_key(ha, &client_handshake_traffic_secret)?;
    //   println!("cfk: {}", client_finished_key.to_hex());
    let server_finished_key = derive_finished_key(ha, &server_handshake_traffic_secret)?;
    //    println!("sfk: {}", server_finished_key.to_hex());
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_handshake_traffic_secret)?;
    //   let (k,iv) = &client_write_key_iv; println!("chk: {}\n     {}", k.to_hex(), iv.to_hex());
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_handshake_traffic_secret)?;
    //   let (k,iv) = &server_write_key_iv; println!("shk: {}\n     {}", k.to_hex(), iv.to_hex());
    let master_secret_ = derive_secret(ha, &handshake_secret, &bytes(&label_derived), &Digest_emp)?;
    let master_secret = hkdf_extract(&ha, &zero_key(ha), &master_secret_)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ))
}

pub fn derive_app_keys(
    ha: &HashAlgorithm,
    ae: &AeadAlgorithm,
    master_secret: &Key,
    tx: &Digest,
) -> Res<(AeadKeyIV, AeadKeyIV, Key)> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, &master_secret, &bytes(&label_c_ap_traffic), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, &master_secret, &bytes(&label_s_ap_traffic), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, ae, &client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, ae, &server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, &bytes(&label_exp_master), tx)?;
    Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ))
}

pub fn derive_rms(ha: &HashAlgorithm, master_secret: &Key, tx: &Digest) -> Res<Key> {
    let resumption_master_secret = derive_secret(ha, master_secret, &bytes(&label_res_master), tx)?;
    Ok(resumption_master_secret)
}

/* CipherStates Exported by the TLS 1.3 Handshake */
pub struct ClientCipherState0(pub AeadAlgorithm, pub AeadKeyIV, pub u64, pub Key);
pub struct ServerCipherState0(pub AeadAlgorithm, pub AeadKeyIV, pub u64, pub Key);
pub struct DuplexCipherStateH(
    pub AeadAlgorithm,
    pub AeadKeyIV,
    pub u64,
    pub AeadKeyIV,
    pub u64,
);
pub struct DuplexCipherState1(
    pub AeadAlgorithm,
    pub AeadKeyIV,
    pub u64,
    pub AeadKeyIV,
    pub u64,
    pub Key,
);

/* Incremental Transcript Construction
For simplicity, we store the full transcript, but an internal Digest state would suffice. */

pub struct Transcript(pub HashAlgorithm, pub HandshakeData);

pub fn transcript_empty(ha: HashAlgorithm) -> Transcript {
    Transcript(ha,HandshakeData(empty()))
}

pub fn transcript_add1(
    tx: Transcript,
    msg: &HandshakeData,
) -> Transcript {
    let Transcript(ha,tx) = tx;
    Transcript(ha,handshake_concat(tx,msg))
}

pub fn get_transcript_hash(
    tx: &Transcript
) -> Res<Digest> {
    let Transcript(ha,HandshakeData(txby)) = tx;
    let th = hash(ha,txby)?;
    Ok(th)
}

pub fn get_transcript_hash_truncated_client_hello(
    tx: &Transcript,
    ch: &HandshakeData,
    trunc_len: usize
) -> Res<Digest> {
    let Transcript(ha,HandshakeData(tx)) = tx;
    let HandshakeData(ch) = ch;
    Ok(hash(&ha, &tx.concat(&ch.slice_range(0..trunc_len)))?)
}

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify ->
PostServerFinished -> PostClientFinished
There are no optional steps, all states must be traversed, even if the traversals are NOOPS.
See "put_psk_skip_server_signature" below */

pub struct ClientPostClientHello(Random, Algorithms, KemSk, Option<PSK>, Transcript);
pub struct ClientPostServerHello(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ClientPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ClientPostClientFinished(Random, Random, Algorithms, Key, Transcript);

pub fn algs(st:&ClientPostServerHello) -> Algorithms {st.2}

pub struct ServerPostClientHello(Random, Algorithms, Bytes, Bytes, Bytes, SignatureKey, Option<PSK>, Transcript);
pub struct ServerPostServerHello(Random, Random, Algorithms, Bytes, SignatureKey, Key, MacKey, MacKey, Transcript);
pub struct ServerPostCertificateVerify(Random, Random, Algorithms, Key, MacKey, MacKey, Transcript);
pub struct ServerPostServerFinished(Random, Random, Algorithms, Key, MacKey, Transcript);
pub struct ServerPostClientFinished(Random, Random, Algorithms, Key, Transcript);

/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript Digestes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

pub fn get_client_hello(
    algs0: Algorithms,
    sn:&Bytes,
    tkt:Option<Bytes>,
    psk: Option<PSK>,
    ent: Entropy,
) -> Res<(HandshakeData, Option<ClientCipherState0>, ClientPostClientHello)> {
    let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs0;
    if ent.len() < 32 + dh_priv_len(&ks) {
        return Err(insufficient_entropy)
    } else {
        let tx = transcript_empty(ha);
        let cr = Random::from_seq(&ent.slice_range(0..32));
        let (x, gx) = kem_keygen(&ks, ent.slice_range(32..32 + dh_priv_len(&ks)))?;
        let (ch,trunc_len) = client_hello(&algs0,&cr,&gx,sn,&tkt)?;
        let (nch,cipher0,tx_ch) = compute_psk_binder_zero_rtt(algs0,ch,trunc_len,&psk,tx)?;
        return Ok((nch,cipher0,ClientPostClientHello(cr, algs0, x, psk,tx_ch)))
    }
}

pub fn compute_psk_binder_zero_rtt(
    algs0:Algorithms,
    ch:HandshakeData,
    trunc_len:usize,
    psk:&Option<PSK>,
    tx:Transcript
) -> Res<(HandshakeData,Option<ClientCipherState0>, Transcript)> {
    let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs0;
    match (psk_mode, psk, trunc_len) {
        (true, Some(k), _) => {
            let th_trunc = get_transcript_hash_truncated_client_hello(&tx,&ch,trunc_len)?;
            let mk = derive_binder_key(&ha, &k)?;
            let binder = hmac_tag(&ha, &mk, &th_trunc)?;
            let nch = set_client_hello_binder(&algs0,&Some(binder),ch,Some(trunc_len))?;
            let tx_ch = transcript_add1(tx,&nch);
            if zero_rtt {
                let th = get_transcript_hash(&tx_ch)?;
                let (aek, key) = derive_0rtt_keys(&ha, &ae, &k, &th)?;
                let cipher0 = Some(ClientCipherState0(ae, aek, 0, key));
                return Ok((nch, cipher0, tx_ch))
            } else {
                return Ok((nch, None, tx_ch))
            }
        },
        (false, None, 0) => {
            let tx_ch = transcript_add1(tx,&ch);
            return Ok((ch,None,tx_ch))
        },
        _ => return Err(psk_mode_mismatch),
    }
}

pub fn put_server_hello(
    sh: &HandshakeData,
    st: ClientPostClientHello,
) -> Res<(DuplexCipherStateH, ClientPostServerHello)> {
    let ClientPostClientHello(cr, algs0, x, psk, tx) = st;
    let (sr,gy) = parse_server_hello(&algs0,&sh)?;    
    let tx = transcript_add1(tx,&sh);
    if algs0 == algs0 {       
        let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs0;
        let gxy = kem_decap(&ks, &gy, x)?;
        let th = get_transcript_hash(&tx)?;
        let (chk, shk, cfk, sfk, ms) = derive_hk_ms(&ha, &ae, &gxy, &psk, &th)?;
        Ok((
            DuplexCipherStateH(ae, chk, 0, shk, 0),
            ClientPostServerHello(cr, sr, algs0, ms, cfk, sfk, tx),
        ))
    } else {
        Err(negotiation_mismatch)
    }
}

pub fn put_server_signature(
    ee: &HandshakeData,
    sc: &HandshakeData,
    scv: &HandshakeData,
    st: ClientPostServerHello,
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk,tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    if !psk_mode {
        parse_encrypted_extensions(&algs,&ee)?;
        let tx = transcript_add1(tx,ee);
        let cert = parse_server_certificate(&algs,&sc)?;
        let tx = transcript_add1(tx,sc);
        let th_sc = get_transcript_hash(&tx)?;
        let pk = verification_key_from_cert(&cert)?;
        let sig = parse_certificate_verify(&algs,&scv)?;
        let sigval = prefix_server_certificate_verify.concat(&th_sc);
        verify(&sa, &pk, &bytes(&sigval), &sig)?;
        let tx = transcript_add1(tx,scv);
        Ok((ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx)))
    } else {
        Err(psk_mode_mismatch)
    }
}


pub fn put_psk_skip_server_signature(
    ee:&HandshakeData, 
    st: ClientPostServerHello
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk,tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    if psk_mode {
        parse_encrypted_extensions(&algs,&ee)?;
        let tx = transcript_add1(tx,ee);
        Ok((ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx)))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn put_server_finished(
    sfin:&HandshakeData,
    st: ClientPostCertificateVerify
) -> Res<(DuplexCipherState1,ClientPostServerFinished)> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk,tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let th = get_transcript_hash(&tx)?;
    let vd = parse_finished(&algs,&sfin)?;
    hmac_verify(&ha,&sfk,&th,&vd)?;
    let tx = transcript_add1(tx,&sfin);
    let th_sfin = get_transcript_hash(&tx)?;
    let (cak, sak, exp) = derive_app_keys(&ha, &ae, &ms, &th_sfin)?;
    let cipher1 = DuplexCipherState1(ae, cak, 0, sak, 0, exp);
    Ok((cipher1,ClientPostServerFinished(cr,sr,algs,ms,cfk,tx)))
}

pub fn get_client_finished(
    st: ClientPostServerFinished,
) -> Res<(HandshakeData, ClientPostClientFinished)> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk, tx) = st;
    let th = get_transcript_hash(&tx)?;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let vd = hmac_tag(&ha, &cfk, &th)?;
    let cfin = finished(&algs,&vd)?;
    let tx = transcript_add1(tx,&cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&ha, &ms, &th)?;
    Ok((cfin, ClientPostClientFinished(cr, sr, algs, rms, tx)))
}


/* TLS 1.3 Server Side Handshake Functions */


pub struct ServerDB(pub Bytes,pub Bytes,pub SignatureKey,pub Option<(Bytes,PSK)>);

fn lookup_db(algs:Algorithms, db:&ServerDB,sni:&Bytes,tkt:&Option<Bytes>) ->
             Res<(Bytes,SignatureKey,Option<PSK>)> {
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ServerDB(server_name,cert,sk,psk_opt) = db;
    check_eq(sni,server_name)?;
    match (psk_mode,tkt, psk_opt) {
        (true, Some(ctkt), Some((stkt,psk))) => {
            check_eq(&ctkt,&stkt)?;
            Ok((cert.clone(),sk.clone(),Some(psk.clone())))},
        (false, _, _) => Ok((cert.clone(),sk.clone(),None)),
        _ => Err(psk_mode_mismatch)
    }
}

pub fn put_client_hello(
    algs: Algorithms,
    ch: &HandshakeData,
    db: ServerDB,
) -> Res<(Option<ServerCipherState0>,ServerPostClientHello)> {
    let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs;
    let (cr,sid,sni,gx,tkto,bindero,trunc_len) = parse_client_hello(&algs,&ch)?;
    let tx = transcript_empty(ha);
    let th_trunc = get_transcript_hash_truncated_client_hello(&tx,&ch,trunc_len)?;
    let tx = transcript_add1(tx,&ch);
    let th = get_transcript_hash(&tx)?;
    let (cert,sigk,psko) = lookup_db(algs,&db,&sni,&tkto)?;
    let cipher0 = process_psk_binder_zero_rtt(algs,th,th_trunc,&psko,bindero)?;
    return Ok((cipher0,ServerPostClientHello(cr, algs, sid, gx, cert, sigk, psko, tx)))
}

pub fn process_psk_binder_zero_rtt(
    algs:Algorithms,
    th_trunc:Digest,
    th:Digest,
    psko: &Option<PSK>,
    bindero: Option<Bytes>
) -> Res<Option<ServerCipherState0>> {
    let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs;
    match (psk_mode, psko, bindero) {
        (true, Some(k), Some(binder)) => {
            let mk = derive_binder_key(&ha, &k)?;
            hmac_verify(&ha, &mk, &th_trunc, &binder)?;
            if zero_rtt {
                let (aek, key) = derive_0rtt_keys(&ha, &ae, &k, &th)?;
                let cipher0 = Some(ServerCipherState0(ae, aek, 0, key));
                return Ok(cipher0)
            }
            else {
                return Ok(None)
             }
        },
        (false, None, None) => return Ok((None)),
        _ => return Err(psk_mode_mismatch),
        }
}

pub fn get_server_hello(
    st: ServerPostClientHello,
    ent:Entropy
) -> Res<(HandshakeData,DuplexCipherStateH, ServerPostServerHello)> {
    let ServerPostClientHello(cr, algs, sid, gx, cert, sigk, psk, tx) = st;
    let Algorithms(ha, ae, sa, ks, psk_mode, zero_rtt) = algs;
    if ent.len() < 32 + dh_priv_len(&ks) {
        return Err(insufficient_entropy)
    } else {
        let sr = Random::from_seq(&ent.slice_range(0..32));
        let (gxy, gy) = kem_encap(&ks, &gx, ent.slice_range(32..32 + dh_priv_len(&ks)))?;
        let sh = server_hello(&algs,&sr,&sid,&gy)?;
        let tx = transcript_add1(tx,&sh);
        let th = get_transcript_hash(&tx)?;
        let (chk, shk, cfk, sfk, ms) = derive_hk_ms(&ha, &ae, &gxy, &psk, &th)?;
        Ok((sh,
            DuplexCipherStateH(ae, shk, 0, chk, 0),
            ServerPostServerHello(cr, sr, algs, cert, sigk, ms, cfk, sfk, tx),
        ))
    }
}

pub fn get_server_signature(
    st: ServerPostServerHello,
    ent: Entropy,
) -> Res<(HandshakeData, HandshakeData, HandshakeData, ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, cert, sigk, ms, cfk, sfk, tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ee = encrypted_extensions(&algs)?;
    let tx = transcript_add1(tx,&ee);
    if !psk_mode {
        let sc = server_certificate(&algs,&cert)?;
        let tx = transcript_add1(tx,&sc);
        let th = get_transcript_hash(&tx)?;
        let sigval = prefix_server_certificate_verify.concat(&th);
        let sig = sign(&sa, &sigk, &sigval, ent)?;
        let scv = certificate_verify(&algs,&sig)?;
        let tx = transcript_add1(tx,&scv);
        Ok((ee,sc,scv, ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx)))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn get_skip_server_signature(st: ServerPostServerHello) -> Res<(HandshakeData,ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, cert, sigk, ms, cfk, sfk, tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    if psk_mode {
        let ee = encrypted_extensions(&algs)?;
        let tx = transcript_add1(tx,&ee);
        Ok((ee,ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk,tx)))
    } else {
        Err(psk_mode_mismatch)
    }
}

pub fn get_server_finished(
    st: ServerPostCertificateVerify,
) -> Res<(HandshakeData, DuplexCipherState1, ServerPostServerFinished)> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk, tx) = st;
    let th_scv = get_transcript_hash(&tx)?;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let vd = hmac_tag(&ha, &sfk, &th_scv)?;
    let sfin = finished(&algs,&vd)?;
    let tx = transcript_add1(tx,&sfin);
    let th_sfin = get_transcript_hash(&tx)?;
    let (cak, sak, exp) = derive_app_keys(&ha, &ae, &ms, &th_sfin)?;
    let cipher1 = DuplexCipherState1(ae, sak, 0, cak, 0, exp);
    Ok((sfin, cipher1, ServerPostServerFinished(cr, sr, algs, ms, cfk, tx)))
}

pub fn put_client_finished(
    cfin:&HandshakeData,
    st: ServerPostServerFinished,
) -> Res<ServerPostClientFinished> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk,tx) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let th = get_transcript_hash(&tx)?;
    let vd = parse_finished(&algs,&cfin)?;
    hmac_verify(&ha, &cfk, &th, &vd)?;
    let tx = transcript_add1(tx, &cfin);
    let th = get_transcript_hash(&tx)?;
    let rms = derive_rms(&ha, &ms,&th)?;
    Ok(ServerPostClientFinished(cr, sr, algs, rms, tx))
}

// Handshake API
// Client-Side Handshake API for TLS 1.3 Applications
// client_init -> (encrypt_zerortt)* -> client_set_params ->
// (decrypt_handshake)* -> client_finish -> (encrypt_handhsake) ->
// (encrypt_data | decrypt_data)*

type Client0 = ClientPostClientHello;
type ClientH = ClientPostServerHello;
type Client1 = ClientPostClientFinished;
    
pub fn client_init(algs:Algorithms,sn:&Bytes,tkt:Option<Bytes>,psk:Option<Key>,ent:Entropy)
-> Res<(HandshakeData,Option<ClientCipherState0>,Client0)> {get_client_hello(algs,sn,tkt,psk,ent)}

pub fn client_set_params(sh:&HandshakeData,st:Client0) -> Res<(DuplexCipherStateH,ClientH)> {
    put_server_hello(sh,st)}


pub fn client_finish(payload:&HandshakeData,st:ClientH) -> Res<(HandshakeData,DuplexCipherState1,Client1)> {
    match psk_mode(&algs(&st)) {
        false => {  
            let (ee,sc,scv,sfin) = get_handshake_messages4(payload)?;
            let cstate_cv = put_server_signature(&ee, &sc, &scv, st)?;
            let (cipher,cstate_fin) = put_server_finished(&sfin,cstate_cv)?;
            let (cfin,cstate) = get_client_finished(cstate_fin)?;
            Ok((cfin,cipher,cstate)) 
        },
        true => {
            let (ee,sfin) = get_handshake_messages2(payload)?;
            let cstate_cv = put_psk_skip_server_signature(&ee, st)?;
            let (cipher,cstate_fin) = put_server_finished(&sfin,cstate_cv)?;
            let (cfin,cstate) = get_client_finished(cstate_fin)?;
            Ok((cfin,cipher,cstate)) 
        }
    }
}

// Server-Side Handshake API for TLS 1.3 Applications
// server_init -> (encrypt_handshake)* -> (decrypt_zerortt)* ->
// (decrypt_handshake) -> server_finish ->
// (encrypt data | decrypt data)*

type Server0 = ServerPostServerFinished;
type Server1 = ServerPostClientFinished;

pub fn server_init(algs:Algorithms,db:ServerDB,ch:&HandshakeData,ent:Entropy) -> Res<(HandshakeData,HandshakeData,DuplexCipherStateH,DuplexCipherState1,Server0)> {
    let (cipher0,sstate) = put_client_hello(algs,ch,db)?;
    let (sh,cipherH,sstate) = get_server_hello(sstate,ent.slice(0,32+dh_priv_len(&kem_alg(&algs))))?;

    match psk_mode(&algs) {
        false => {
            let (ee,sc,scv,sstate) = get_server_signature(sstate,ent.slice(0,32))?; //FIX: use 32 extra bytes
            let (sfin,cipher1,sstate) = get_server_finished(sstate)?;
            let flight = handshake_concat(ee,&handshake_concat(sc,&handshake_concat(scv,&sfin)));
            Ok((sh,flight,cipherH,cipher1,sstate))
        },
        true => {
            let (ee,sstate) = get_skip_server_signature(sstate)?;
            let (sfin,cipher1,sstate) = get_server_finished(sstate)?;
            let flight = handshake_concat(ee,&sfin);
            Ok((sh,flight,cipherH,cipher1,sstate))
        }
    }
}
    
pub fn server_finish(cfin:&HandshakeData,st:Server0) -> Res<Server1> {
    put_client_finished(&cfin,st)
}

