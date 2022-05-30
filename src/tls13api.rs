// Import hacspec and all needed definitions.
use hacspec_lib::*;
use hacspec_cryptolib::*;
use crate::tls13utils::*;
use crate::tls13handshake::*;
use crate::tls13formats::*;
use crate::tls13record::*;

// Client-Side Handshake API for TLS 1.3 Applications
// client_init -> (encrypt_zerortt)* -> client_set_params ->
// (decrypt_handshake)* -> client_finish -> (encrypt_handhsake) ->
// (encrypt_data | decrypt_data)*

pub struct Client0(Algorithms,ClientPostClientHello);
pub struct ClientH(Algorithms,ClientPostServerHello);
pub struct Client1(Algorithms,ClientPostClientFinished);
    
pub fn client_init(algs:Algorithms,sn:&Bytes,tkt:Option<Bytes>,psk:Option<Key>,ent:Entropy) -> Res<(HandshakeData,Client0,Option<ClientCipherState0>)> {
    let (ch,c2s0,cstate) = get_client_hello(algs,sn,tkt,psk,ent)?;
    let st = Client0(algs,cstate);
    Ok((ch,st,c2s0))  
}

pub fn client_set_params(sh:&HandshakeData,st:Client0) -> Res<(ClientH,DuplexCipherStateH)> {
    let Client0(algs,cstate) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (cipher,cstate) = put_server_hello(sh,cstate)?;
    Ok((ClientH(algs,cstate),cipher))
}

pub fn client_finish(payload:&HandshakeData,st:ClientH) -> Res<(HandshakeData,Client1,DuplexCipherState1)> {
    let ClientH(algs,cstate) = st;
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let mut next = 0;
    let (ee,len_ee) = check_handshake_message(&payload,0)?;
    next = next + len_ee;
    let cstate_cv:ClientPostCertificateVerify;
    match psk_mode {
        false => {  
            let (sc,len_sc) = check_handshake_message(&payload,next)?;
            next = next + len_sc;
            let (cv,len_cv) = check_handshake_message(&payload,next)?;
            next = next + len_cv; 
            cstate_cv = put_server_signature(&ee, &sc, &cv, cstate)?;
        },
        true => {
            cstate_cv = put_psk_skip_server_signature(&ee,cstate)?;
        }
    };    
    let (sfin,len_fin) = check_handshake_message(&payload,next)?;
    next = next + len_fin;
    if !has_handshake_message(payload,next) {
        let (cipher,cstate) = put_server_finished(&sfin,cstate_cv)?;
        let (cfin,cstate) = get_client_finished(cstate)?;
        Ok((cfin,Client1(algs,cstate),cipher))
    } else {Err(parse_failed)}
}

// Server-Side Handshake API for TLS 1.3 Applications
// server_init -> (encrypt_handshake)* -> (decrypt_zerortt)* ->
// (decrypt_handshake) -> server_finish ->
// (encrypt data | decrypt data)*

pub struct Server0(Algorithms,ServerPostServerFinished);
pub struct Server1(Algorithms,ServerPostClientFinished);

pub fn server_init(algs:Algorithms,db:ServerDB,ch:&HandshakeData,ent:Entropy) -> Res<(HandshakeData,HandshakeData,Server0,DuplexCipherStateH,DuplexCipherState1)> {
    let Algorithms(ha, ae, sa, gn, psk_mode, zero_rtt) = &algs;
    let (cipher0,sstate) = put_client_hello(algs,&ch,db)?;
    let (sh,cipherH,sstate) = get_server_hello(sstate,ent.slice(0,32+dh_priv_len(gn)))?;

    match psk_mode {
        false => {
            let (ee,sc,scv,sstate) = get_server_signature(sstate,ent.slice(0,32))?; 
            let (sfin,cipher1,sstate) = get_server_finished(sstate)?;
            let flight = handshake_concat(ee,&handshake_concat(sc,&handshake_concat(scv,&sfin)));
            Ok((sh,flight,Server0(algs,sstate),cipherH,cipher1))
        },
        true => {
            let (ee,sstate) = get_skip_server_signature(sstate)?;
            let (sfin,cipher1,sstate) = get_server_finished(sstate)?;
            let flight = handshake_concat(ee,&sfin);
            Ok((sh,flight,Server0(algs,sstate),cipherH,cipher1))
        }
    }
}
    
pub fn server_finish(payload:&HandshakeData,st:Server0) -> Res<Server1> {
    let Server0(algs,sstate) = st;
    let (cfin,flen) = check_handshake_message(payload,0)?;
    let sstate = put_client_finished(&cfin,sstate)?;
    if !has_handshake_message(payload,flen) {
        Ok(Server1(algs,sstate))
    } else {Err(parse_failed)}
}

/* Record Encryption/Decryption API */

pub struct AppData(pub Bytes);

pub fn encrypt_zerortt(payload:&AppData, pad:usize, st: ClientCipherState0) -> Res<(Bytes,ClientCipherState0)> {
    let ClientCipherState0(ae, kiv, n, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,payload,pad)?;
    Ok((rec,ClientCipherState0(ae,kiv,n+1, exp)))
}

pub fn decrypt_zerortt(ciphertext:&Bytes, st: ServerCipherState0) -> Res<(AppData,ServerCipherState0)> {
    let ServerCipherState0(ae, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((AppData(payload),ServerCipherState0(ae,kiv,n+1,exp)))
}

pub fn encrypt_handshake(payload:&HandshakeData, pad:usize, st: DuplexCipherStateH) -> Res<(Bytes,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, kiv, n, x, y) = st;
    let HandshakeData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::Handshake,payload,pad)?;
    Ok((rec,DuplexCipherStateH(ae,kiv,n+1, x, y)))
}

pub fn decrypt_handshake(ciphertext:&Bytes, st: DuplexCipherStateH) -> Res<(HandshakeData,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, x, y, kiv, n) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::Handshake)?;
    Ok((HandshakeData(payload),DuplexCipherStateH(ae, x, y, kiv, n+1)))
}

pub fn encrypt_data(payload:&AppData, pad:usize, st: DuplexCipherState1) -> Res<(Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, kiv, n, x, y, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,payload,pad)?;
    Ok((rec,DuplexCipherState1(ae,kiv,n+1,x,y,exp)))
}

pub fn decrypt_data_or_hs(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(ContentType,Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    Ok((ct,payload,DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}
pub fn decrypt_data(ciphertext:&Bytes, st: DuplexCipherState1) -> Res<(AppData,DuplexCipherState1)> {
    let DuplexCipherState1(ae, x, y, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((AppData(payload),DuplexCipherState1(ae, x, y, kiv, n+1, exp)))
}
