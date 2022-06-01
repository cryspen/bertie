// TLS 1.3 Record Layer Computations

use hacspec_cryptolib::*;
use crate::tls13utils::*;
use crate::tls13formats::*;
//use crate::tls13handshake::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

/* CipherStates Exported by the TLS 1.3 Handshake */
pub struct ClientCipherState0(AeadAlgorithm, AeadKeyIV, u64, Key);
pub fn client_cipher_state0(ae:AeadAlgorithm,kiv:AeadKeyIV,c:u64,k:Key)
-> ClientCipherState0 {ClientCipherState0(ae,kiv,c,k)}

pub struct ServerCipherState0(AeadAlgorithm, AeadKeyIV, u64, Key);
pub fn server_cipher_state0(ae:AeadAlgorithm,kiv:AeadKeyIV,c:u64,k:Key)
-> ServerCipherState0 {ServerCipherState0(ae,kiv,c,k)}

pub struct DuplexCipherStateH(
    AeadAlgorithm,
    AeadKeyIV,
    u64,
    AeadKeyIV,
    u64,
);
pub fn duplex_cipher_stateH(ae:AeadAlgorithm,kiv1:AeadKeyIV,c1:u64,kiv2:AeadKeyIV,c2:u64)
-> DuplexCipherStateH {DuplexCipherStateH(ae,kiv1,c1,kiv2,c2)}

pub struct DuplexCipherState1(
    AeadAlgorithm,
    AeadKeyIV,
    u64,
    AeadKeyIV,
    u64,
    Key,
);
pub fn duplex_cipher_state1(ae:AeadAlgorithm,kiv1:AeadKeyIV,c1:u64,kiv2:AeadKeyIV,c2:u64,k:Key)
-> DuplexCipherState1 {DuplexCipherState1(ae,kiv1,c1,kiv2,c2,k)}


pub fn derive_iv_ctr(ae: &AeadAlgorithm, iv: &AeadIv, n:u64) -> AeadIv {
    let counter = bytes(&U64_to_be_bytes(U64(n)));
    let mut iv_ctr = AeadIv::new(iv.len());
    for i in 0..iv.len()-8 {
        iv_ctr[i] = iv[i];
    }
    for i in 0..8 {
        iv_ctr[i+iv.len()-8] = iv[i+iv.len()-8] ^ counter[i];
    }
    iv_ctr
}

pub fn encrypt_record_payload(ae:&AeadAlgorithm, kiv: &AeadKeyIV, n:u64, ct:ContentType, payload: &Bytes, pad:usize) -> Res<Bytes> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae,&iv,n);
    let inner_plaintext = payload.concat(&bytes1(content_type(ct))).concat(&zeros(pad));
    let clen = inner_plaintext.len() + 16;
    if clen <= 65536 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        let cip = aead_encrypt(&ae, &k, &iv_ctr, &inner_plaintext, &ad)?;
        let rec = ad.concat(&cip);
        Ok(rec)
    } else {
        Err(payload_too_long)
    }
}

pub fn padlen(b:&Bytes,n:usize) -> usize {
    if n > 0 && b[n-1].declassify() == 0 {1 + padlen(&b,n-1)}
    else {0}
}
pub fn decrypt_record_payload(ae:&AeadAlgorithm, kiv:&AeadKeyIV, n:u64, ciphertext: &Bytes) -> Res<(ContentType,Bytes)> {
    let (k,iv) = kiv;
    let iv_ctr = derive_iv_ctr(&ae, &iv, n);
    let clen = ciphertext.len() - 5;
    if clen <= 65536 && clen > 16 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes5(23, 3, 3, clenb[0], clenb[1]);
        check_eq(&ad,&ciphertext.slice_range(0..5))?;
        let cip = ciphertext.slice_range(5..ciphertext.len());
        let plain = aead_decrypt(&ae, &k, &iv_ctr, &cip, &ad)?;
        let payload_len = plain.len() - padlen(&plain,plain.len()) - 1;
        let ct = get_content_type(plain[payload_len].declassify())?;
        let payload = plain.slice_range(0..payload_len);       
        Ok((ct,payload))
    } else {
        Err(payload_too_long)
    }
}

/* Record Encryption/Decryption API */
#[derive(PartialEq)]
pub struct AppData(Bytes);

pub fn app_data(b:Bytes) -> AppData{AppData(b)}
pub fn app_data_bytes(a:AppData)->Bytes{a.0}

pub fn encrypt_zerortt(payload:AppData, pad:usize, st: ClientCipherState0) -> Res<(Bytes,ClientCipherState0)> {
    let ClientCipherState0(ae, kiv, n, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,&payload,pad)?;
    Ok((rec,ClientCipherState0(ae,kiv,n+1, exp)))
}

pub fn decrypt_zerortt(ciphertext:&Bytes, st: ServerCipherState0) -> Res<(AppData,ServerCipherState0)> {
    let ServerCipherState0(ae, kiv, n, exp) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::ApplicationData)?;
    Ok((AppData(payload),ServerCipherState0(ae,kiv,n+1,exp)))
}

pub fn encrypt_handshake(payload:HandshakeData, pad:usize, st: DuplexCipherStateH) -> Res<(Bytes,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, kiv, n, x, y) = st;
    let payload = handshake_data_bytes(&payload);
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::Handshake,&payload,pad)?;
    Ok((rec,DuplexCipherStateH(ae,kiv,n+1, x, y)))
}

pub fn decrypt_handshake(ciphertext:&Bytes, st: DuplexCipherStateH) -> Res<(HandshakeData,DuplexCipherStateH)> {
    let DuplexCipherStateH(ae, x, y, kiv, n) = st;
    let (ct,payload) = decrypt_record_payload(&ae,&kiv,n,ciphertext)?;
    check(ct == ContentType::Handshake)?;
    Ok((handshake_data(payload),DuplexCipherStateH(ae, x, y, kiv, n+1)))
}

pub fn encrypt_data(payload:AppData, pad:usize, st: DuplexCipherState1) -> Res<(Bytes,DuplexCipherState1)> {
    let DuplexCipherState1(ae, kiv, n, x, y, exp) = st;
    let AppData(payload) = payload;
    let rec = encrypt_record_payload(&ae,&kiv,n,ContentType::ApplicationData,&payload,pad)?;
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
