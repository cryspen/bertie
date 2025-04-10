module Bertie.Tls13record
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13formats in
  let open Bertie.Tls13formats.Handshake_data in
  let open Bertie.Tls13utils in
  ()

type t_ClientCipherState0 =
  | ClientCipherState0 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13keyscheduler.Key_schedule.t_TagKey
    -> t_ClientCipherState0

/// Build the initial client cipher state.
val client_cipher_state0
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (c: u64)
      (k: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
    : Prims.Pure t_ClientCipherState0 Prims.l_True (fun _ -> Prims.l_True)

/// The AEAD state of the server with the key, iv, and counter.
type t_ServerCipherState0 = {
  f_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_counter:u64;
  f_early_exporter_ms:Bertie.Tls13keyscheduler.Key_schedule.t_TagKey
}

/// Create the initial cipher state for the server.
val server_cipher_state0
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (counter: u64)
      (early_exporter_ms: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
    : Prims.Pure t_ServerCipherState0 Prims.l_True (fun _ -> Prims.l_True)

/// Duplex cipher state with hello keys.
type t_DuplexCipherStateH = {
  f_sender_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_sender_counter:u64;
  f_receiver_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_receiver_counter:u64
}

/// Create a new state
val impl_DuplexCipherStateH__new
      (sender_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (sender_counter: u64)
      (receiver_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (receiver_counter: u64)
    : Prims.Pure t_DuplexCipherStateH Prims.l_True (fun _ -> Prims.l_True)

type t_DuplexCipherState1 =
  | DuplexCipherState1 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13keyscheduler.Key_schedule.t_TagKey
    -> t_DuplexCipherState1

/// Create the next cipher state.
val duplex_cipher_state1
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv1: Bertie.Tls13crypto.t_AeadKeyIV)
      (c1: u64)
      (kiv2: Bertie.Tls13crypto.t_AeadKeyIV)
      (c2: u64)
      (k: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
    : Prims.Pure t_DuplexCipherState1 Prims.l_True (fun _ -> Prims.l_True)

/// Derive the AEAD IV with counter `n`
val derive_iv_ctr (iv: Bertie.Tls13utils.t_Bytes) (n: u64)
    : Prims.Pure Bertie.Tls13utils.t_Bytes
      (requires (Bertie.Tls13utils.impl_Bytes__len iv <: usize) >=. mk_usize 8)
      (fun _ -> Prims.l_True)

/// Encrypt the record `payload` with the given `key_iv`.
val encrypt_record_payload
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ct: Bertie.Tls13formats.t_ContentType)
      (payload: Bertie.Tls13utils.t_Bytes)
      (pad: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encrypt 0-RTT `payload`.
/// TODO: Implement 0-RTT
val encrypt_zerortt (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_ClientCipherState0)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Encrypt the `payload` [`HandshakeData`].
/// Returns the ciphertext, new [`DuplexCipherStateH`] if successful, or a
/// [`TLSError`] otherwise.
val encrypt_handshake
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (pad: usize)
      (state: t_DuplexCipherStateH)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val encrypt_data (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_DuplexCipherState1)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val padlen (b: Bertie.Tls13utils.t_Bytes) (n: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// AEAD decrypt the record `ciphertext`
val decrypt_record_payload
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ciphertext: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decrypt 0-RTT `ciphertext`.
/// TODO: Implement 0-RTT
val decrypt_zerortt (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_ServerCipherState0)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Decrypt a handshake message.
val decrypt_handshake (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_DuplexCipherStateH)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decrypt_data_or_hs (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decrypt_data (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
