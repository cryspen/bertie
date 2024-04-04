module Bertie.Tls13record
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val derive_iv_ctr (iv: Bertie.Tls13utils.t_Bytes) (n: u64)
    : Prims.Pure Bertie.Tls13utils.t_Bytes
      (Seq.length iv._0 >= 8 /\ Seq.length iv._0 <= 32)
      (fun _ -> Prims.l_True)

val padlen (b: Bertie.Tls13utils.t_Bytes) (n: usize)
    : Prims.Pure usize
      (v n <= Seq.length b._0)
      (fun r -> v r <= v n)
      (decreases (v n))

val decrypt_record_payload
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ciphertext: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
      (Seq.length ciphertext._0 >= 5)
      (fun _ -> Prims.l_True)

val encrypt_record_payload
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ct: Bertie.Tls13formats.t_ContentType)
      (payload: Bertie.Tls13utils.t_Bytes)
      (pad: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      (Seq.length payload._0 < 65536 /\ v pad < 4096)
      (fun _ -> Prims.l_True)

type t_ClientCipherState0 =
  | ClientCipherState0 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13utils.t_Bytes
    -> t_ClientCipherState0

type t_DuplexCipherState1 =
  | DuplexCipherState1 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13utils.t_Bytes
    -> t_DuplexCipherState1

type t_DuplexCipherStateH = {
  f_sender_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_sender_counter:u64;
  f_receiver_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_receiver_counter:u64
}

val impl__DuplexCipherStateH__new
      (sender_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (sender_counter: u64)
      (receiver_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (receiver_counter: u64)
    : Prims.Pure t_DuplexCipherStateH Prims.l_True (fun _ -> Prims.l_True)

type t_ServerCipherState0 = {
  f_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_counter:u64;
  f_early_exporter_ms:Bertie.Tls13utils.t_Bytes
}

val client_cipher_state0
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (c: u64)
      (k: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure t_ClientCipherState0 Prims.l_True (fun _ -> Prims.l_True)

val decrypt_data (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
      (Seq.length ciphertext._0 >= 5)
      (fun _ -> Prims.l_True)

val decrypt_data_or_hs (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      (Seq.length ciphertext._0 >= 5)
      (fun _ -> Prims.l_True)

val decrypt_handshake (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_DuplexCipherStateH)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH) u8)
      (Seq.length ciphertext._0 >= 5)
      (fun _ -> Prims.l_True)

val decrypt_zerortt (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_ServerCipherState0)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
      (Seq.length ciphertext._0 >= 5)
      (fun _ -> Prims.l_True)

val duplex_cipher_state1
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv1: Bertie.Tls13crypto.t_AeadKeyIV)
      (c1: u64)
      (kiv2: Bertie.Tls13crypto.t_AeadKeyIV)
      (c2: u64)
      (k: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure t_DuplexCipherState1 Prims.l_True (fun _ -> Prims.l_True)

val encrypt_data (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_DuplexCipherState1)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      (Seq.length payload._0._0 < 65536 /\ v pad < 4096)
      (fun _ -> Prims.l_True)

val encrypt_handshake
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (pad: usize)
      (state: t_DuplexCipherStateH)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
      (Seq.length payload._0._0 < 65536 /\ v pad < 4096)
      (fun _ -> Prims.l_True)

val encrypt_zerortt (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_ClientCipherState0)
    : Prims.Pure (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
      (Seq.length payload._0._0 < 65536 /\ v pad < 4096)
      (fun _ -> Prims.l_True)

val server_cipher_state0
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (counter: u64)
      (early_exporter_ms: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure t_ServerCipherState0 Prims.l_True (fun _ -> Prims.l_True)
