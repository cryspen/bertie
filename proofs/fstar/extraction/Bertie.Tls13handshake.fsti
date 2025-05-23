module Bertie.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  let open Rand_core in
  ()

/// Get the hash of an empty byte slice.
val hash_empty (algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// HKDF expand with a `label`.
val hkdf_expand_label
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label context: Bertie.Tls13utils.t_Bytes)
      (len: usize)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_secret
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label transcript_hash: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_binder_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Derive an AEAD key and iv.
val derive_aead_key_iv
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Derive 0-RTT AEAD keys.
val derive_0rtt_keys
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key tx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_finished_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Derive the handshake keys and master secret.
val derive_hk_ms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (shared_secret: Bertie.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (transcript_hash: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Derive the application keys and master secret.
val derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes) u8) Prims.l_True (fun _ -> Prims.l_True)

val derive_rms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

type t_ClientPostClientHello =
  | ClientPostClientHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostClientHello

type t_ClientPostServerHello =
  | ClientPostServerHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostServerHello

type t_ClientPostCertificateVerify =
  | ClientPostCertificateVerify :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostCertificateVerify

type t_ClientPostServerFinished =
  | ClientPostServerFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostServerFinished

type t_ClientPostClientFinished =
  | ClientPostClientFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostClientFinished

val algs_post_client_hello (st: t_ClientPostClientHello)
    : Prims.Pure Bertie.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_server_hello (st: t_ClientPostServerHello)
    : Prims.Pure Bertie.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_client_finished (st: t_ClientPostClientFinished)
    : Prims.Pure Bertie.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

/// Server state after processing the client hello.
type t_ServerPostClientHello = {
  f_client_randomness:Bertie.Tls13utils.t_Bytes;
  f_ciphersuite:Bertie.Tls13crypto.t_Algorithms;
  f_session_id:Bertie.Tls13utils.t_Bytes;
  f_gx:Bertie.Tls13utils.t_Bytes;
  f_server:Bertie.Server.t_ServerInfo;
  f_transcript:Bertie.Tls13formats.t_Transcript
}

/// Server state after generating the server hello.
type t_ServerPostServerHello = {
  f_client_random:Bertie.Tls13utils.t_Bytes;
  f_server_random:Bertie.Tls13utils.t_Bytes;
  f_ciphersuite:Bertie.Tls13crypto.t_Algorithms;
  f_server:Bertie.Server.t_ServerInfo;
  f_master_secret:Bertie.Tls13utils.t_Bytes;
  f_cfk:Bertie.Tls13utils.t_Bytes;
  f_sfk:Bertie.Tls13utils.t_Bytes;
  f_transcript:Bertie.Tls13formats.t_Transcript
}

type t_ServerPostCertificateVerify =
  | ServerPostCertificateVerify :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostCertificateVerify

type t_ServerPostServerFinished =
  | ServerPostServerFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostServerFinished

type t_ServerPostClientFinished =
  | ServerPostClientFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostClientFinished

val compute_psk_binder_zero_rtt
      (algs0: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (tx: Bertie.Tls13formats.t_Transcript)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            Bertie.Tls13formats.t_Transcript) u8) Prims.l_True (fun _ -> Prims.l_True)

val build_client_hello
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_server_hello
      (handshake: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_psk_skip_server_signature
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_server_finished
      (server_finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val get_client_finished (handshake_state: t_ClientPostServerFinished)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val client_init
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Update the client state after generating the client hello message.
val client_set_params
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
    : Prims.Pure
      (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val client_finish
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Process the PSK binder for 0-RTT
val process_psk_binder_zero_rtt
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (th_trunc th: Bertie.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
    : Prims.Pure
      (Core.Result.t_Result
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val get_server_hello
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (state: t_ServerPostClientHello)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_rsa_signature
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (cert sk sigval: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_916461611_)
    : Prims.Pure (iimpl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_server_signature_no_psk
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (state: t_ServerPostServerHello)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_server_signature
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (state: t_ServerPostServerHello)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_skip_server_signature_no_psk (st: t_ServerPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_skip_server_signature (st: t_ServerPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_server_finished (st: t_ServerPostCertificateVerify)
    : Prims.Pure
      (Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_client_finished
      (cfin: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Prims.Pure (Core.Result.t_Result t_ServerPostClientFinished u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_init_no_psk
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init_psk
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init
      (#iimpl_916461611_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_916461611_ |}
      {| i2: Rand_core.t_RngCore iimpl_916461611_ |}
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_916461611_)
    : Prims.Pure
      (iimpl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_finish
      (cf: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Prims.Pure (Core.Result.t_Result t_ServerPostClientFinished u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
