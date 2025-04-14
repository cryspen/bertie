module t13.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val hash_empty (algorithm: t13.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val hkdf_expand_label
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (key label context: t13.Tls13utils.t_Bytes)
      (len: usize)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      (Seq.length label._0 < 65536)
      (fun _ -> Prims.l_True)

val derive_finished_key (ha: t13.Tls13crypto.t_HashAlgorithm) (k: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_secret
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (key label transcript_hash: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      (Seq.length label._0 < 65536)
      (fun _ -> Prims.l_True)

val derive_binder_key (ha: t13.Tls13crypto.t_HashAlgorithm) (k: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_rms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (master_secret tx: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_rsa_signature
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (cert sk sigval: t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_aead_key_iv
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (key: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13crypto.t_AeadKeyIV u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_0rtt_keys
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (key tx: t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_app_keys
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
            t13.Tls13utils.t_Bytes) u8) Prims.l_True (fun _ -> Prims.l_True)

val derive_hk_ms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (shared_secret: t13.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (transcript_hash: t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
            t13.Tls13utils.t_Bytes &
            t13.Tls13utils.t_Bytes &
            t13.Tls13utils.t_Bytes) u8) Prims.l_True (fun _ -> Prims.l_True)

type t_ClientPostCertificateVerify =
  | ClientPostCertificateVerify :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostCertificateVerify

type t_ClientPostClientFinished =
  | ClientPostClientFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostClientFinished

type t_ClientPostClientHello =
  | ClientPostClientHello :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      Core.Option.t_Option t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostClientHello

type t_ClientPostServerFinished =
  | ClientPostServerFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostServerFinished

type t_ClientPostServerHello =
  | ClientPostServerHello :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostServerHello

type t_ServerPostCertificateVerify =
  | ServerPostCertificateVerify :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostCertificateVerify

type t_ServerPostClientFinished =
  | ServerPostClientFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostClientFinished

type t_ServerPostClientHello = {
  f_client_randomness:t13.Tls13utils.t_Bytes;
  f_ciphersuite:t13.Tls13crypto.t_Algorithms;
  f_session_id:t13.Tls13utils.t_Bytes;
  f_gx:t13.Tls13utils.t_Bytes;
  f_server:t13.Server.t_ServerInfo;
  f_transcript:t13.Tls13formats.t_Transcript
}

type t_ServerPostServerFinished =
  | ServerPostServerFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostServerFinished

type t_ServerPostServerHello = {
  f_client_random:t13.Tls13utils.t_Bytes;
  f_server_random:t13.Tls13utils.t_Bytes;
  f_ciphersuite:t13.Tls13crypto.t_Algorithms;
  f_server:t13.Server.t_ServerInfo;
  f_master_secret:t13.Tls13utils.t_Bytes;
  f_cfk:t13.Tls13utils.t_Bytes;
  f_sfk:t13.Tls13utils.t_Bytes;
  f_transcript:t13.Tls13formats.t_Transcript
}

val algs_post_client_finished (st: t_ClientPostClientFinished)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_client_hello (st: t_ClientPostClientHello)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_server_hello (st: t_ClientPostServerHello)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val get_client_finished (handshake_state: t_ClientPostServerFinished)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_server_signature_no_psk
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (state: t_ServerPostServerHello)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_server_signature
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (state: t_ServerPostServerHello)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_skip_server_signature_no_psk (st: t_ServerPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_skip_server_signature (st: t_ServerPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_client_finished
      (cfin: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Prims.Pure (Core.Result.t_Result t_ServerPostClientFinished u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_psk_skip_server_signature
      (encrypted_extensions: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val server_finish
      (cf: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Prims.Pure (Core.Result.t_Result t_ServerPostClientFinished u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_server_hello
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (state: t_ServerPostClientHello)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_server_hello
      (handshake: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
    : Prims.Pure
      (Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val client_set_params
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
    : Prims.Pure
      (Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_psk_binder_zero_rtt
      (algs0: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (tx: t13.Tls13formats.t_Transcript)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t13.Tls13formats.t_Transcript) u8) Prims.l_True (fun _ -> Prims.l_True)

val build_client_hello
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8)
      (Seq.length sn._0 < 65536)
      (fun _ -> Prims.l_True)

val client_init
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8) 
      (Seq.length sn._0 < 65536)
      (fun _ -> Prims.l_True)
      
val get_server_finished (st: t_ServerPostCertificateVerify)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_server_finished
      (server_finished: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
    : Prims.Pure
      (Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val client_finish
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure
      (Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val process_psk_binder_zero_rtt
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (th_trunc th: t13.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option t13.Tls13utils.t_Bytes)
    : Prims.Pure
      (Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_client_hello
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
    : Prims.Pure
      (Core.Result.t_Result
          (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init_no_psk
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init_psk
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init
      (#impl_916461611_: Type)
      {| i1: Rand_core.t_CryptoRng impl_916461611_ |}
      {| i2: Rand_core.t_RngCore impl_916461611_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
    : Prims.Pure
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)
