module t13.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13utils in
  let open Rand_core in
  ()

type t_ClientPostClientHello =
  | ClientPostClientHello :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13utils.t_Bytes ->
      Core.Option.t_Option t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostClientHello

type t_ClientPostServerHello =
  | ClientPostServerHello :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostServerHello

type t_ClientPostCertificateVerify =
  | ClientPostCertificateVerify :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostCertificateVerify

type t_ClientPostServerFinished =
  | ClientPostServerFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostServerFinished

type t_ClientPostClientFinished =
  | ClientPostClientFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13formats.t_Transcript
    -> t_ClientPostClientFinished

val algs_post_client_hello (st: t_ClientPostClientHello)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_server_hello (st: t_ClientPostServerHello)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

val algs_post_client_finished (st: t_ClientPostClientFinished)
    : Prims.Pure t13.Tls13crypto.t_Algorithms Prims.l_True (fun _ -> Prims.l_True)

/// Server state after processing the client hello.
type t_ServerPostClientHello = {
  f_client_randomness:t13.Tls13utils.t_Bytes;
  f_ciphersuite:t13.Tls13crypto.t_Algorithms;
  f_session_id:t13.Tls13utils.t_Bytes;
  f_gx:t13.Tls13utils.t_Bytes;
  f_server:t13.Server.t_ServerInfo;
  f_transcript:t13.Tls13formats.t_Transcript
}

/// Server state after generating the server hello.
type t_ServerPostServerHello = {
  f_client_random:t13.Tls13utils.t_Bytes;
  f_server_random:t13.Tls13utils.t_Bytes;
  f_ciphersuite:t13.Tls13crypto.t_Algorithms;
  f_server:t13.Server.t_ServerInfo;
  f_master_secret:t13.Tls13keyscheduler.Key_schedule.t_Handle;
  f_cfk:t13.Tls13utils.t_Bytes;
  f_sfk:t13.Tls13utils.t_Bytes;
  f_transcript:t13.Tls13formats.t_Transcript
}

type t_ServerPostCertificateVerify =
  | ServerPostCertificateVerify :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostCertificateVerify

type t_ServerPostServerFinished =
  | ServerPostServerFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostServerFinished

type t_ServerPostClientFinished =
  | ServerPostClientFinished :
      t13.Tls13utils.t_Bytes ->
      t13.Tls13utils.t_Bytes ->
      t13.Tls13crypto.t_Algorithms ->
      t13.Tls13keyscheduler.Key_schedule.t_Handle ->
      t13.Tls13formats.t_Transcript
    -> t_ServerPostClientFinished

val compute_psk_binder_zero_rtt
      (algs0: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (tx: t13.Tls13formats.t_Transcript)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t13.Tls13formats.t_Transcript) u8)
      (requires
        trunc_len <=. (t13.Tls13formats.Handshake_data.impl_HandshakeData__len ch <: usize))
      (fun _ -> Prims.l_True)

val build_client_hello
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_server_hello
      (handshake: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_psk_skip_server_signature
      (encrypted_extensions: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Prims.Pure (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_server_finished
      (server_finished: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val get_client_finished
      (handshake_state: t_ClientPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val client_init
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Update the client state after generating the client hello message.
val client_set_params
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val client_finish
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Process the PSK binder for 0-RTT
val process_psk_binder_zero_rtt
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (th_trunc th: t13.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val put_client_hello
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8) Prims.l_True (fun _ -> Prims.l_True)

val get_server_hello
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (state: t_ServerPostClientHello)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_rsa_signature
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (cert sk sigval: t13.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
    : Prims.Pure (iimpl_447424039_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val get_server_signature_no_psk
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) Prims.l_True (fun _ -> Prims.l_True)

val get_server_signature
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
    : Prims.Pure
      (iimpl_447424039_ &
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

val get_server_finished
      (st: t_ServerPostCertificateVerify)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val put_client_finished
      (cfin: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t_ServerPostClientFinished u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init_no_psk
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init_psk
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_init
      (#iimpl_447424039_: Type0)
      {| i1: Rand_core.t_CryptoRng iimpl_447424039_ |}
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: iimpl_447424039_)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (iimpl_447424039_ & t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) Prims.l_True (fun _ -> Prims.l_True)

val server_finish
      (cf: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t_ServerPostClientFinished u8) Prims.l_True (fun _ -> Prims.l_True)
