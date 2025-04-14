module t13.Tls13keyscheduler
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13keyscheduler.Key_schedule in
  ()

/// Get the hash of an empty byte slice.
val hash_empty (algorithm: t13.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_binder_key
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (handle: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// Derive an AEAD key and iv.
val derive_aead_key_iv
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (handle: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t13.Tls13crypto.t_AeadKeyIV u8) Prims.l_True (fun _ -> Prims.l_True)

val next_keys_c_2_
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (handle: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Derive 0-RTT AEAD keys.
val derive_0rtt_keys
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (handle: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13keyscheduler.Key_schedule.t_Handle) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_finished_key
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (handle: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8) Prims.l_True (fun _ -> Prims.l_True)

/// Derive the handshake keys and master secret.
val derive_hk_handles
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (shared_secret: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (psko: Core.Option.t_Option t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (transcript_hash: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) Prims.l_True (fun _ -> Prims.l_True)

val derive_hk_ms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (client_handshake_traffic_secret server_handshake_traffic_secret:
          t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
            t13.Tls13utils.t_Bytes &
            t13.Tls13utils.t_Bytes) u8) Prims.l_True (fun _ -> Prims.l_True)

/// Derive the application keys and master secret.
val derive_app_handles
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (master_secret: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result
          (t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle &
            t13.Tls13keyscheduler.Key_schedule.t_Handle) u8) Prims.l_True (fun _ -> Prims.l_True)

val derive_app_keys
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (client_application_traffic_secret_0_ server_application_traffic_secret_0_:
          t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV) u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val derive_rms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (master_secret: t13.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: t13.Tls13utils.t_Bytes)
      (ks: t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
    : Prims.Pure
      (t13.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Core.Result.t_Result t13.Tls13keyscheduler.Key_schedule.t_Handle u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
