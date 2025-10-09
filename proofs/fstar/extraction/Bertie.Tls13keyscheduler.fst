module Bertie.Tls13keyscheduler
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13keyscheduler.Key_schedule in
  ()

let hash_empty (algorithm: Bertie.Tls13crypto.t_HashAlgorithm) =
  Bertie.Tls13crypto.hash algorithm
    (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)

let derive_binder_key
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (handle: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
    Bertie.Tls13keyscheduler.Key_schedule.zero_salt ks ha
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let zero_salt_handle:Bertie.Tls13keyscheduler.Key_schedule.t_Handle = out in
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
    Bertie.Tls13keyscheduler.Key_schedule.v_XTR ks
      (mk_u8 0)
      (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_ES
        <:
        Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
      handle
      zero_salt_handle
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok hoist137 ->
        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
          Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
            (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_Bind
              <:
              Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
            (mk_u8 0)
            early_secret
            true
            hoist137
        in
        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        let hax_temp_output:Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 =
          out
        in
        ks, hax_temp_output
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8)
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8)

let derive_aead_key_iv
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (handle: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match
    Bertie.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks handle
    <:
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_TagKey u8
  with
  | Core.Result.Result_Ok hoist138 ->
    let key:Bertie.Tls13utils.t_Bytes = hoist138.Bertie.Tls13keyscheduler.Key_schedule.f_val in
    (match
        Bertie.Tls13keyscheduler.Key_schedule.hkdf_expand_label hash_algorithm
          key
          (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_KEY <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13crypto.impl_AeadAlgorithm__key_len aead_algorithm <: usize)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok sender_write_key ->
        (match
            Bertie.Tls13keyscheduler.Key_schedule.hkdf_expand_label hash_algorithm
              key
              (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_IV <: t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13crypto.impl_AeadAlgorithm__iv_len aead_algorithm <: usize)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok sender_write_iv ->
            let hax_temp_output:Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 =
              Core.Result.Result_Ok
              (Bertie.Tls13crypto.impl_AeadKeyIV__new (Bertie.Tls13crypto.impl_AeadKey__new sender_write_key
                      aead_algorithm
                    <:
                    Bertie.Tls13crypto.t_AeadKey)
                  sender_write_iv)
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
            in
            ks, hax_temp_output
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8))
      | Core.Result.Result_Err err ->
        ks, (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8))
  | Core.Result.Result_Err err ->
    ks, (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)

let next_keys_c_2_
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (handle: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: Bertie.Tls13utils.t_Bytes)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
    Bertie.Tls13keyscheduler.Key_schedule.zero_salt ks hash_algorithm
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let zero_salt_handle:Bertie.Tls13keyscheduler.Key_schedule.t_Handle = out in
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
    Bertie.Tls13keyscheduler.Key_schedule.v_XTR ks
      (mk_u8 0)
      (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_ES
        <:
        Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
      handle
      zero_salt_handle
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty hash_algorithm <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok digest_emp ->
        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
          Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
            (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_ESalt
              <:
              Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
            (mk_u8 0)
            early_secret
            true
            digest_emp
        in
        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
          | Core.Result.Result_Ok derived_secret ->
            let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
              Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
                (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_CET
                  <:
                  Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                (mk_u8 0)
                early_secret
                true
                tx
            in
            let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
              with
              | Core.Result.Result_Ok client_early_traffic_secret ->
                let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                  Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
                    (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_EEM
                      <:
                      Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                    (mk_u8 0)
                    early_secret
                    true
                    tx
                in
                let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
                  with
                  | Core.Result.Result_Ok early_exporter_master_secret ->
                    let hax_temp_output:Core.Result.t_Result
                      (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                        Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                        Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8 =
                      Core.Result.Result_Ok
                      (early_exporter_master_secret, client_early_traffic_secret, derived_secret
                        <:
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle))
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8
                    in
                    ks, hax_temp_output
                    <:
                    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                    <:
                    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                <:
                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)

let derive_0rtt_keys
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (handle: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: Bertie.Tls13utils.t_Bytes)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result
      (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8) =
    next_keys_c_2_ hash_algorithm handle tx ks
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match
    out
    <:
    Core.Result.t_Result
      (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8
  with
  | Core.Result.Result_Ok
    (early_exporter_master_secret, client_early_traffic_secret, derived_secret) ->
    let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) =
      derive_aead_key_iv hash_algorithm aead_algorithm client_early_traffic_secret ks
    in
    let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
    (match out <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 with
      | Core.Result.Result_Ok sender_write_key_iv ->
        let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8 =
          Core.Result.Result_Ok
          (sender_write_key_iv, early_exporter_master_secret
            <:
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle))
          <:
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8
        in
        ks, hax_temp_output
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)

let derive_finished_key
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (handle: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  match
    Bertie.Tls13keyscheduler.Key_schedule.tagkey_from_handle ks handle
    <:
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_TagKey u8
  with
  | Core.Result.Result_Ok k ->
    let hax_temp_output:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
      Bertie.Tls13keyscheduler.Key_schedule.hkdf_expand_label ha
        k.Bertie.Tls13keyscheduler.Key_schedule.f_val
        (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_FINISHED <: t_Slice u8)
          <:
          Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13crypto.impl_HashAlgorithm__hmac_tag_len ha <: usize)
    in
    ks, hax_temp_output
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    ks, (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)

let derive_hk_handles
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (shared_secret: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (psko: Core.Option.t_Option Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (transcript_hash: Bertie.Tls13utils.t_Bytes)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let ks, psk_handle:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
    match psko <: Core.Option.t_Option Bertie.Tls13keyscheduler.Key_schedule.t_Handle with
    | Core.Option.Option_Some k ->
      ks,
      Core.Clone.f_clone #Bertie.Tls13keyscheduler.Key_schedule.t_Handle
        #FStar.Tactics.Typeclasses.solve
        k
      <:
      (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
    | _ ->
      let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
        Bertie.Tls13keyscheduler.Key_schedule.no_psk ks ha
      in
      let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
      ks, out
      <:
      (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
        Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
  in
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
    Bertie.Tls13keyscheduler.Key_schedule.zero_salt ks ha
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let zero_salt_handle:Bertie.Tls13keyscheduler.Key_schedule.t_Handle = out in
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
    Bertie.Tls13keyscheduler.Key_schedule.v_XTR ks
      (mk_u8 0)
      (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_ES
        <:
        Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
      psk_handle
      zero_salt_handle
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok digest_emp ->
        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
          Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
            (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_ESalt
              <:
              Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
            (mk_u8 0)
            early_secret
            true
            digest_emp
        in
        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
          | Core.Result.Result_Ok derived_secret ->
            let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
              Bertie.Tls13keyscheduler.Key_schedule.v_XTR ks
                (mk_u8 0)
                (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_HS
                  <:
                  Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                shared_secret
                derived_secret
            in
            let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match
                out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
              with
              | Core.Result.Result_Ok handshake_secret ->
                let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                  Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
                    (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_CHT
                      <:
                      Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                    (mk_u8 0)
                    handshake_secret
                    true
                    transcript_hash
                in
                let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                (match
                    out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
                  with
                  | Core.Result.Result_Ok client_handshake_traffic_secret ->
                    let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                      Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
                        (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_SHT
                          <:
                          Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                        (mk_u8 0)
                        handshake_secret
                        true
                        transcript_hash
                    in
                    let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                    (match
                        out
                        <:
                        Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
                      with
                      | Core.Result.Result_Ok server_handshake_traffic_secret ->
                        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
                          Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
                            (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_HSalt
                              <:
                              Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                            (mk_u8 0)
                            handshake_secret
                            true
                            digest_emp
                        in
                        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                        (match
                            out
                            <:
                            Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
                          with
                          | Core.Result.Result_Ok master_secret_ ->
                            let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) =
                              Bertie.Tls13keyscheduler.Key_schedule.zero_ikm ks ha
                            in
                            let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                            let zero_ikm_handle:Bertie.Tls13keyscheduler.Key_schedule.t_Handle =
                              out
                            in
                            let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8
                            ) =
                              Bertie.Tls13keyscheduler.Key_schedule.v_XTR ks
                                (mk_u8 0)
                                (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_AS
                                  <:
                                  Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
                                zero_ikm_handle
                                master_secret_
                            in
                            let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
                            (match
                                out
                                <:
                                Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle
                                  u8
                              with
                              | Core.Result.Result_Ok master_secret ->
                                let hax_temp_output:Core.Result.t_Result
                                  (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                    Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                    Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8 =
                                  Core.Result.Result_Ok
                                  (client_handshake_traffic_secret,
                                    server_handshake_traffic_secret,
                                    master_secret
                                    <:
                                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle))
                                  <:
                                  Core.Result.t_Result
                                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8
                                in
                                ks, hax_temp_output
                                <:
                                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                  Core.Result.t_Result
                                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                              | Core.Result.Result_Err err ->
                                ks,
                                (Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                                <:
                                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                                  Core.Result.t_Result
                                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
                          | Core.Result.Result_Err err ->
                            ks,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                            <:
                            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                              Core.Result.t_Result
                                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
                      | Core.Result.Result_Err err ->
                        ks,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                        <:
                        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                          Core.Result.t_Result
                            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
                  | Core.Result.Result_Err err ->
                    ks,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                    <:
                    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                      Core.Result.t_Result
                        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
                <:
                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                      Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)

let derive_hk_ms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (client_handshake_traffic_secret server_handshake_traffic_secret:
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
    derive_finished_key ha client_handshake_traffic_secret ks
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
  | Core.Result.Result_Ok client_finished_key ->
    let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
      derive_finished_key ha server_handshake_traffic_secret ks
    in
    let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
    (match out <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok server_finished_key ->
        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) =
          derive_aead_key_iv ha ae client_handshake_traffic_secret ks
        in
        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 with
          | Core.Result.Result_Ok client_write_key_iv ->
            let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) =
              derive_aead_key_iv ha ae server_handshake_traffic_secret ks
            in
            let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
            (match out <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 with
              | Core.Result.Result_Ok server_write_key_iv ->
                let hax_temp_output:Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8 =
                  Core.Result.Result_Ok
                  (client_write_key_iv,
                    server_write_key_iv,
                    client_finished_key,
                    server_finished_key
                    <:
                    (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes) u8
                in
                ks, hax_temp_output
                <:
                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                ks,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes) u8)
                <:
                (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
                  Core.Result.t_Result
                    (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes) u8))
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes &
          Bertie.Tls13utils.t_Bytes) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes &
          Bertie.Tls13utils.t_Bytes) u8)

let derive_app_handles
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (master_secret: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: Bertie.Tls13utils.t_Bytes)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
    Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
      (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_CAT
        <:
        Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
      (mk_u8 0)
      master_secret
      true
      tx
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
  | Core.Result.Result_Ok client_application_traffic_secret_0_ ->
    let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
      Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
        (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_SAT
          <:
          Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
        (mk_u8 0)
        master_secret
        true
        tx
    in
    let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
    (match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
      | Core.Result.Result_Ok server_application_traffic_secret_0_ ->
        let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
          Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
            (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_EAM
              <:
              Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
            (mk_u8 0)
            master_secret
            true
            tx
        in
        let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
        (match out <: Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 with
          | Core.Result.Result_Ok exporter_master_secret ->
            let hax_temp_output:Core.Result.t_Result
              (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8 =
              Core.Result.Result_Ok
              (client_application_traffic_secret_0_,
                server_application_traffic_secret_0_,
                exporter_master_secret
                <:
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle))
              <:
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8
            in
            ks, hax_temp_output
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
          | Core.Result.Result_Err err ->
            ks,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
            <:
            (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
              Core.Result.t_Result
                (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
                  Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result
            (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
              Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8))
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result
        (Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle &
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle) u8)

let derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (client_application_traffic_secret_0_ server_application_traffic_secret_0_:
          Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) =
    derive_aead_key_iv ha ae client_application_traffic_secret_0_ ks
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  match out <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 with
  | Core.Result.Result_Ok client_write_key_iv ->
    let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) =
      derive_aead_key_iv ha ae server_application_traffic_secret_0_ ks
    in
    let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
    (match out <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 with
      | Core.Result.Result_Ok server_write_key_iv ->
        let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8 =
          Core.Result.Result_Ok
          (client_write_key_iv, server_write_key_iv
            <:
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV))
          <:
          Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8
        in
        ks, hax_temp_output
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8)
      | Core.Result.Result_Err err ->
        ks,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8)
        <:
        (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
          Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8)
    )
  | Core.Result.Result_Err err ->
    ks,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8)
    <:
    (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
      Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV) u8)

let derive_rms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (master_secret: Bertie.Tls13keyscheduler.Key_schedule.t_Handle)
      (tx: Bertie.Tls13utils.t_Bytes)
      (ks: Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler)
     =
  let tmp0, out:(Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8) =
    Bertie.Tls13keyscheduler.Key_schedule.v_XPD ks
      (Bertie.Tls13keyscheduler.Key_schedule.TLSnames_RM
        <:
        Bertie.Tls13keyscheduler.Key_schedule.t_TLSnames)
      (mk_u8 0)
      master_secret
      true
      tx
  in
  let ks:Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler = tmp0 in
  let hax_temp_output:Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8 =
    out
  in
  ks, hax_temp_output
  <:
  (Bertie.Tls13keyscheduler.Key_schedule.t_TLSkeyscheduler &
    Core.Result.t_Result Bertie.Tls13keyscheduler.Key_schedule.t_Handle u8)
