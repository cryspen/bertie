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

let hash_empty (algorithm: Bertie.Tls13crypto.t_HashAlgorithm) =
  Bertie.Tls13crypto.impl_HashAlgorithm__hash algorithm
    (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)

let hkdf_expand_label
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label context: Bertie.Tls13utils.t_Bytes)
      (len: usize)
     =
  if len >=. mk_usize 65536
  then
    Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    let lenb:t_Array u8 (mk_usize 2) =
      Bertie.Tls13utils.u16_as_be_bytes (Bertie.Tls13utils.v_U16 (cast (len <: usize) <: u16) <: u16
        )
    in
    let tls13_label:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__from_slice (Bertie.Tls13formats.v_LABEL_TLS13
              <:
              t_Slice u8)
          <:
          Bertie.Tls13utils.t_Bytes)
        label
    in
    match
      Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw tls13_label
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    with
    | Core.Result.Result_Ok hoist96 ->
      (match
          Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw context
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok hoist95 ->
          let info:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl_Bytes__prefix (Bertie.Tls13utils.impl_Bytes__concat hoist96
                  hoist95
                <:
                Bertie.Tls13utils.t_Bytes)
              (lenb <: t_Slice u8)
          in
          Bertie.Tls13crypto.hkdf_expand hash_algorithm key info len
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let derive_secret
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label transcript_hash: Bertie.Tls13utils.t_Bytes)
     =
  hkdf_expand_label hash_algorithm
    key
    label
    transcript_hash
    (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len hash_algorithm <: usize)

let derive_binder_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13crypto.hkdf_extract ha
      k
      (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok hoist98 ->
        derive_secret ha
          early_secret
          (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_RES_BINDER <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist98
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let derive_aead_key_iv
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key: Bertie.Tls13utils.t_Bytes)
     =
  match
    hkdf_expand_label hash_algorithm
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
        hkdf_expand_label hash_algorithm
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
        Core.Result.Result_Ok
        (Bertie.Tls13crypto.impl_AeadKeyIV__new (Bertie.Tls13crypto.impl_AeadKey__new sender_write_key
                aead_algorithm
              <:
              Bertie.Tls13crypto.t_AeadKey)
            sender_write_iv)
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8

let derive_0rtt_keys
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key tx: Bertie.Tls13utils.t_Bytes)
     =
  match
    Bertie.Tls13crypto.hkdf_extract hash_algorithm
      key
      (Bertie.Tls13crypto.zero_key hash_algorithm <: Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok early_secret ->
    (match
        derive_secret hash_algorithm
          early_secret
          (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_C_E_TRAFFIC <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          tx
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok client_early_traffic_secret ->
        (match
            derive_secret hash_algorithm
              early_secret
              (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_E_EXP_MASTER <: t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok early_exporter_master_secret ->
            (match
                derive_aead_key_iv hash_algorithm aead_algoorithm client_early_traffic_secret
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
              with
              | Core.Result.Result_Ok sender_write_key_iv ->
                Core.Result.Result_Ok
                (sender_write_key_iv, early_exporter_master_secret
                  <:
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes))
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
            )
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8

let derive_finished_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes) =
  hkdf_expand_label ha
    k
    (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_FINISHED <: t_Slice u8)
      <:
      Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13utils.impl_Bytes__new () <: Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13crypto.impl_HashAlgorithm__hmac_tag_len ha <: usize)

let derive_hk_ms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (shared_secret: Bertie.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (transcript_hash: Bertie.Tls13utils.t_Bytes)
     =
  let psk:Bertie.Tls13utils.t_Bytes =
    match psko <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes with
    | Core.Option.Option_Some k ->
      Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve k
    | _ -> Bertie.Tls13crypto.zero_key ha
  in
  match
    Bertie.Tls13crypto.hkdf_extract ha
      psk
      (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
      | Core.Result.Result_Ok digest_emp ->
        (match
            derive_secret ha
              early_secret
              (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_DERIVED <: t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              digest_emp
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok derived_secret ->
            (match
                Bertie.Tls13crypto.hkdf_extract ha shared_secret derived_secret
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok handshake_secret ->
                (match
                    derive_secret ha
                      handshake_secret
                      (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_C_HS_TRAFFIC
                            <:
                            t_Slice u8)
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      transcript_hash
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok client_handshake_traffic_secret ->
                    (match
                        derive_secret ha
                          handshake_secret
                          (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_S_HS_TRAFFIC
                                <:
                                t_Slice u8)
                            <:
                            Bertie.Tls13utils.t_Bytes)
                          transcript_hash
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      with
                      | Core.Result.Result_Ok server_handshake_traffic_secret ->
                        (match
                            derive_finished_key ha client_handshake_traffic_secret
                            <:
                            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                          with
                          | Core.Result.Result_Ok client_finished_key ->
                            (match
                                derive_finished_key ha server_handshake_traffic_secret
                                <:
                                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                              with
                              | Core.Result.Result_Ok server_finished_key ->
                                (match
                                    derive_aead_key_iv ha ae client_handshake_traffic_secret
                                    <:
                                    Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
                                  with
                                  | Core.Result.Result_Ok client_write_key_iv ->
                                    (match
                                        derive_aead_key_iv ha ae server_handshake_traffic_secret
                                        <:
                                        Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
                                      with
                                      | Core.Result.Result_Ok server_write_key_iv ->
                                        (match
                                            derive_secret ha
                                              handshake_secret
                                              (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_DERIVED
                                                    <:
                                                    t_Slice u8)
                                                <:
                                                Bertie.Tls13utils.t_Bytes)
                                              digest_emp
                                            <:
                                            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                                          with
                                          | Core.Result.Result_Ok master_secret_ ->
                                            (match
                                                Bertie.Tls13crypto.hkdf_extract ha
                                                  (Bertie.Tls13crypto.zero_key ha
                                                    <:
                                                    Bertie.Tls13utils.t_Bytes)
                                                  master_secret_
                                                <:
                                                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                                              with
                                              | Core.Result.Result_Ok master_secret ->
                                                Core.Result.Result_Ok
                                                (client_write_key_iv,
                                                  server_write_key_iv,
                                                  client_finished_key,
                                                  server_finished_key,
                                                  master_secret
                                                  <:
                                                  (Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes))
                                                <:
                                                Core.Result.t_Result
                                                  (Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes) u8
                                              | Core.Result.Result_Err err ->
                                                Core.Result.Result_Err err
                                                <:
                                                Core.Result.t_Result
                                                  (Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13crypto.t_AeadKeyIV &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes &
                                                    Bertie.Tls13utils.t_Bytes) u8)
                                          | Core.Result.Result_Err err ->
                                            Core.Result.Result_Err err
                                            <:
                                            Core.Result.t_Result
                                              (Bertie.Tls13crypto.t_AeadKeyIV &
                                                Bertie.Tls13crypto.t_AeadKeyIV &
                                                Bertie.Tls13utils.t_Bytes &
                                                Bertie.Tls13utils.t_Bytes &
                                                Bertie.Tls13utils.t_Bytes) u8)
                                      | Core.Result.Result_Err err ->
                                        Core.Result.Result_Err err
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13crypto.t_AeadKeyIV &
                                            Bertie.Tls13crypto.t_AeadKeyIV &
                                            Bertie.Tls13utils.t_Bytes &
                                            Bertie.Tls13utils.t_Bytes &
                                            Bertie.Tls13utils.t_Bytes) u8)
                                  | Core.Result.Result_Err err ->
                                    Core.Result.Result_Err err
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13crypto.t_AeadKeyIV &
                                        Bertie.Tls13crypto.t_AeadKeyIV &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes) u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                                    Bertie.Tls13utils.t_Bytes &
                                    Bertie.Tls13utils.t_Bytes &
                                    Bertie.Tls13utils.t_Bytes) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                                Bertie.Tls13utils.t_Bytes &
                                Bertie.Tls13utils.t_Bytes &
                                Bertie.Tls13utils.t_Bytes) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                            Bertie.Tls13utils.t_Bytes &
                            Bertie.Tls13utils.t_Bytes &
                            Bertie.Tls13utils.t_Bytes) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes &
                        Bertie.Tls13utils.t_Bytes &
                        Bertie.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) u8

let derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
     =
  match
    derive_secret ha
      master_secret
      (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_C_AP_TRAFFIC <: t_Slice u8)
        <:
        Bertie.Tls13utils.t_Bytes)
      tx
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok client_application_traffic_secret_0_ ->
    (match
        derive_secret ha
          master_secret
          (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_S_AP_TRAFFIC <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          tx
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok server_application_traffic_secret_0_ ->
        (match
            derive_aead_key_iv ha ae client_application_traffic_secret_0_
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
          with
          | Core.Result.Result_Ok client_write_key_iv ->
            (match
                derive_aead_key_iv ha ae server_application_traffic_secret_0_
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8
              with
              | Core.Result.Result_Ok server_write_key_iv ->
                (match
                    derive_secret ha
                      master_secret
                      (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_EXP_MASTER <: t_Slice u8
                          )
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      tx
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok exporter_master_secret ->
                    Core.Result.Result_Ok
                    (client_write_key_iv, server_write_key_iv, exporter_master_secret
                      <:
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes))
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                Bertie.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
      u8

let derive_rms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
     =
  derive_secret ha
    master_secret
    (Bertie.Tls13utils.bytes (Bertie.Tls13formats.v_LABEL_RES_MASTER <: t_Slice u8)
      <:
      Bertie.Tls13utils.t_Bytes)
    tx

let algs_post_client_hello (st: t_ClientPostClientHello) = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) = st._2

let algs_post_client_finished (st: t_ClientPostClientFinished) = st._2

let compute_psk_binder_zero_rtt
      (algs0: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (tx: Bertie.Tls13formats.t_Transcript)
     =
  let
  { Bertie.Tls13crypto.f_hash = ha ;
    Bertie.Tls13crypto.f_aead = ae ;
    Bertie.Tls13crypto.f_signature = e_sa ;
    Bertie.Tls13crypto.f_kem = e_ks ;
    Bertie.Tls13crypto.f_psk_mode = psk_mode ;
    Bertie.Tls13crypto.f_zero_rtt = zero_rtt }:Bertie.Tls13crypto.t_Algorithms =
    algs0
  in
  match
    psk_mode, psk, (cast (trunc_len <: usize) <: u8)
    <:
    (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes & u8)
  with
  | true, Core.Option.Option_Some k, _ ->
    (match
        Bertie.Tls13formats.impl_Transcript__transcript_hash_without_client_hello tx ch trunc_len
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok th_trunc ->
        (match derive_binder_key ha k <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
          | Core.Result.Result_Ok mk ->
            (match
                Bertie.Tls13crypto.hmac_tag ha mk th_trunc
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok binder ->
                (match
                    Bertie.Tls13formats.set_client_hello_binder algs0
                      (Core.Option.Option_Some binder
                        <:
                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                      ch
                      (Core.Option.Option_Some trunc_len <: Core.Option.t_Option usize)
                    <:
                    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                  with
                  | Core.Result.Result_Ok nch ->
                    let tx_ch:Bertie.Tls13formats.t_Transcript =
                      Bertie.Tls13formats.impl_Transcript__add tx nch
                    in
                    if zero_rtt
                    then
                      match
                        Bertie.Tls13formats.impl_Transcript__transcript_hash tx_ch
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      with
                      | Core.Result.Result_Ok th ->
                        (match
                            derive_0rtt_keys ha ae k th
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
                          with
                          | Core.Result.Result_Ok (aek, key) ->
                            let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
                            =
                              Core.Option.Option_Some
                              (Bertie.Tls13record.client_cipher_state0 ae aek (mk_u64 0) key)
                              <:
                              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
                            in
                            Core.Result.Result_Ok
                            (nch, cipher0, tx_ch
                              <:
                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                                Bertie.Tls13formats.t_Transcript))
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                                Bertie.Tls13formats.t_Transcript) u8
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                                Bertie.Tls13formats.t_Transcript) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                            Bertie.Tls13formats.t_Transcript) u8
                    else
                      Core.Result.Result_Ok
                      (nch,
                        (Core.Option.Option_None
                          <:
                          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0),
                        tx_ch
                        <:
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                          Bertie.Tls13formats.t_Transcript))
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                          Bertie.Tls13formats.t_Transcript) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            Bertie.Tls13formats.t_Transcript) u8)
  | false, Core.Option.Option_None , Rust_primitives.Integers.MkInt 0 ->
    let tx_ch:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.impl_Transcript__add tx ch in
    Core.Result.Result_Ok
    (ch,
      (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0),
      tx_ch
      <:
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript))
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) u8
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) u8

let build_client_hello
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  let tx:Bertie.Tls13formats.t_Transcript =
    Bertie.Tls13formats.impl_Transcript__new (Bertie.Tls13crypto.impl_Algorithms__hash ciphersuite
        <:
        Bertie.Tls13crypto.t_HashAlgorithm)
  in
  let client_random:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng client_random
  in
  let rng:iimpl_447424039_ = tmp0 in
  let client_random:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
    Bertie.Tls13crypto.kem_keygen #iimpl_447424039_
      (Bertie.Tls13crypto.impl_Algorithms__kem ciphersuite <: Bertie.Tls13crypto.t_KemScheme)
      rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  match out <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 with
  | Core.Result.Result_Ok (kem_sk, kem_pk) ->
    (match
        Bertie.Tls13formats.client_hello ciphersuite
          (Core.Convert.f_into #(t_Array u8 (mk_usize 32))
              #Bertie.Tls13utils.t_Bytes
              #FStar.Tactics.Typeclasses.solve
              client_random
            <:
            Bertie.Tls13utils.t_Bytes)
          kem_pk
          sn
          tkt
        <:
        Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
      with
      | Core.Result.Result_Ok (client_hello, trunc_len) ->
        (match
            compute_psk_binder_zero_rtt ciphersuite client_hello trunc_len psk tx
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8
          with
          | Core.Result.Result_Ok (nch, cipher0, tx_ch) ->
            let hax_temp_output:Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8 =
              Core.Result.Result_Ok
              (nch,
                cipher0,
                (ClientPostClientHello
                    (Core.Convert.f_into #(t_Array u8 (mk_usize 32))
                        #Bertie.Tls13utils.t_Bytes
                        #FStar.Tactics.Typeclasses.solve
                        client_random) ciphersuite kem_sk psk tx_ch
                  <:
                  t_ClientPostClientHello)
                <:
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello))
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8
            in
            rng, hax_temp_output
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)

let put_server_hello
      (handshake: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
     =
  let ClientPostClientHello client_random ciphersuite sk psk tx:t_ClientPostClientHello = state in
  match
    Bertie.Tls13formats.parse_server_hello ciphersuite handshake
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (sr, ct) ->
    let tx:Bertie.Tls13formats.t_Transcript =
      Bertie.Tls13formats.impl_Transcript__add tx handshake
    in
    (match
        Bertie.Tls13crypto.kem_decap ciphersuite.Bertie.Tls13crypto.f_kem ct sk
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok shared_secret ->
        (match
            Bertie.Tls13formats.impl_Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok th ->
            (match
                derive_hk_ms ciphersuite.Bertie.Tls13crypto.f_hash
                  ciphersuite.Bertie.Tls13crypto.f_aead
                  shared_secret
                  psk
                  th
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok (chk, shk, cfk, sfk, ms) ->
                Core.Result.Result_Ok
                (Bertie.Tls13record.impl_DuplexCipherStateH__new chk (mk_u64 0) shk (mk_u64 0),
                  (ClientPostServerHello client_random sr ciphersuite ms cfk sfk tx
                    <:
                    t_ClientPostServerHello)
                  <:
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello))
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello)
              u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8

let put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  let
  ClientPostServerHello
    client_random
    server_random
    algorithms
    master_secret
    client_finished_key
    server_finished_key
    transcript:t_ClientPostServerHello =
    handshake_state
  in
  if ~.(Bertie.Tls13crypto.impl_Algorithms__psk_mode algorithms <: bool)
  then
    match
      Bertie.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl_Transcript__add transcript encrypted_extensions
      in
      (match
          Bertie.Tls13formats.parse_server_certificate server_certificate
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok certificate ->
          let transcript:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl_Transcript__add transcript server_certificate
          in
          (match
              Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok transcript_hash_server_certificate ->
              (match
                  Bertie.Tls13cert.verification_key_from_cert certificate
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8
                with
                | Core.Result.Result_Ok spki ->
                  (match
                      Bertie.Tls13cert.cert_public_key certificate spki
                      <:
                      Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8
                    with
                    | Core.Result.Result_Ok cert_pk ->
                      (match
                          Bertie.Tls13formats.parse_certificate_verify algorithms
                            server_certificate_verify
                          <:
                          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                        with
                        | Core.Result.Result_Ok cert_signature ->
                          let sigval:Bertie.Tls13utils.t_Bytes =
                            Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__from_slice
                                  (Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE <: t_Slice u8)
                                <:
                                Bertie.Tls13utils.t_Bytes)
                              transcript_hash_server_certificate
                          in
                          (match
                              Bertie.Tls13crypto.verify (Bertie.Tls13crypto.impl_Algorithms__signature
                                    algorithms
                                  <:
                                  Bertie.Tls13crypto.t_SignatureScheme)
                                cert_pk
                                sigval
                                cert_signature
                              <:
                              Core.Result.t_Result Prims.unit u8
                            with
                            | Core.Result.Result_Ok _ ->
                              let transcript:Bertie.Tls13formats.t_Transcript =
                                Bertie.Tls13formats.impl_Transcript__add transcript
                                  server_certificate_verify
                              in
                              Core.Result.Result_Ok
                              (ClientPostCertificateVerify client_random
                                  server_random
                                  algorithms
                                  master_secret
                                  client_finished_key
                                  server_finished_key
                                  transcript
                                <:
                                t_ClientPostCertificateVerify)
                              <:
                              Core.Result.t_Result t_ClientPostCertificateVerify u8
                            | Core.Result.Result_Err err ->
                              Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result t_ClientPostCertificateVerify u8)
                        | Core.Result.Result_Err err ->
                          Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result t_ClientPostCertificateVerify u8)
                    | Core.Result.Result_Err err ->
                      Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result t_ClientPostCertificateVerify u8)
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let put_psk_skip_server_signature
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  let
  ClientPostServerHello
    client_random
    server_random
    algorithms
    master_secret
    client_finished_key
    server_finished_key
    transcript:t_ClientPostServerHello =
    handshake_state
  in
  if Bertie.Tls13crypto.impl_Algorithms__psk_mode algorithms
  then
    match
      Bertie.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl_Transcript__add transcript encrypted_extensions
      in
      Core.Result.Result_Ok
      (ClientPostCertificateVerify client_random
          server_random
          algorithms
          master_secret
          client_finished_key
          server_finished_key
          transcript
        <:
        t_ClientPostCertificateVerify)
      <:
      Core.Result.t_Result t_ClientPostCertificateVerify u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result t_ClientPostCertificateVerify u8
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let put_server_finished
      (server_finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
     =
  let
  ClientPostCertificateVerify
    client_random
    server_random
    algorithms
    master_secret
    client_finished_key
    server_finished_key
    transcript:t_ClientPostCertificateVerify =
    handshake_state
  in
  let
  { Bertie.Tls13crypto.f_hash = hash ;
    Bertie.Tls13crypto.f_aead = aead ;
    Bertie.Tls13crypto.f_signature = signature ;
    Bertie.Tls13crypto.f_kem = kem ;
    Bertie.Tls13crypto.f_psk_mode = psk_mode ;
    Bertie.Tls13crypto.f_zero_rtt = zero_rtt }:Bertie.Tls13crypto.t_Algorithms =
    algorithms
  in
  match
    Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok transcript_hash ->
    (match
        Bertie.Tls13formats.parse_finished server_finished
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok verify_data ->
        (match
            Bertie.Tls13crypto.hmac_verify hash server_finished_key transcript_hash verify_data
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let transcript:Bertie.Tls13formats.t_Transcript =
              Bertie.Tls13formats.impl_Transcript__add transcript server_finished
            in
            (match
                Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok transcript_hash_server_finished ->
                (match
                    derive_app_keys hash aead master_secret transcript_hash_server_finished
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes) u8
                  with
                  | Core.Result.Result_Ok (cak, sak, exp) ->
                    let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
                      Bertie.Tls13record.duplex_cipher_state1 aead cak (mk_u64 0) sak (mk_u64 0) exp
                    in
                    Core.Result.Result_Ok
                    (cipher1,
                      (ClientPostServerFinished client_random
                          server_random
                          algorithms
                          master_secret
                          client_finished_key
                          transcript
                        <:
                        t_ClientPostServerFinished)
                      <:
                      (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished))
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8

let get_client_finished (handshake_state: t_ClientPostServerFinished) =
  let
  ClientPostServerFinished
    client_random
    server_random
    algorithms
    master_secret
    client_finished_key
    transcript:t_ClientPostServerFinished =
    handshake_state
  in
  match
    Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok transcript_hash ->
    (match
        Bertie.Tls13crypto.hmac_tag (Bertie.Tls13crypto.impl_Algorithms__hash algorithms
            <:
            Bertie.Tls13crypto.t_HashAlgorithm)
          client_finished_key
          transcript_hash
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok verify_data ->
        (match
            Bertie.Tls13formats.finished verify_data
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
          with
          | Core.Result.Result_Ok client_finished ->
            let transcript:Bertie.Tls13formats.t_Transcript =
              Bertie.Tls13formats.impl_Transcript__add transcript client_finished
            in
            (match
                Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok transcript_hash ->
                (match
                    derive_rms (Bertie.Tls13crypto.impl_Algorithms__hash algorithms
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                      master_secret
                      transcript_hash
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok resumption_master_secret ->
                    Core.Result.Result_Ok
                    (client_finished,
                      (ClientPostClientFinished client_random
                          server_random
                          algorithms
                          resumption_master_secret
                          transcript
                        <:
                        t_ClientPostClientFinished)
                      <:
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished))
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished)
                  u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8

let client_init
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8) =
    build_client_hello #iimpl_447424039_ algs sn tkt psk rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  let hax_temp_output:Core.Result.t_Result
    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
      t_ClientPostClientHello) u8 =
    out
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8)

let client_set_params
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
     = put_server_hello payload st

let client_finish
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  match
    Bertie.Tls13crypto.impl_Algorithms__psk_mode (algs_post_server_hello handshake_state
        <:
        Bertie.Tls13crypto.t_Algorithms)
    <:
    bool
  with
  | false ->
    (match
        Bertie.Tls13formats.Handshake_data.impl_HandshakeData__to_four payload
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData) u8
      with
      | Core.Result.Result_Ok
        (encrypted_extensions, server_certificate, server_certificate_verify, server_finished) ->
        (match
            put_server_signature encrypted_extensions
              server_certificate
              server_certificate_verify
              handshake_state
            <:
            Core.Result.t_Result t_ClientPostCertificateVerify u8
          with
          | Core.Result.Result_Ok client_state_certificate_verify ->
            (match
                put_server_finished server_finished client_state_certificate_verify
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
              with
              | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
                (match
                    get_client_finished client_state_server_finished
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8
                  with
                  | Core.Result.Result_Ok (client_finished, client_state) ->
                    Core.Result.Result_Ok
                    (client_finished, cipher, client_state
                      <:
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished))
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8)
  | true ->
    match
      Bertie.Tls13formats.Handshake_data.impl_HandshakeData__to_two payload
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData) u8
    with
    | Core.Result.Result_Ok (encrypted_extensions, server_finished) ->
      (match
          put_psk_skip_server_signature encrypted_extensions handshake_state
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8
        with
        | Core.Result.Result_Ok client_state_certificate_verify ->
          (match
              put_server_finished server_finished client_state_certificate_verify
              <:
              Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
            with
            | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
              (match
                  get_client_finished client_state_server_finished
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished
                    ) u8
                with
                | Core.Result.Result_Ok (client_finished, client_state) ->
                  Core.Result.Result_Ok
                  (client_finished, cipher, client_state
                    <:
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ClientPostClientFinished) u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ClientPostClientFinished) u8

let process_psk_binder_zero_rtt
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (th_trunc th: Bertie.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
     =
  match
    ciphersuite.Bertie.Tls13crypto.f_psk_mode, psko, bindero
    <:
    (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
  with
  | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
    (match
        derive_binder_key ciphersuite.Bertie.Tls13crypto.f_hash k
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok mk ->
        (match
            Bertie.Tls13crypto.hmac_verify ciphersuite.Bertie.Tls13crypto.f_hash mk th_trunc binder
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            if ciphersuite.Bertie.Tls13crypto.f_zero_rtt
            then
              match
                derive_0rtt_keys ciphersuite.Bertie.Tls13crypto.f_hash
                  ciphersuite.Bertie.Tls13crypto.f_aead
                  k
                  th
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok (key_iv, early_exporter_ms) ->
                let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
                  Core.Option.Option_Some
                  (Bertie.Tls13record.server_cipher_state0 key_iv (mk_u64 0) early_exporter_ms)
                  <:
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0
                in
                Core.Result.Result_Ok cipher0
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8
            else
              Core.Result.Result_Ok
              (Core.Option.Option_None
                <:
                Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
  | false, Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok
    (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8
  | _ ->
    Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8

let put_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
     =
  match
    Bertie.Tls13formats.parse_client_hello ciphersuite ch
    <:
    Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8
  with
  | Core.Result.Result_Ok (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) ->
    let tx:Bertie.Tls13formats.t_Transcript =
      Bertie.Tls13formats.impl_Transcript__new (Bertie.Tls13crypto.impl_Algorithms__hash ciphersuite
          <:
          Bertie.Tls13crypto.t_HashAlgorithm)
    in
    (match
        Bertie.Tls13formats.impl_Transcript__transcript_hash_without_client_hello tx ch trunc_len
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok th_trunc ->
        let transcript:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl_Transcript__add tx ch
        in
        (match
            Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok th ->
            (match
                Bertie.Server.lookup_db ciphersuite db sni tkto
                <:
                Core.Result.t_Result Bertie.Server.t_ServerInfo u8
              with
              | Core.Result.Result_Ok server ->
                (match
                    process_psk_binder_zero_rtt ciphersuite
                      th_trunc
                      th
                      server.Bertie.Server.f_psk_opt
                      bindero
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8
                  with
                  | Core.Result.Result_Ok cipher0 ->
                    Core.Result.Result_Ok
                    (cipher0,
                      ({
                          f_client_randomness = client_randomness;
                          f_ciphersuite = ciphersuite;
                          f_session_id = session_id;
                          f_gx = gx;
                          f_server = server;
                          f_transcript = transcript
                        }
                        <:
                        t_ServerPostClientHello)
                      <:
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello))
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                t_ServerPostClientHello) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8

let get_server_hello
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostClientHello)
      (rng: iimpl_447424039_)
     =
  let server_random:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let tmp0, tmp1:(iimpl_447424039_ & t_Array u8 (mk_usize 32)) =
    Rand_core.f_fill_bytes #iimpl_447424039_ #FStar.Tactics.Typeclasses.solve rng server_random
  in
  let rng:iimpl_447424039_ = tmp0 in
  let server_random:t_Array u8 (mk_usize 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(iimpl_447424039_ &
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
    Bertie.Tls13crypto.kem_encap #iimpl_447424039_
      state.f_ciphersuite.Bertie.Tls13crypto.f_kem
      state.f_gx
      rng
  in
  let rng:iimpl_447424039_ = tmp0 in
  match out <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 with
  | Core.Result.Result_Ok (shared_secret, gy) ->
    (match
        Bertie.Tls13formats.server_hello state.f_ciphersuite
          (Core.Convert.f_into #(t_Array u8 (mk_usize 32))
              #Bertie.Tls13utils.t_Bytes
              #FStar.Tactics.Typeclasses.solve
              server_random
            <:
            Bertie.Tls13utils.t_Bytes)
          state.f_session_id
          gy
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sh ->
        let transcript:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl_Transcript__add state.f_transcript sh
        in
        (match
            Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok transcript_hash ->
            (match
                derive_hk_ms state.f_ciphersuite.Bertie.Tls13crypto.f_hash
                  state.f_ciphersuite.Bertie.Tls13crypto.f_aead
                  shared_secret
                  state.f_server.Bertie.Server.f_psk_opt
                  transcript_hash
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok (chk, shk, cfk, sfk, ms) ->
                let hax_temp_output:Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8 =
                  Core.Result.Result_Ok
                  (sh,
                    Bertie.Tls13record.impl_DuplexCipherStateH__new shk (mk_u64 0) chk (mk_u64 0),
                    ({
                        f_client_random = state.f_client_randomness;
                        f_server_random
                        =
                        Core.Convert.f_into #(t_Array u8 (mk_usize 32))
                          #Bertie.Tls13utils.t_Bytes
                          #FStar.Tactics.Typeclasses.solve
                          server_random;
                        f_ciphersuite = state.f_ciphersuite;
                        f_server = state.f_server;
                        f_master_secret = ms;
                        f_cfk = cfk;
                        f_sfk = sfk;
                        f_transcript = transcript
                      }
                      <:
                      t_ServerPostServerHello)
                    <:
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8
                in
                rng, hax_temp_output
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)

let get_rsa_signature
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (cert sk sigval: Bertie.Tls13utils.t_Bytes)
      (rng: iimpl_447424039_)
     =
  match
    Bertie.Tls13cert.verification_key_from_cert cert
    <:
    Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
      u8
  with
  | Core.Result.Result_Ok (cert_scheme, cert_slice) ->
    (match
        Bertie.Tls13cert.rsa_public_key cert cert_slice
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8
      with
      | Core.Result.Result_Ok pk ->
        let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
          Bertie.Tls13crypto.sign_rsa #iimpl_447424039_
            sk
            pk.Bertie.Tls13crypto.f_modulus
            pk.Bertie.Tls13crypto.f_exponent
            cert_scheme
            sigval
            rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        let hax_temp_output:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = out in
        rng, hax_temp_output
        <:
        (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        rng, (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))
  | Core.Result.Result_Err err ->
    rng, (Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    <:
    (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)

let get_server_signature_no_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
     =
  match
    Bertie.Tls13formats.encrypted_extensions state.f_ciphersuite
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ee ->
    let transcript:Bertie.Tls13formats.t_Transcript =
      Bertie.Tls13formats.impl_Transcript__add state.f_transcript ee
    in
    (match
        Bertie.Tls13formats.server_certificate state.f_ciphersuite
          state.f_server.Bertie.Server.f_cert
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
      with
      | Core.Result.Result_Ok sc ->
        let transcript:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl_Transcript__add transcript sc
        in
        (match
            Bertie.Tls13formats.impl_Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok transcript_hash ->
            let sigval:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__from_slice (Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                transcript_hash
            in
            let rng, hoist101:(iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            =
              match
                Bertie.Tls13crypto.impl_Algorithms__signature state.f_ciphersuite
                <:
                Bertie.Tls13crypto.t_SignatureScheme
              with
              | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
                let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                =
                  Bertie.Tls13crypto.sign #iimpl_447424039_
                    (Bertie.Tls13crypto.impl_Algorithms__signature state.f_ciphersuite
                      <:
                      Bertie.Tls13crypto.t_SignatureScheme)
                    state.f_server.Bertie.Server.f_sk
                    sigval
                    rng
                in
                let rng:iimpl_447424039_ = tmp0 in
                rng, out <: (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
                let tmp0, out:(iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                =
                  get_rsa_signature #iimpl_447424039_
                    state.f_server.Bertie.Server.f_cert
                    state.f_server.Bertie.Server.f_sk
                    sigval
                    rng
                in
                let rng:iimpl_447424039_ = tmp0 in
                rng, out <: (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
                rng,
                (Core.Result.Result_Err Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                <:
                (iimpl_447424039_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            (match hoist101 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
              | Core.Result.Result_Ok sig ->
                (match
                    Bertie.Tls13formats.certificate_verify state.f_ciphersuite sig
                    <:
                    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                  with
                  | Core.Result.Result_Ok scv ->
                    let transcript:Bertie.Tls13formats.t_Transcript =
                      Bertie.Tls13formats.impl_Transcript__add transcript scv
                    in
                    let hax_temp_output:Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8 =
                      Core.Result.Result_Ok
                      (ee,
                        sc,
                        scv,
                        (ServerPostCertificateVerify state.f_client_random
                            state.f_server_random
                            state.f_ciphersuite
                            state.f_master_secret
                            state.f_cfk
                            state.f_sfk
                            transcript
                          <:
                          t_ServerPostCertificateVerify)
                        <:
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify))
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8
                    in
                    rng, hax_temp_output
                    <:
                    (iimpl_447424039_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                  | Core.Result.Result_Err err ->
                    rng,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (iimpl_447424039_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)

let get_server_signature
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (state: t_ServerPostServerHello)
      (rng: iimpl_447424039_)
     =
  let rng, hax_temp_output:(iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        t_ServerPostCertificateVerify) u8) =
    if ~.(Bertie.Tls13crypto.impl_Algorithms__psk_mode state.f_ciphersuite <: bool)
    then
      let tmp0, out:(iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) =
        get_server_signature_no_psk #iimpl_447424039_ state rng
      in
      let rng:iimpl_447424039_ = tmp0 in
      rng, out
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
    else
      rng,
      (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        t_ServerPostCertificateVerify) u8)

let get_skip_server_signature_no_psk (st: t_ServerPostServerHello) =
  let
  { f_client_random = cr ;
    f_server_random = sr ;
    f_ciphersuite = algs ;
    f_server = server ;
    f_master_secret = ms ;
    f_cfk = cfk ;
    f_sfk = sfk ;
    f_transcript = tx }:t_ServerPostServerHello =
    st
  in
  match
    Bertie.Tls13formats.encrypted_extensions algs
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok ee ->
    let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.impl_Transcript__add tx ee in
    Core.Result.Result_Ok
    (ee, (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
      <:
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify))
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

let get_skip_server_signature (st: t_ServerPostServerHello) =
  let
  { f_client_random = cr ;
    f_server_random = sr ;
    f_ciphersuite = algs ;
    f_server = server ;
    f_master_secret = ms ;
    f_cfk = cfk ;
    f_sfk = sfk ;
    f_transcript = tx }:t_ServerPostServerHello =
    st
  in
  if Bertie.Tls13crypto.impl_Algorithms__psk_mode algs
  then get_skip_server_signature_no_psk st
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

let get_server_finished (st: t_ServerPostCertificateVerify) =
  let ServerPostCertificateVerify cr sr algs ms cfk sfk tx:t_ServerPostCertificateVerify = st in
  let
  { Bertie.Tls13crypto.f_hash = ha ;
    Bertie.Tls13crypto.f_aead = ae ;
    Bertie.Tls13crypto.f_signature = e_sa ;
    Bertie.Tls13crypto.f_kem = e_gn ;
    Bertie.Tls13crypto.f_psk_mode = e_psk_mode ;
    Bertie.Tls13crypto.f_zero_rtt = e_zero_rtt }:Bertie.Tls13crypto.t_Algorithms =
    algs
  in
  match
    Bertie.Tls13formats.impl_Transcript__transcript_hash tx
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th_scv ->
    (match
        Bertie.Tls13crypto.hmac_tag ha sfk th_scv
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok vd ->
        (match
            Bertie.Tls13formats.finished vd
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
          with
          | Core.Result.Result_Ok sfin ->
            let tx:Bertie.Tls13formats.t_Transcript =
              Bertie.Tls13formats.impl_Transcript__add tx sfin
            in
            (match
                Bertie.Tls13formats.impl_Transcript__transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok th_sfin ->
                (match
                    derive_app_keys ha ae ms th_sfin
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                        Bertie.Tls13utils.t_Bytes) u8
                  with
                  | Core.Result.Result_Ok (cak, sak, exp) ->
                    let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
                      Bertie.Tls13record.duplex_cipher_state1 ae sak (mk_u64 0) cak (mk_u64 0) exp
                    in
                    Core.Result.Result_Ok
                    (sfin,
                      cipher1,
                      (ServerPostServerFinished cr sr algs ms cfk tx <: t_ServerPostServerFinished)
                      <:
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished))
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                        Bertie.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ServerPostServerFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8

let put_client_finished
      (cfin: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
     =
  let ServerPostServerFinished cr sr algs ms cfk tx:t_ServerPostServerFinished = st in
  match
    Bertie.Tls13formats.impl_Transcript__transcript_hash tx
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th ->
    (match
        Bertie.Tls13formats.parse_finished cfin <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok vd ->
        (match
            Bertie.Tls13crypto.hmac_verify (Bertie.Tls13crypto.impl_Algorithms__hash algs
                <:
                Bertie.Tls13crypto.t_HashAlgorithm)
              cfk
              th
              vd
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let tx:Bertie.Tls13formats.t_Transcript =
              Bertie.Tls13formats.impl_Transcript__add tx cfin
            in
            (match
                Bertie.Tls13formats.impl_Transcript__transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok th ->
                (match
                    derive_rms (Bertie.Tls13crypto.impl_Algorithms__hash algs
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                      ms
                      th
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok rms ->
                    Core.Result.Result_Ok
                    (ServerPostClientFinished cr sr algs rms tx <: t_ServerPostClientFinished)
                    <:
                    Core.Result.t_Result t_ServerPostClientFinished u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8
                )
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_ServerPostClientFinished u8

let server_init_no_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_447424039_)
     =
  match
    put_client_hello algs ch db
    <:
    Core.Result.t_Result
      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8
  with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, out:(iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello #iimpl_447424039_ st rng
    in
    let rng:iimpl_447424039_ = tmp0 in
    (match
        out
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8
      with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        let tmp0, out:(iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8) =
          get_server_signature #iimpl_447424039_ st rng
        in
        let rng:iimpl_447424039_ = tmp0 in
        (match
            out
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                t_ServerPostCertificateVerify) u8
          with
          | Core.Result.Result_Ok (ee, sc, scv, st) ->
            (match
                get_server_finished st
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8
              with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
                  Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat
                        (Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat ee sc
                          <:
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData)
                        scv
                      <:
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData)
                    sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, hax_temp_output
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init_psk
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_447424039_)
     =
  match
    put_client_hello algs ch db
    <:
    Core.Result.t_Result
      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8
  with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, out:(iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello #iimpl_447424039_ st rng
    in
    let rng:iimpl_447424039_ = tmp0 in
    (match
        out
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8
      with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        (match
            get_skip_server_signature st
            <:
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
              u8
          with
          | Core.Result.Result_Ok (ee, st) ->
            (match
                get_server_finished st
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8
              with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
                  Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat ee sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, hax_temp_output
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (iimpl_447424039_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (iimpl_447424039_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (iimpl_447424039_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (iimpl_447424039_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init
      (#iimpl_447424039_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng iimpl_447424039_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: iimpl_447424039_)
     =
  let rng, hax_temp_output:(iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
        Bertie.Tls13record.t_DuplexCipherStateH &
        Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8) =
    match Bertie.Tls13crypto.impl_Algorithms__psk_mode algs <: bool with
    | false ->
      let tmp0, out:(iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_no_psk #iimpl_447424039_ algs ch db rng
      in
      let rng:iimpl_447424039_ = tmp0 in
      rng, out
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
    | true ->
      let tmp0, out:(iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_psk #iimpl_447424039_ algs ch db rng
      in
      let rng:iimpl_447424039_ = tmp0 in
      rng, out
      <:
      (iimpl_447424039_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
  in
  rng, hax_temp_output
  <:
  (iimpl_447424039_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
        Bertie.Tls13record.t_DuplexCipherStateH &
        Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8)

let server_finish
      (cf: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
     = put_client_finished cf st
