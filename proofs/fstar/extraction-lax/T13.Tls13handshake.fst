module t13.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let hash_empty (algorithm: t13.Tls13crypto.t_HashAlgorithm) =
  t13.Tls13crypto.impl__HashAlgorithm__hash algorithm
    (t13.Tls13utils.impl__Bytes__new () <: t13.Tls13utils.t_Bytes)

let hkdf_expand_label
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (key label context: t13.Tls13utils.t_Bytes)
      (len: usize)
     =
  if len >=. sz 65536
  then
    Core.Result.Result_Err t13.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  else
    let lenb:t_Array u8 (sz 2) =
      t13.Tls13utils.u16_as_be_bytes (t13.Tls13utils.v_U16 (cast (len <: usize) <: u16) <: u16
        )
    in
    let tls13_label:t13.Tls13utils.t_Bytes =
      t13.Tls13utils.impl__Bytes__concat (t13.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                t13.Tls13formats.v_LABEL_TLS13
              <:
              t_Slice u8)
          <:
          t13.Tls13utils.t_Bytes)
        label
    in
    match
      t13.Tls13utils.encode_length_u8 (t13.Tls13utils.impl__Bytes__as_raw tls13_label
          <:
          t_Slice u8)
    with
    | Core.Result.Result_Ok hoist107 ->
      (match
          t13.Tls13utils.encode_length_u8 (t13.Tls13utils.impl__Bytes__as_raw context
              <:
              t_Slice u8)
        with
        | Core.Result.Result_Ok hoist106 ->
          let info:t13.Tls13utils.t_Bytes =
            t13.Tls13utils.impl__Bytes__prefix (t13.Tls13utils.impl__Bytes__concat hoist107
                  hoist106
                <:
                t13.Tls13utils.t_Bytes)
              (Rust_primitives.unsize lenb <: t_Slice u8)
          in
          t13.Tls13crypto.hkdf_expand hash_algorithm key info len
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8

let derive_finished_key (ha: t13.Tls13crypto.t_HashAlgorithm) (k: t13.Tls13utils.t_Bytes) =
  hkdf_expand_label ha
    k
    (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_FINISHED
          <:
          t_Slice u8)
      <:
      t13.Tls13utils.t_Bytes)
    (t13.Tls13utils.impl__Bytes__new () <: t13.Tls13utils.t_Bytes)
    (t13.Tls13crypto.impl__HashAlgorithm__hmac_tag_len ha <: usize)

let derive_secret
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (key label transcript_hash: t13.Tls13utils.t_Bytes)
     =
  hkdf_expand_label hash_algorithm
    key
    label
    transcript_hash
    (t13.Tls13crypto.impl__HashAlgorithm__hash_len hash_algorithm <: usize)

let derive_binder_key (ha: t13.Tls13crypto.t_HashAlgorithm) (k: t13.Tls13utils.t_Bytes) =
  match
    t13.Tls13crypto.hkdf_extract ha
      k
      (t13.Tls13crypto.zero_key ha <: t13.Tls13utils.t_Bytes)
  with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha with
      | Core.Result.Result_Ok hoist109 ->
        derive_secret ha
          early_secret
          (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_RES_BINDER
                <:
                t_Slice u8)
            <:
            t13.Tls13utils.t_Bytes)
          hoist109
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8

let derive_rms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (master_secret tx: t13.Tls13utils.t_Bytes)
     =
  derive_secret ha
    master_secret
    (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_RES_MASTER
          <:
          t_Slice u8)
      <:
      t13.Tls13utils.t_Bytes)
    tx

let get_rsa_signature
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (cert sk sigval: t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
     =
  match t13.Tls13cert.verification_key_from_cert cert with
  | Core.Result.Result_Ok (cert_scheme, cert_slice) ->
    (match t13.Tls13cert.rsa_public_key cert cert_slice with
      | Core.Result.Result_Ok pk ->
        let tmp0, out:(impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8) =
          t13.Tls13crypto.sign_rsa sk
            pk.t13.Tls13crypto.f_modulus
            pk.t13.Tls13crypto.f_exponent
            cert_scheme
            sigval
            rng
        in
        let rng:impl_916461611_ = tmp0 in
        let hax_temp_output:Core.Result.t_Result t13.Tls13utils.t_Bytes u8 = out in
        rng, hax_temp_output
        <:
        (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        rng, (Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
        <:
        (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8))
  | Core.Result.Result_Err err ->
    rng, (Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
    <:
    (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)

let derive_aead_key_iv
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (key: t13.Tls13utils.t_Bytes)
     =
  match
    hkdf_expand_label hash_algorithm
      key
      (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_KEY <: t_Slice u8
          )
        <:
        t13.Tls13utils.t_Bytes)
      (t13.Tls13utils.impl__Bytes__new () <: t13.Tls13utils.t_Bytes)
      (t13.Tls13crypto.impl__AeadAlgorithm__key_len aead_algorithm <: usize)
  with
  | Core.Result.Result_Ok sender_write_key ->
    (match
        hkdf_expand_label hash_algorithm
          key
          (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_IV
                <:
                t_Slice u8)
            <:
            t13.Tls13utils.t_Bytes)
          (t13.Tls13utils.impl__Bytes__new () <: t13.Tls13utils.t_Bytes)
          (t13.Tls13crypto.impl__AeadAlgorithm__iv_len aead_algorithm <: usize)
      with
      | Core.Result.Result_Ok sender_write_iv ->
        Core.Result.Result_Ok
        (t13.Tls13crypto.impl__AeadKeyIV__new (t13.Tls13crypto.impl__AeadKey__new sender_write_key
                aead_algorithm
              <:
              t13.Tls13crypto.t_AeadKey)
            sender_write_iv)
        <:
        Core.Result.t_Result t13.Tls13crypto.t_AeadKeyIV u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13crypto.t_AeadKeyIV u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13crypto.t_AeadKeyIV u8

let derive_0rtt_keys
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: t13.Tls13crypto.t_AeadAlgorithm)
      (key tx: t13.Tls13utils.t_Bytes)
     =
  match
    t13.Tls13crypto.hkdf_extract hash_algorithm
      key
      (t13.Tls13crypto.zero_key hash_algorithm <: t13.Tls13utils.t_Bytes)
  with
  | Core.Result.Result_Ok early_secret ->
    (match
        derive_secret hash_algorithm
          early_secret
          (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_C_E_TRAFFIC
                <:
                t_Slice u8)
            <:
            t13.Tls13utils.t_Bytes)
          tx
      with
      | Core.Result.Result_Ok client_early_traffic_secret ->
        (match
            derive_secret hash_algorithm
              early_secret
              (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_E_EXP_MASTER

                    <:
                    t_Slice u8)
                <:
                t13.Tls13utils.t_Bytes)
              tx
          with
          | Core.Result.Result_Ok early_exporter_master_secret ->
            (match
                derive_aead_key_iv hash_algorithm aead_algoorithm client_early_traffic_secret
              with
              | Core.Result.Result_Ok sender_write_key_iv ->
                Core.Result.Result_Ok
                (sender_write_key_iv, early_exporter_master_secret
                  <:
                  (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes))
                <:
                Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8
            )
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes) u8

let derive_app_keys
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: t13.Tls13utils.t_Bytes)
     =
  match
    derive_secret ha
      master_secret
      (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_C_AP_TRAFFIC
            <:
            t_Slice u8)
        <:
        t13.Tls13utils.t_Bytes)
      tx
  with
  | Core.Result.Result_Ok client_application_traffic_secret_0_ ->
    (match
        derive_secret ha
          master_secret
          (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_S_AP_TRAFFIC
                <:
                t_Slice u8)
            <:
            t13.Tls13utils.t_Bytes)
          tx
      with
      | Core.Result.Result_Ok server_application_traffic_secret_0_ ->
        (match derive_aead_key_iv ha ae client_application_traffic_secret_0_ with
          | Core.Result.Result_Ok client_write_key_iv ->
            (match derive_aead_key_iv ha ae server_application_traffic_secret_0_ with
              | Core.Result.Result_Ok server_write_key_iv ->
                (match
                    derive_secret ha
                      master_secret
                      (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_EXP_MASTER

                            <:
                            t_Slice u8)
                        <:
                        t13.Tls13utils.t_Bytes)
                      tx
                  with
                  | Core.Result.Result_Ok exporter_master_secret ->
                    Core.Result.Result_Ok
                    (client_write_key_iv, server_write_key_iv, exporter_master_secret
                      <:
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                    t13.Tls13utils.t_Bytes) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                t13.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
            t13.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes)
      u8

let derive_hk_ms
      (ha: t13.Tls13crypto.t_HashAlgorithm)
      (ae: t13.Tls13crypto.t_AeadAlgorithm)
      (shared_secret: t13.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (transcript_hash: t13.Tls13utils.t_Bytes)
     =
  let psk:t13.Tls13utils.t_Bytes =
    match psko with
    | Core.Option.Option_Some k -> Core.Clone.f_clone k
    | _ -> t13.Tls13crypto.zero_key ha
  in
  match
    t13.Tls13crypto.hkdf_extract ha
      psk
      (t13.Tls13crypto.zero_key ha <: t13.Tls13utils.t_Bytes)
  with
  | Core.Result.Result_Ok early_secret ->
    (match hash_empty ha with
      | Core.Result.Result_Ok digest_emp ->
        (match
            derive_secret ha
              early_secret
              (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_DERIVED
                    <:
                    t_Slice u8)
                <:
                t13.Tls13utils.t_Bytes)
              digest_emp
          with
          | Core.Result.Result_Ok derived_secret ->
            (match t13.Tls13crypto.hkdf_extract ha shared_secret derived_secret with
              | Core.Result.Result_Ok handshake_secret ->
                (match
                    derive_secret ha
                      handshake_secret
                      (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_C_HS_TRAFFIC

                            <:
                            t_Slice u8)
                        <:
                        t13.Tls13utils.t_Bytes)
                      transcript_hash
                  with
                  | Core.Result.Result_Ok client_handshake_traffic_secret ->
                    (match
                        derive_secret ha
                          handshake_secret
                          (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_S_HS_TRAFFIC

                                <:
                                t_Slice u8)
                            <:
                            t13.Tls13utils.t_Bytes)
                          transcript_hash
                      with
                      | Core.Result.Result_Ok server_handshake_traffic_secret ->
                        (match derive_finished_key ha client_handshake_traffic_secret with
                          | Core.Result.Result_Ok client_finished_key ->
                            (match derive_finished_key ha server_handshake_traffic_secret with
                              | Core.Result.Result_Ok server_finished_key ->
                                (match derive_aead_key_iv ha ae client_handshake_traffic_secret with
                                  | Core.Result.Result_Ok client_write_key_iv ->
                                    (match
                                        derive_aead_key_iv ha ae server_handshake_traffic_secret
                                      with
                                      | Core.Result.Result_Ok server_write_key_iv ->
                                        (match
                                            derive_secret ha
                                              handshake_secret
                                              (t13.Tls13utils.bytes (Rust_primitives.unsize t13.Tls13formats.v_LABEL_DERIVED

                                                    <:
                                                    t_Slice u8)
                                                <:
                                                t13.Tls13utils.t_Bytes)
                                              digest_emp
                                          with
                                          | Core.Result.Result_Ok master_secret___ ->
                                            (match
                                                t13.Tls13crypto.hkdf_extract ha
                                                  (t13.Tls13crypto.zero_key ha
                                                    <:
                                                    t13.Tls13utils.t_Bytes)
                                                  master_secret___
                                              with
                                              | Core.Result.Result_Ok master_secret ->
                                                Core.Result.Result_Ok
                                                (client_write_key_iv,
                                                  server_write_key_iv,
                                                  client_finished_key,
                                                  server_finished_key,
                                                  master_secret
                                                  <:
                                                  (t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes))
                                                <:
                                                Core.Result.t_Result
                                                  (t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes) u8
                                              | Core.Result.Result_Err err ->
                                                Core.Result.Result_Err err
                                                <:
                                                Core.Result.t_Result
                                                  (t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13crypto.t_AeadKeyIV &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes &
                                                    t13.Tls13utils.t_Bytes) u8)
                                          | Core.Result.Result_Err err ->
                                            Core.Result.Result_Err err
                                            <:
                                            Core.Result.t_Result
                                              (t13.Tls13crypto.t_AeadKeyIV &
                                                t13.Tls13crypto.t_AeadKeyIV &
                                                t13.Tls13utils.t_Bytes &
                                                t13.Tls13utils.t_Bytes &
                                                t13.Tls13utils.t_Bytes) u8)
                                      | Core.Result.Result_Err err ->
                                        Core.Result.Result_Err err
                                        <:
                                        Core.Result.t_Result
                                          (t13.Tls13crypto.t_AeadKeyIV &
                                            t13.Tls13crypto.t_AeadKeyIV &
                                            t13.Tls13utils.t_Bytes &
                                            t13.Tls13utils.t_Bytes &
                                            t13.Tls13utils.t_Bytes) u8)
                                  | Core.Result.Result_Err err ->
                                    Core.Result.Result_Err err
                                    <:
                                    Core.Result.t_Result
                                      (t13.Tls13crypto.t_AeadKeyIV &
                                        t13.Tls13crypto.t_AeadKeyIV &
                                        t13.Tls13utils.t_Bytes &
                                        t13.Tls13utils.t_Bytes &
                                        t13.Tls13utils.t_Bytes) u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                                    t13.Tls13utils.t_Bytes &
                                    t13.Tls13utils.t_Bytes &
                                    t13.Tls13utils.t_Bytes) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                                t13.Tls13utils.t_Bytes &
                                t13.Tls13utils.t_Bytes &
                                t13.Tls13utils.t_Bytes) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                            t13.Tls13utils.t_Bytes &
                            t13.Tls13utils.t_Bytes &
                            t13.Tls13utils.t_Bytes) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                        t13.Tls13utils.t_Bytes &
                        t13.Tls13utils.t_Bytes &
                        t13.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                    t13.Tls13utils.t_Bytes &
                    t13.Tls13utils.t_Bytes &
                    t13.Tls13utils.t_Bytes) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
                t13.Tls13utils.t_Bytes &
                t13.Tls13utils.t_Bytes &
                t13.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV &
            t13.Tls13utils.t_Bytes &
            t13.Tls13utils.t_Bytes &
            t13.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13crypto.t_AeadKeyIV & t13.Tls13crypto.t_AeadKeyIV & t13.Tls13utils.t_Bytes &
        t13.Tls13utils.t_Bytes &
        t13.Tls13utils.t_Bytes) u8

let algs_post_client_finished (st: t_ClientPostClientFinished) = st._2

let algs_post_client_hello (st: t_ClientPostClientHello) = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) = st._2

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
  match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
  | Core.Result.Result_Ok transcript_hash ->
    (match
        t13.Tls13crypto.hmac_tag (t13.Tls13crypto.impl__Algorithms__hash algorithms
            <:
            t13.Tls13crypto.t_HashAlgorithm)
          client_finished_key
          transcript_hash
      with
      | Core.Result.Result_Ok verify_data ->
        (match t13.Tls13formats.finished verify_data with
          | Core.Result.Result_Ok client_finished ->
            let transcript:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl__Transcript__add transcript client_finished
            in
            (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
              | Core.Result.Result_Ok transcript_hash ->
                (match
                    derive_rms (t13.Tls13crypto.impl__Algorithms__hash algorithms
                        <:
                        t13.Tls13crypto.t_HashAlgorithm)
                      master_secret
                      transcript_hash
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
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t_ClientPostClientFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished)
                  u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8

let get_server_signature_no_psk
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (state: t_ServerPostServerHello)
      (rng: impl_916461611_)
     =
  match t13.Tls13formats.encrypted_extensions state.f_ciphersuite with
  | Core.Result.Result_Ok ee ->
    let transcript:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl__Transcript__add state.f_transcript ee
    in
    (match
        t13.Tls13formats.server_certificate state.f_ciphersuite
          state.f_server.t13.Server.f_cert
      with
      | Core.Result.Result_Ok sc ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl__Transcript__add transcript sc
        in
        (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
          | Core.Result.Result_Ok transcript_hash ->
            let sigval:t13.Tls13utils.t_Bytes =
              t13.Tls13utils.impl__Bytes__concat (t13.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                        t13.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                      <:
                      t_Slice u8)
                  <:
                  t13.Tls13utils.t_Bytes)
                transcript_hash
            in
            let rng, hoist164:(impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
            =
              match t13.Tls13crypto.impl__Algorithms__signature state.f_ciphersuite with
              | t13.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
                let tmp0, out:(impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                =
                  t13.Tls13crypto.sign (t13.Tls13crypto.impl__Algorithms__signature state
                          .f_ciphersuite
                      <:
                      t13.Tls13crypto.t_SignatureScheme)
                    state.f_server.t13.Server.f_sk
                    sigval
                    rng
                in
                let rng:impl_916461611_ = tmp0 in
                rng, out <: (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
              | t13.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
                let tmp0, out:(impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                =
                  get_rsa_signature state.f_server.t13.Server.f_cert
                    state.f_server.t13.Server.f_sk
                    sigval
                    rng
                in
                let rng:impl_916461611_ = tmp0 in
                rng, out <: (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
              | t13.Tls13crypto.SignatureScheme_ED25519  ->
                rng,
                (Core.Result.Result_Err t13.Tls13utils.v_UNSUPPORTED_ALGORITHM
                  <:
                  Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                <:
                (impl_916461611_ & Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
            in
            (match hoist164 with
              | Core.Result.Result_Ok sig ->
                (match t13.Tls13formats.certificate_verify state.f_ciphersuite sig with
                  | Core.Result.Result_Ok scv ->
                    let transcript:t13.Tls13formats.t_Transcript =
                      t13.Tls13formats.impl__Transcript__add transcript scv
                    in
                    let hax_temp_output:Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13formats.Handshake_data.t_HandshakeData &
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
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8
                    in
                    rng, hax_temp_output
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                  | Core.Result.Result_Err err ->
                    rng,
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t13.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8)

let get_server_signature
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (state: t_ServerPostServerHello)
      (rng: impl_916461611_)
     =
  let rng, hax_temp_output:(impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t_ServerPostCertificateVerify) u8) =
    if ~.(t13.Tls13crypto.impl__Algorithms__psk_mode state.f_ciphersuite <: bool)
    then
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) =
        get_server_signature_no_psk state rng
      in
      let rng:impl_916461611_ = tmp0 in
      rng, out
      <:
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
    else
      rng,
      (Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
      <:
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8)
  in
  rng, hax_temp_output
  <:
  (impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
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
  match t13.Tls13formats.encrypted_extensions algs with
  | Core.Result.Result_Ok ee ->
    let tx:t13.Tls13formats.t_Transcript = t13.Tls13formats.impl__Transcript__add tx ee in
    Core.Result.Result_Ok
    (ee, (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
      <:
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify))
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

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
  if t13.Tls13crypto.impl__Algorithms__psk_mode algs
  then get_skip_server_signature_no_psk st
  else
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8

let put_client_finished
      (cfin: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
     =
  let ServerPostServerFinished cr sr algs ms cfk tx:t_ServerPostServerFinished = st in
  match t13.Tls13formats.impl__Transcript__transcript_hash tx with
  | Core.Result.Result_Ok th ->
    (match t13.Tls13formats.parse_finished cfin with
      | Core.Result.Result_Ok vd ->
        (match
            t13.Tls13crypto.hmac_verify (t13.Tls13crypto.impl__Algorithms__hash algs
                <:
                t13.Tls13crypto.t_HashAlgorithm)
              cfk
              th
              vd
          with
          | Core.Result.Result_Ok _ ->
            let tx:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl__Transcript__add tx cfin
            in
            (match t13.Tls13formats.impl__Transcript__transcript_hash tx with
              | Core.Result.Result_Ok th ->
                (match
                    derive_rms (t13.Tls13crypto.impl__Algorithms__hash algs
                        <:
                        t13.Tls13crypto.t_HashAlgorithm)
                      ms
                      th
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

let put_psk_skip_server_signature
      (encrypted_extensions: t13.Tls13formats.Handshake_data.t_HandshakeData)
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
  if t13.Tls13crypto.impl__Algorithms__psk_mode algorithms
  then
    match t13.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions with
    | Core.Result.Result_Ok _ ->
      let transcript:t13.Tls13formats.t_Transcript =
        t13.Tls13formats.impl__Transcript__add transcript encrypted_extensions
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
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          t13.Tls13formats.Handshake_data.t_HandshakeData)
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
  if ~.(t13.Tls13crypto.impl__Algorithms__psk_mode algorithms <: bool)
  then
    match t13.Tls13formats.parse_encrypted_extensions algorithms encrypted_extensions with
    | Core.Result.Result_Ok _ ->
      let transcript:t13.Tls13formats.t_Transcript =
        t13.Tls13formats.impl__Transcript__add transcript encrypted_extensions
      in
      (match t13.Tls13formats.parse_server_certificate server_certificate with
        | Core.Result.Result_Ok certificate ->
          let transcript:t13.Tls13formats.t_Transcript =
            t13.Tls13formats.impl__Transcript__add transcript server_certificate
          in
          (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
            | Core.Result.Result_Ok transcript_hash_server_certificate ->
              (match t13.Tls13cert.verification_key_from_cert certificate with
                | Core.Result.Result_Ok spki ->
                  (match t13.Tls13cert.cert_public_key certificate spki with
                    | Core.Result.Result_Ok cert_pk ->
                      (match
                          t13.Tls13formats.parse_certificate_verify algorithms
                            server_certificate_verify
                        with
                        | Core.Result.Result_Ok cert_signature ->
                          let sigval:t13.Tls13utils.t_Bytes =
                            t13.Tls13utils.impl__Bytes__concat (t13.Tls13utils.impl__Bytes__from_slice
                                  (Rust_primitives.unsize t13.Tls13formats.v_PREFIX_SERVER_SIGNATURE

                                    <:
                                    t_Slice u8)
                                <:
                                t13.Tls13utils.t_Bytes)
                              transcript_hash_server_certificate
                          in
                          (match
                              t13.Tls13crypto.verify (t13.Tls13crypto.impl__Algorithms__signature
                                    algorithms
                                  <:
                                  t13.Tls13crypto.t_SignatureScheme)
                                cert_pk
                                sigval
                                cert_signature
                            with
                            | Core.Result.Result_Ok _ ->
                              let transcript:t13.Tls13formats.t_Transcript =
                                t13.Tls13formats.impl__Transcript__add transcript
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
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result t_ClientPostCertificateVerify u8

let server_finish
      (cf: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
     = put_client_finished cf st

let get_server_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (state: t_ServerPostClientHello)
      (rng: impl_916461611_)
     =
  let server_random:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) =
    Rand_core.f_fill_bytes rng server_random
  in
  let rng:impl_916461611_ = tmp0 in
  let server_random:t_Array u8 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8) =
    t13.Tls13crypto.kem_encap state.f_ciphersuite.t13.Tls13crypto.f_kem state.f_gx rng
  in
  let rng:impl_916461611_ = tmp0 in
  match out with
  | Core.Result.Result_Ok (shared_secret, gy) ->
    (match
        t13.Tls13formats.server_hello state.f_ciphersuite
          (Core.Convert.f_into server_random <: t13.Tls13utils.t_Bytes)
          state.f_session_id
          gy
      with
      | Core.Result.Result_Ok sh ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl__Transcript__add state.f_transcript sh
        in
        (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
          | Core.Result.Result_Ok transcript_hash ->
            (match
                derive_hk_ms state.f_ciphersuite.t13.Tls13crypto.f_hash
                  state.f_ciphersuite.t13.Tls13crypto.f_aead
                  shared_secret
                  state.f_server.t13.Server.f_psk_opt
                  transcript_hash
              with
              | Core.Result.Result_Ok (chk, shk, cfk, sfk, ms) ->
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8 =
                  Core.Result.Result_Ok
                  (sh,
                    t13.Tls13record.impl__DuplexCipherStateH__new shk 0uL chk 0uL,
                    ({
                        f_client_random = state.f_client_randomness;
                        f_server_random = Core.Convert.f_into server_random;
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
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8
                in
                rng, hax_temp_output
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8)

let put_server_hello
      (handshake: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
     =
  let ClientPostClientHello client_random ciphersuite sk psk tx:t_ClientPostClientHello = state in
  match t13.Tls13formats.parse_server_hello ciphersuite handshake with
  | Core.Result.Result_Ok (sr, ct) ->
    let tx:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl__Transcript__add tx handshake
    in
    (match t13.Tls13crypto.kem_decap ciphersuite.t13.Tls13crypto.f_kem ct sk with
      | Core.Result.Result_Ok shared_secret ->
        (match t13.Tls13formats.impl__Transcript__transcript_hash tx with
          | Core.Result.Result_Ok th ->
            (match
                derive_hk_ms ciphersuite.t13.Tls13crypto.f_hash
                  ciphersuite.t13.Tls13crypto.f_aead
                  shared_secret
                  psk
                  th
              with
              | Core.Result.Result_Ok (chk, shk, cfk, sfk, ms) ->
                Core.Result.Result_Ok
                (t13.Tls13record.impl__DuplexCipherStateH__new chk 0uL shk 0uL,
                  (ClientPostServerHello client_random sr ciphersuite ms cfk sfk tx
                    <:
                    t_ClientPostServerHello)
                  <:
                  (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello))
                <:
                Core.Result.t_Result
                  (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello)
              u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t13.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8

let client_set_params
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
     = put_server_hello payload st

let compute_psk_binder_zero_rtt
      (algs0: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (tx: t13.Tls13formats.t_Transcript)
     =
  let
  { t13.Tls13crypto.f_hash = ha ;
    t13.Tls13crypto.f_aead = ae ;
    t13.Tls13crypto.f_signature = v__sa ;
    t13.Tls13crypto.f_kem = v__ks ;
    t13.Tls13crypto.f_psk_mode = psk_mode ;
    t13.Tls13crypto.f_zero_rtt = zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algs0
  in
  match
    psk_mode, psk, (cast (trunc_len <: usize) <: u8)
    <:
    (bool & Core.Option.t_Option t13.Tls13utils.t_Bytes & u8)
  with
  | true, Core.Option.Option_Some k, _ ->
    (match
        t13.Tls13formats.impl__Transcript__transcript_hash_without_client_hello tx ch trunc_len
      with
      | Core.Result.Result_Ok th_trunc ->
        (match derive_binder_key ha k with
          | Core.Result.Result_Ok mk ->
            (match t13.Tls13crypto.hmac_tag ha mk th_trunc with
              | Core.Result.Result_Ok binder ->
                (match
                    t13.Tls13formats.set_client_hello_binder algs0
                      (Core.Option.Option_Some binder
                        <:
                        Core.Option.t_Option t13.Tls13utils.t_Bytes)
                      ch
                      (Core.Option.Option_Some trunc_len <: Core.Option.t_Option usize)
                  with
                  | Core.Result.Result_Ok nch ->
                    let tx_ch:t13.Tls13formats.t_Transcript =
                      t13.Tls13formats.impl__Transcript__add tx nch
                    in
                    if zero_rtt
                    then
                      match t13.Tls13formats.impl__Transcript__transcript_hash tx_ch with
                      | Core.Result.Result_Ok th ->
                        (match derive_0rtt_keys ha ae k th with
                          | Core.Result.Result_Ok (aek, key) ->
                            let cipher0:Core.Option.t_Option t13.Tls13record.t_ClientCipherState0
                            =
                              Core.Option.Option_Some
                              (t13.Tls13record.client_cipher_state0 ae aek 0uL key)
                              <:
                              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0
                            in
                            Core.Result.Result_Ok
                            (nch, cipher0, tx_ch
                              <:
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript))
                            <:
                            Core.Result.t_Result
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript) u8
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                                t13.Tls13formats.t_Transcript) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (t13.Tls13formats.Handshake_data.t_HandshakeData &
                            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                            t13.Tls13formats.t_Transcript) u8
                    else
                      Core.Result.Result_Ok
                      (nch,
                        (Core.Option.Option_None
                          <:
                          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0),
                        tx_ch
                        <:
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                          t13.Tls13formats.t_Transcript))
                      <:
                      Core.Result.t_Result
                        (t13.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                          t13.Tls13formats.t_Transcript) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                        t13.Tls13formats.t_Transcript) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                    t13.Tls13formats.t_Transcript) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                t13.Tls13formats.t_Transcript) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
            t13.Tls13formats.t_Transcript) u8)
  | false, Core.Option.Option_None , 0uy ->
    let tx_ch:t13.Tls13formats.t_Transcript = t13.Tls13formats.impl__Transcript__add tx ch in
    Core.Result.Result_Ok
    (ch,
      (Core.Option.Option_None <: Core.Option.t_Option t13.Tls13record.t_ClientCipherState0),
      tx_ch
      <:
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13formats.t_Transcript))
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13formats.t_Transcript) u8
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t13.Tls13formats.t_Transcript) u8

let build_client_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
     =
  let tx:t13.Tls13formats.t_Transcript =
    t13.Tls13formats.impl__Transcript__new (t13.Tls13crypto.impl__Algorithms__hash ciphersuite
        <:
        t13.Tls13crypto.t_HashAlgorithm)
  in
  let client_random:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) =
    Rand_core.f_fill_bytes rng client_random
  in
  let rng:impl_916461611_ = tmp0 in
  let client_random:t_Array u8 (sz 32) = tmp1 in
  let _:Prims.unit = () in
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result (t13.Tls13utils.t_Bytes & t13.Tls13utils.t_Bytes) u8) =
    t13.Tls13crypto.kem_keygen (t13.Tls13crypto.impl__Algorithms__kem ciphersuite
        <:
        t13.Tls13crypto.t_KemScheme)
      rng
  in
  let rng:impl_916461611_ = tmp0 in
  match out with
  | Core.Result.Result_Ok (kem_sk, kem_pk) ->
    (match
        t13.Tls13formats.client_hello ciphersuite
          (Core.Convert.f_into client_random <: t13.Tls13utils.t_Bytes)
          kem_pk
          sn
          tkt
      with
      | Core.Result.Result_Ok (client_hello, trunc_len) ->
        (match compute_psk_binder_zero_rtt ciphersuite client_hello trunc_len psk tx with
          | Core.Result.Result_Ok (nch, cipher0, tx_ch) ->
            let hax_temp_output:Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8 =
              Core.Result.Result_Ok
              (nch,
                cipher0,
                (ClientPostClientHello (Core.Convert.f_into client_random)
                    ciphersuite
                    kem_sk
                    psk
                    tx_ch
                  <:
                  t_ClientPostClientHello)
                <:
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello))
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8
            in
            rng, hax_temp_output
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8)

let client_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (sn: t13.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option t13.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
     =
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8) =
    build_client_hello algs sn tkt psk rng
  in
  let rng:impl_916461611_ = tmp0 in
  let hax_temp_output:Core.Result.t_Result
    (t13.Tls13formats.Handshake_data.t_HandshakeData &
      Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
      t_ClientPostClientHello) u8 =
    out
  in
  rng, hax_temp_output
  <:
  (impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8)

let get_server_finished (st: t_ServerPostCertificateVerify) =
  let ServerPostCertificateVerify cr sr algs ms cfk sfk tx:t_ServerPostCertificateVerify = st in
  let
  { t13.Tls13crypto.f_hash = ha ;
    t13.Tls13crypto.f_aead = ae ;
    t13.Tls13crypto.f_signature = v__sa ;
    t13.Tls13crypto.f_kem = v__gn ;
    t13.Tls13crypto.f_psk_mode = v__psk_mode ;
    t13.Tls13crypto.f_zero_rtt = v__zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algs
  in
  match t13.Tls13formats.impl__Transcript__transcript_hash tx with
  | Core.Result.Result_Ok th_scv ->
    (match t13.Tls13crypto.hmac_tag ha sfk th_scv with
      | Core.Result.Result_Ok vd ->
        (match t13.Tls13formats.finished vd with
          | Core.Result.Result_Ok sfin ->
            let tx:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl__Transcript__add tx sfin
            in
            (match t13.Tls13formats.impl__Transcript__transcript_hash tx with
              | Core.Result.Result_Ok th_sfin ->
                (match derive_app_keys ha ae ms th_sfin with
                  | Core.Result.Result_Ok (cak, sak, exp) ->
                    let cipher1:t13.Tls13record.t_DuplexCipherState1 =
                      t13.Tls13record.duplex_cipher_state1 ae sak 0uL cak 0uL exp
                    in
                    Core.Result.Result_Ok
                    (sfin,
                      cipher1,
                      (ServerPostServerFinished cr sr algs ms cfk tx <: t_ServerPostServerFinished)
                      <:
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t_ServerPostServerFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData & t13.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8

let put_server_finished
      (server_finished: t13.Tls13formats.Handshake_data.t_HandshakeData)
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
  { t13.Tls13crypto.f_hash = hash ;
    t13.Tls13crypto.f_aead = aead ;
    t13.Tls13crypto.f_signature = signature ;
    t13.Tls13crypto.f_kem = kem ;
    t13.Tls13crypto.f_psk_mode = psk_mode ;
    t13.Tls13crypto.f_zero_rtt = zero_rtt }:t13.Tls13crypto.t_Algorithms =
    algorithms
  in
  match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
  | Core.Result.Result_Ok transcript_hash ->
    (match t13.Tls13formats.parse_finished server_finished with
      | Core.Result.Result_Ok verify_data ->
        (match
            t13.Tls13crypto.hmac_verify hash server_finished_key transcript_hash verify_data
          with
          | Core.Result.Result_Ok _ ->
            let transcript:t13.Tls13formats.t_Transcript =
              t13.Tls13formats.impl__Transcript__add transcript server_finished
            in
            (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
              | Core.Result.Result_Ok transcript_hash_server_finished ->
                (match derive_app_keys hash aead master_secret transcript_hash_server_finished with
                  | Core.Result.Result_Ok (cak, sak, exp) ->
                    let cipher1:t13.Tls13record.t_DuplexCipherState1 =
                      t13.Tls13record.duplex_cipher_state1 aead cak 0uL sak 0uL exp
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
                      (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t13.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8

let client_finish
      (payload: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
     =
  match
    t13.Tls13crypto.impl__Algorithms__psk_mode (algs_post_server_hello handshake_state
        <:
        t13.Tls13crypto.t_Algorithms)
  with
  | false ->
    (match t13.Tls13formats.Handshake_data.impl__HandshakeData__to_four payload with
      | Core.Result.Result_Ok
        (encrypted_extensions, server_certificate, server_certificate_verify, server_finished) ->
        (match
            put_server_signature encrypted_extensions
              server_certificate
              server_certificate_verify
              handshake_state
          with
          | Core.Result.Result_Ok client_state_certificate_verify ->
            (match put_server_finished server_finished client_state_certificate_verify with
              | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
                (match get_client_finished client_state_server_finished with
                  | Core.Result.Result_Ok (client_finished, client_state) ->
                    Core.Result.Result_Ok
                    (client_finished, cipher, client_state
                      <:
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished))
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (t13.Tls13formats.Handshake_data.t_HandshakeData &
                        t13.Tls13record.t_DuplexCipherState1 &
                        t_ClientPostClientFinished) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t13.Tls13formats.Handshake_data.t_HandshakeData &
                t13.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ClientPostClientFinished) u8)
  | true ->
    match t13.Tls13formats.Handshake_data.impl__HandshakeData__to_two payload with
    | Core.Result.Result_Ok (encrypted_extensions, server_finished) ->
      (match put_psk_skip_server_signature encrypted_extensions handshake_state with
        | Core.Result.Result_Ok client_state_certificate_verify ->
          (match put_server_finished server_finished client_state_certificate_verify with
            | Core.Result.Result_Ok (cipher, client_state_server_finished) ->
              (match get_client_finished client_state_server_finished with
                | Core.Result.Result_Ok (client_finished, client_state) ->
                  Core.Result.Result_Ok
                  (client_finished, cipher, client_state
                    <:
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ClientPostClientFinished) u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ClientPostClientFinished) u8

let process_psk_binder_zero_rtt
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (th_trunc th: t13.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option t13.Tls13utils.t_Bytes)
     =
  match
    ciphersuite.t13.Tls13crypto.f_psk_mode, psko, bindero
    <:
    (bool & Core.Option.t_Option t13.Tls13utils.t_Bytes &
      Core.Option.t_Option t13.Tls13utils.t_Bytes)
  with
  | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
    (match derive_binder_key ciphersuite.t13.Tls13crypto.f_hash k with
      | Core.Result.Result_Ok mk ->
        (match
            t13.Tls13crypto.hmac_verify ciphersuite.t13.Tls13crypto.f_hash mk th_trunc binder
          with
          | Core.Result.Result_Ok _ ->
            if ciphersuite.t13.Tls13crypto.f_zero_rtt
            then
              match
                derive_0rtt_keys ciphersuite.t13.Tls13crypto.f_hash
                  ciphersuite.t13.Tls13crypto.f_aead
                  k
                  th
              with
              | Core.Result.Result_Ok (key_iv, early_exporter_ms) ->
                let cipher0:Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 =
                  Core.Option.Option_Some
                  (t13.Tls13record.server_cipher_state0 key_iv 0uL early_exporter_ms)
                  <:
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0
                in
                Core.Result.Result_Ok cipher0
                <:
                Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                  u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
                  u8
            else
              Core.Result.Result_Ok
              (Core.Option.Option_None
                <:
                Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
              <:
              Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8)
  | false, Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok
    (Core.Option.Option_None <: Core.Option.t_Option t13.Tls13record.t_ServerCipherState0)
    <:
    Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8
  | _ ->
    Core.Result.Result_Err t13.Tls13utils.v_PSK_MODE_MISMATCH
    <:
    Core.Result.t_Result (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0) u8

let put_client_hello
      (ciphersuite: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
     =
  match t13.Tls13formats.parse_client_hello ciphersuite ch with
  | Core.Result.Result_Ok (client_randomness, session_id, sni, gx, tkto, bindero, trunc_len) ->
    let tx:t13.Tls13formats.t_Transcript =
      t13.Tls13formats.impl__Transcript__new (t13.Tls13crypto.impl__Algorithms__hash ciphersuite

          <:
          t13.Tls13crypto.t_HashAlgorithm)
    in
    (match
        t13.Tls13formats.impl__Transcript__transcript_hash_without_client_hello tx ch trunc_len
      with
      | Core.Result.Result_Ok th_trunc ->
        let transcript:t13.Tls13formats.t_Transcript =
          t13.Tls13formats.impl__Transcript__add tx ch
        in
        (match t13.Tls13formats.impl__Transcript__transcript_hash transcript with
          | Core.Result.Result_Ok th ->
            (match t13.Server.lookup_db ciphersuite db sni tkto with
              | Core.Result.Result_Ok server ->
                (match
                    process_psk_binder_zero_rtt ciphersuite
                      th_trunc
                      th
                      server.t13.Server.f_psk_opt
                      bindero
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
                      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello))
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                        t_ServerPostClientHello) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                t_ServerPostClientHello) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8

let server_init_no_psk
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
     =
  match put_client_hello algs ch db with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, out:(impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello st rng
    in
    let rng:impl_916461611_ = tmp0 in
    (match out with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        let tmp0, out:(impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8) =
          get_server_signature st rng
        in
        let rng:impl_916461611_ = tmp0 in
        (match out with
          | Core.Result.Result_Ok (ee, sc, scv, st) ->
            (match get_server_finished st with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:t13.Tls13formats.Handshake_data.t_HandshakeData =
                  t13.Tls13formats.Handshake_data.impl__HandshakeData__concat (t13.Tls13formats.Handshake_data.impl__HandshakeData__concat
                        (t13.Tls13formats.Handshake_data.impl__HandshakeData__concat ee sc
                          <:
                          t13.Tls13formats.Handshake_data.t_HandshakeData)
                        scv
                      <:
                      t13.Tls13formats.Handshake_data.t_HandshakeData)
                    sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                    t13.Tls13record.t_DuplexCipherStateH &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, hax_temp_output
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init_psk
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
     =
  match put_client_hello algs ch db with
  | Core.Result.Result_Ok (cipher0, st) ->
    let tmp0, out:(impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
      get_server_hello st rng
    in
    let rng:impl_916461611_ = tmp0 in
    (match out with
      | Core.Result.Result_Ok (sh, cipher_hs, st) ->
        (match get_skip_server_signature st with
          | Core.Result.Result_Ok (ee, st) ->
            (match get_server_finished st with
              | Core.Result.Result_Ok (sfin, cipher1, st) ->
                let flight:t13.Tls13formats.Handshake_data.t_HandshakeData =
                  t13.Tls13formats.Handshake_data.impl__HandshakeData__concat ee sfin
                in
                let hax_temp_output:Core.Result.t_Result
                  (t13.Tls13formats.Handshake_data.t_HandshakeData &
                    t13.Tls13formats.Handshake_data.t_HandshakeData &
                    Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                    t13.Tls13record.t_DuplexCipherStateH &
                    t13.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8 =
                  Core.Result.Result_Ok
                  (sh, flight, cipher0, cipher_hs, cipher1, st
                    <:
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished))
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8
                in
                rng, hax_temp_output
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
              | Core.Result.Result_Err err ->
                rng,
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (t13.Tls13formats.Handshake_data.t_HandshakeData &
                      t13.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                      t13.Tls13record.t_DuplexCipherStateH &
                      t13.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          | Core.Result.Result_Err err ->
            rng,
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (t13.Tls13formats.Handshake_data.t_HandshakeData &
                  t13.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
                  t13.Tls13record.t_DuplexCipherStateH &
                  t13.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
      | Core.Result.Result_Err err ->
        rng,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (t13.Tls13formats.Handshake_data.t_HandshakeData &
              t13.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
              t13.Tls13record.t_DuplexCipherStateH &
              t13.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
  | Core.Result.Result_Err err ->
    rng,
    (Core.Result.Result_Err err
      <:
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)
    <:
    (impl_916461611_ &
      Core.Result.t_Result
        (t13.Tls13formats.Handshake_data.t_HandshakeData &
          t13.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
          t13.Tls13record.t_DuplexCipherStateH &
          t13.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8)

let server_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: t13.Tls13crypto.t_Algorithms)
      (ch: t13.Tls13formats.Handshake_data.t_HandshakeData)
      (db: t13.Server.t_ServerDB)
      (rng: impl_916461611_)
     =
  let rng, hax_temp_output:(impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
        t13.Tls13record.t_DuplexCipherStateH &
        t13.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8) =
    match t13.Tls13crypto.impl__Algorithms__psk_mode algs with
    | false ->
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_no_psk algs ch db rng
      in
      let rng:impl_916461611_ = tmp0 in
      rng, out
      <:
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
    | true ->
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        server_init_psk algs ch db rng
      in
      let rng:impl_916461611_ = tmp0 in
      rng, out
      <:
      (impl_916461611_ &
        Core.Result.t_Result
          (t13.Tls13formats.Handshake_data.t_HandshakeData &
            t13.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
            t13.Tls13record.t_DuplexCipherStateH &
            t13.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
  in
  rng, hax_temp_output
  <:
  (impl_916461611_ &
    Core.Result.t_Result
      (t13.Tls13formats.Handshake_data.t_HandshakeData &
        t13.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option t13.Tls13record.t_ServerCipherState0 &
        t13.Tls13record.t_DuplexCipherStateH &
        t13.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8)
