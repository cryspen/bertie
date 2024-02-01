module Bertie.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let hash_empty (algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Bertie.Tls13crypto.impl__HashAlgorithm__hash algorithm
    (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes)

let hkdf_expand_label
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label context: Bertie.Tls13utils.t_Bytes)
      (len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if len >=. sz 65536 <: bool
      then
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8
      else
        let lenb:t_Array u8 (sz 2) =
          Bertie.Tls13utils.u16_as_be_bytes (Bertie.Tls13utils.v_U16 (cast (len <: usize) <: u16)
              <:
              u16)
        in
        let tls13_label:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                    Bertie.Tls13formats.v_LABEL_TLS13
                  <:
                  t_Slice u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            label
        in
        let| hoist127:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    tls13_label
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| hoist126:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw
                    context
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let hoist128:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat hoist127 hoist126
          in
          let info:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__prefix hoist128
              (Rust_primitives.unsize lenb <: t_Slice u8)
          in
          Bertie.Tls13crypto.hkdf_expand hash_algorithm key info len)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let derive_finished_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label ha
    k
    (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_FINISHED
          <:
          t_Slice u8)
      <:
      Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13crypto.impl__HashAlgorithm__hmac_tag_len ha <: usize)

let derive_secret
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label transcript_hash: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label hash_algorithm
    key
    label
    transcript_hash
    (Bertie.Tls13crypto.impl__HashAlgorithm__hash_len hash_algorithm <: usize)

let derive_binder_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| early_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hkdf_extract ha
              k
              (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist129:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (hash_empty ha
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (derive_secret ha
          early_secret
          (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_RES_BINDER
                <:
                t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist129)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let derive_rms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  derive_secret ha
    master_secret
    (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_RES_MASTER
          <:
          t_Slice u8)
      <:
      Bertie.Tls13utils.t_Bytes)
    tx

let derive_aead_key_iv
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| sender_write_key:Bertie.Tls13utils.t_Bytes
      =
        Core.Result.impl__map_err (hkdf_expand_label hash_algorithm
              key
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_KEY
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13crypto.impl__AeadAlgorithm__key_len aead_algorithm <: usize)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| sender_write_iv:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (hkdf_expand_label hash_algorithm
              key
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_IV
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13utils.impl__Bytes__new () <: Bertie.Tls13utils.t_Bytes)
              (Bertie.Tls13crypto.impl__AeadAlgorithm__iv_len aead_algorithm <: usize)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (Bertie.Tls13crypto.impl__AeadKeyIV__new (Bertie.Tls13crypto.impl__AeadKey__new sender_write_key
                aead_algorithm
              <:
              Bertie.Tls13crypto.t_AeadKey)
            sender_write_iv)
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) u8)

let derive_0rtt_keys
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| early_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hkdf_extract hash_algorithm
              key
              (Bertie.Tls13crypto.zero_key hash_algorithm <: Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_early_traffic_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret hash_algorithm
              early_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_E_TRAFFIC

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| early_exporter_master_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret hash_algorithm
              early_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_E_EXP_MASTER

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| sender_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        Core.Result.impl__map_err (derive_aead_key_iv hash_algorithm
              aead_algoorithm
              client_early_traffic_secret
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (sender_write_key_iv, early_exporter_master_secret
          <:
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8) u8)

let derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| client_application_traffic_secret_0_:Bertie.Tls13utils.t_Bytes
      =
        Core.Result.impl__map_err (derive_secret ha
              master_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_AP_TRAFFIC

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server_application_traffic_secret_0_:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              master_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_S_AP_TRAFFIC

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        Core.Result.impl__map_err (derive_aead_key_iv ha ae client_application_traffic_secret_0_
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        Core.Result.impl__map_err (derive_aead_key_iv ha ae server_application_traffic_secret_0_
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| exporter_master_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              master_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_EXP_MASTER

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (client_write_key_iv, server_write_key_iv, exporter_master_secret
          <:
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes) u8) u8)

let derive_hk_ms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (shared_secret: Bertie.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (transcript_hash: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let psk:Bertie.Tls13utils.t_Bytes =
        match psko with
        | Core.Option.Option_Some k -> Core.Clone.f_clone k
        | _ -> Bertie.Tls13crypto.zero_key ha
      in
      let| early_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hkdf_extract ha
              psk
              (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| digest_emp:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (hash_empty ha
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| derived_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              early_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_DERIVED
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              digest_emp
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| handshake_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hkdf_extract ha shared_secret derived_secret
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_handshake_traffic_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              handshake_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_HS_TRAFFIC

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              transcript_hash
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server_handshake_traffic_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              handshake_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_S_HS_TRAFFIC

                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              transcript_hash
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_finished_key:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_finished_key ha client_handshake_traffic_secret
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server_finished_key:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_finished_key ha server_handshake_traffic_secret
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        Core.Result.impl__map_err (derive_aead_key_iv ha ae client_handshake_traffic_secret
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        Core.Result.impl__map_err (derive_aead_key_iv ha ae server_handshake_traffic_secret
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| master_secret___:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_secret ha
              handshake_secret
              (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_DERIVED
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              digest_emp
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| master_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hkdf_extract ha
              (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
              master_secret___
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (client_write_key_iv,
          server_write_key_iv,
          client_finished_key,
          server_finished_key,
          master_secret
          <:
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8) u8)

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

type t_ClientPostClientFinished =
  | ClientPostClientFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostClientFinished

type t_ClientPostClientHello =
  | ClientPostClientHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostClientHello

type t_ClientPostServerFinished =
  | ClientPostServerFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ClientPostServerFinished

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

type t_ServerPostClientFinished =
  | ServerPostClientFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostClientFinished

type t_ServerPostClientHello = {
  f_client_randomness:Bertie.Tls13utils.t_Bytes;
  f_ciphersuite:Bertie.Tls13crypto.t_Algorithms;
  f_session_id:Bertie.Tls13utils.t_Bytes;
  f_gx:Bertie.Tls13utils.t_Bytes;
  f_server:Bertie.Server.t_ServerInfo;
  f_transcript:Bertie.Tls13formats.t_Transcript
}

type t_ServerPostServerFinished =
  | ServerPostServerFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostServerFinished

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

let algs_post_client_finished (st: t_ClientPostClientFinished) : Bertie.Tls13crypto.t_Algorithms =
  st._2

let algs_post_client_hello (st: t_ClientPostClientHello) : Bertie.Tls13crypto.t_Algorithms = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) : Bertie.Tls13crypto.t_Algorithms = st._2

let get_client_finished (handshake_state: t_ClientPostServerFinished)
    : Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
      ClientPostServerFinished
        client_random
        server_random
        algorithms
        master_secret
        client_finished_key
        transcript:t_ClientPostServerFinished =
        handshake_state
      in
      let| transcript_hash:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| verify_data:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_tag (Bertie.Tls13crypto.impl__Algorithms__hash
                  algorithms
                <:
                Bertie.Tls13crypto.t_HashAlgorithm)
              client_finished_key
              transcript_hash
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| client_finished:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        Core.Result.impl__map_err (Bertie.Tls13formats.finished verify_data
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add transcript client_finished
      in
      let| transcript_hash:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| resumption_master_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash algorithms
                <:
                Bertie.Tls13crypto.t_HashAlgorithm)
              master_secret
              transcript_hash
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (client_finished,
          (ClientPostClientFinished client_random
              server_random
              algorithms
              resumption_master_secret
              transcript
            <:
            t_ClientPostClientFinished)
          <:
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished))
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8) u8
    )

let get_server_signature
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (state: t_ServerPostServerHello)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          t_ServerPostCertificateVerify) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! ee:Bertie.Tls13formats.Handshake_data.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.encrypted_extensions state.f_ciphersuite
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist188:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist188)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add state.f_transcript ee
      in
      let! rng, hax_temp_output:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) =
        if ~.(Bertie.Tls13crypto.impl__Algorithms__psk_mode state.f_ciphersuite <: bool)
        then
          let! sc:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_certificate state
                      .f_ciphersuite
                    state.f_server.Bertie.Server.f_cert
                  <:
                  Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist189:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist189)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                Bertie.Tls13formats.Handshake_data.t_HandshakeData
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                Bertie.Tls13formats.Handshake_data.t_HandshakeData
          in
          let transcript:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl__Transcript__add transcript sc
          in
          let! transcript_hash:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript

                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist190:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist190)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
          in
          let sigval:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                      Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              transcript_hash
          in
          let! rng, sig:(impl_916461611_ & Bertie.Tls13utils.t_Bytes) =
            match Bertie.Tls13crypto.impl__Algorithms__signature state.f_ciphersuite with
            | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
              let tmp0, out:(impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
                Bertie.Tls13crypto.sign (Bertie.Tls13crypto.impl__Algorithms__signature state
                        .f_ciphersuite
                    <:
                    Bertie.Tls13crypto.t_SignatureScheme)
                  state.f_server.Bertie.Server.f_sk
                  sigval
                  rng
              in
              let rng:impl_916461611_ = tmp0 in
              let hoist192:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = out in
              let hoist193:Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
                Core.Ops.Try_trait.f_branch hoist192
              in
              (match hoist193 with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let! hoist191:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, Rust_primitives.Hax.never_to_any hoist191
                    <:
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, v_val <: (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
            | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
              let! cert_scheme, cert_slice:(Bertie.Tls13crypto.t_SignatureScheme &
                Bertie.Tls13cert.t_CertificateKey) =
                match
                  Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert state
                          .f_server
                          .Bertie.Server.f_cert
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
                        u8)
                with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let! hoist194:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (Rust_primitives.Hax.never_to_any hoist194)
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue v_val
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
              in
              let! pk:Bertie.Tls13crypto.t_RsaVerificationKey =
                match
                  Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.rsa_public_key state.f_server
                          .Bertie.Server.f_cert
                        cert_slice
                      <:
                      Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
                with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let! hoist195:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (Rust_primitives.Hax.never_to_any hoist195)
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8) Bertie.Tls13crypto.t_RsaVerificationKey
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue v_val
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8) Bertie.Tls13crypto.t_RsaVerificationKey
              in
              let tmp0, out:(impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
                Bertie.Tls13crypto.sign_rsa state.f_server.Bertie.Server.f_sk
                  pk.Bertie.Tls13crypto.f_modulus
                  pk.Bertie.Tls13crypto.f_exponent
                  cert_scheme
                  sigval
                  rng
              in
              let rng:impl_916461611_ = tmp0 in
              let hoist197:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = out in
              let hoist198:Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
                Core.Ops.Try_trait.f_branch hoist197
              in
              (match hoist198 with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let! hoist196:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, Rust_primitives.Hax.never_to_any hoist196
                    <:
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, v_val <: (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
            | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
              Core.Ops.Control_flow.ControlFlow_Continue
              (rng,
                Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
                    <:
                    Rust_primitives.Hax.t_Never)
                <:
                (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
          in
          let! scv:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.certificate_verify state
                      .f_ciphersuite
                    sig
                  <:
                  Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist199:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist199)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                Bertie.Tls13formats.Handshake_data.t_HandshakeData
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                Bertie.Tls13formats.Handshake_data.t_HandshakeData
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let transcript:Bertie.Tls13formats.t_Transcript =
              Bertie.Tls13formats.impl__Transcript__add transcript scv
            in
            rng,
            (Core.Result.Result_Ok
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
                  t_ServerPostCertificateVerify) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
        else
          Core.Ops.Control_flow.ControlFlow_Continue
          (rng,
            (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))

let get_skip_server_signature (st: t_ServerPostServerHello)
    : Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
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
      if Bertie.Tls13crypto.impl__Algorithms__psk_mode algs
      then
        let| ee:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
          Core.Result.impl__map_err (Bertie.Tls13formats.encrypted_extensions algs
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let tx:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl__Transcript__add tx ee
          in
          Core.Result.Result_Ok
          (ee,
            (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify))
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
              u8) u8
      else
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
              u8) u8)

let put_client_finished
      (cfin: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
      ServerPostServerFinished cr sr algs ms cfk tx:t_ServerPostServerFinished =
        st
      in
      let| th:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| vd:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.parse_finished cfin
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_verify (Bertie.Tls13crypto.impl__Algorithms__hash
                  algs
                <:
                Bertie.Tls13crypto.t_HashAlgorithm)
              cfk
              th
              vd
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.impl__Transcript__add tx cfin in
      let| th:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| rms:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash algs
                <:
                Bertie.Tls13crypto.t_HashAlgorithm)
              ms
              th
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (ServerPostClientFinished cr sr algs rms tx <: t_ServerPostClientFinished)
        <:
        Core.Result.t_Result t_ServerPostClientFinished u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result t_ServerPostClientFinished u8) u8)

let put_psk_skip_server_signature
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
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
      if Bertie.Tls13crypto.impl__Algorithms__psk_mode algorithms
      then
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13formats.parse_encrypted_extensions algorithms
                encrypted_extensions
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let transcript:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl__Transcript__add transcript encrypted_extensions
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
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_ClientPostCertificateVerify u8) u8
      else
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_ClientPostCertificateVerify u8) u8)

let put_server_signature
      (encrypted_extensions server_certificate server_certificate_verify:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
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
      if ~.(Bertie.Tls13crypto.impl__Algorithms__psk_mode algorithms <: bool)
      then
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13formats.parse_encrypted_extensions algorithms
                encrypted_extensions
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let transcript:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl__Transcript__add transcript encrypted_extensions
        in
        let| certificate:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13formats.parse_server_certificate server_certificate
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let transcript:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl__Transcript__add transcript server_certificate
        in
        let| transcript_hash_server_certificate:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript

              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| spki:(Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) =
          Core.Result.impl__map_err (Bertie.Tls13cert.verification_key_from_cert certificate
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| cert_pk:Bertie.Tls13crypto.t_PublicVerificationKey =
          Core.Result.impl__map_err (Bertie.Tls13cert.cert_public_key certificate spki
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| cert_signature:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13formats.parse_certificate_verify algorithms
                server_certificate_verify
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let sigval:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                    Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                  <:
                  t_Slice u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            transcript_hash_server_certificate
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13crypto.verify (Bertie.Tls13crypto.impl__Algorithms__signature
                    algorithms
                  <:
                  Bertie.Tls13crypto.t_SignatureScheme)
                cert_pk
                sigval
                cert_signature
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let transcript:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl__Transcript__add transcript server_certificate_verify
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
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_ClientPostCertificateVerify u8) u8
      else
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result t_ClientPostCertificateVerify u8) u8)

let server_finish
      (cf: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 = put_client_finished cf st

let get_server_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (state: t_ServerPostClientHello)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let server_random:t_Array u8 (sz 32) =
        Rust_primitives.Hax.repeat 0uy (sz 32)
      in
      let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) =
        Rand_core.f_fill_bytes rng server_random
      in
      let rng:impl_916461611_ = tmp0 in
      let server_random:t_Array u8 (sz 32) = tmp1 in
      let _:Prims.unit = () in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
        Bertie.Tls13crypto.kem_encap state.f_ciphersuite.Bertie.Tls13crypto.f_kem state.f_gx rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist201:Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
        out
      in
      let hoist202:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        Core.Ops.Try_trait.f_branch hoist201
      in
      let! shared_secret, gy:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match hoist202 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist200:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist200)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let! sh:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_hello state.f_ciphersuite
                (Core.Convert.f_into server_random <: Bertie.Tls13utils.t_Bytes)
                state.f_session_id
                gy
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist203:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist203)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13formats.Handshake_data.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13formats.Handshake_data.t_HandshakeData
      in
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add state.f_transcript sh
      in
      let! transcript_hash:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript

              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist204:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist204)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
      in
      let! chk, shk, cfk, sfk, ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_hk_ms state.f_ciphersuite.Bertie.Tls13crypto.f_hash
                state.f_ciphersuite.Bertie.Tls13crypto.f_aead
                shared_secret
                state.f_server.Bertie.Server.f_psk_opt
                transcript_hash
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist205:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist205)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8 =
          Core.Result.Result_Ok
          (sh,
            Bertie.Tls13record.impl__DuplexCipherStateH__new shk 0uL chk 0uL,
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
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))

let put_server_hello
      (handshake: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (state: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
      ClientPostClientHello client_random ciphersuite sk psk tx:t_ClientPostClientHello =
        state
      in
      let| sr, ct:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        Core.Result.impl__map_err (Bertie.Tls13formats.parse_server_hello ciphersuite handshake
            <:
            Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add tx handshake
      in
      let| shared_secret:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.kem_decap ciphersuite.Bertie.Tls13crypto.f_kem
              ct
              sk
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| th:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| chk, shk, cfk, sfk, ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) =
        Core.Result.impl__map_err (derive_hk_ms ciphersuite.Bertie.Tls13crypto.f_hash
              ciphersuite.Bertie.Tls13crypto.f_aead
              shared_secret
              psk
              th
            <:
            Core.Result.t_Result
              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (Bertie.Tls13record.impl__DuplexCipherStateH__new chk 0uL shk 0uL,
          (ClientPostServerHello client_random sr ciphersuite ms cfk sfk tx
            <:
            t_ClientPostServerHello)
          <:
          (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello))
        <:
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
        ) u8)

let client_set_params
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (st: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  put_server_hello payload st

let compute_psk_binder_zero_rtt
      (algs0: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (tx: Bertie.Tls13formats.t_Transcript)
    : Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
      { Bertie.Tls13crypto.f_hash = ha ;
        Bertie.Tls13crypto.f_aead = ae ;
        Bertie.Tls13crypto.f_signature = v__sa ;
        Bertie.Tls13crypto.f_kem = v__ks ;
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
        let| th_trunc:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash_without_client_hello
                tx
                ch
                trunc_len
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| mk:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (derive_binder_key ha k
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| binder:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_tag ha mk th_trunc
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| nch:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
          Core.Result.impl__map_err (Bertie.Tls13formats.set_client_hello_binder algs0
                (Core.Option.Option_Some binder <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                ch
                (Core.Option.Option_Some trunc_len <: Core.Option.t_Option usize)
              <:
              Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let tx_ch:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.impl__Transcript__add tx nch
        in
        if zero_rtt
        then
          let| th:Bertie.Tls13utils.t_Bytes =
            Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx_ch
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              (Core.Convert.f_from <: u8 -> u8)
          in
          let| aek, key:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) =
            Core.Result.impl__map_err (derive_0rtt_keys ha ae k th
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 =
              Core.Option.Option_Some (Bertie.Tls13record.client_cipher_state0 ae aek 0uL key)
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
                Bertie.Tls13formats.t_Transcript) u8)
          <:
          Core.Result.t_Result
            (Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8) u8
        else
          Core.Result.Result_Ok
          (Core.Result.Result_Ok
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
                Bertie.Tls13formats.t_Transcript) u8)
          <:
          Core.Result.t_Result
            (Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8) u8
      | false, Core.Option.Option_None , 0uy ->
        Core.Result.Result_Ok
        (let tx_ch:Bertie.Tls13formats.t_Transcript =
            Bertie.Tls13formats.impl__Transcript__add tx ch
          in
          Core.Result.Result_Ok
          (ch,
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
            ),
            tx_ch
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript))
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8) u8
      | _ ->
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8) u8)

let build_client_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__new (Bertie.Tls13crypto.impl__Algorithms__hash ciphersuite

            <:
            Bertie.Tls13crypto.t_HashAlgorithm)
      in
      let client_random:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
      let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) =
        Rand_core.f_fill_bytes rng client_random
      in
      let rng:impl_916461611_ = tmp0 in
      let client_random:t_Array u8 (sz 32) = tmp1 in
      let _:Prims.unit = () in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
        Bertie.Tls13crypto.kem_keygen (Bertie.Tls13crypto.impl__Algorithms__kem ciphersuite
            <:
            Bertie.Tls13crypto.t_KemScheme)
          rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist207:Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
        out
      in
      let hoist208:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        Core.Ops.Try_trait.f_branch hoist207
      in
      let! kem_sk, kem_pk:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match hoist208 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist206:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist206)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let! client_hello, trunc_len:(Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.client_hello ciphersuite
                (Core.Convert.f_into client_random <: Bertie.Tls13utils.t_Bytes)
                kem_pk
                sn
                tkt
              <:
              Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist209:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist209)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
      in
      let! nch, cipher0, tx_ch:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) =
        match
          Core.Ops.Try_trait.f_branch (compute_psk_binder_zero_rtt ciphersuite
                client_hello
                trunc_len
                psk
                tx
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist210:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist210)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8 =
          Core.Result.Result_Ok
          (nch,
            cipher0,
            (ClientPostClientHello (Core.Convert.f_into client_random) ciphersuite kem_sk psk tx_ch
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
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))

let client_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8) =
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8) =
    build_client_hello algs sn tkt psk rng
  in
  let rng:impl_916461611_ = tmp0 in
  let hax_temp_output:Core.Result.t_Result
    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
      t_ClientPostClientHello) u8 =
    out
  in
  rng, hax_temp_output
  <:
  (impl_916461611_ &
    Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8)

let get_server_finished (st: t_ServerPostCertificateVerify)
    : Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
      ServerPostCertificateVerify cr sr algs ms cfk sfk tx:t_ServerPostCertificateVerify =
        st
      in
      let
      { Bertie.Tls13crypto.f_hash = ha ;
        Bertie.Tls13crypto.f_aead = ae ;
        Bertie.Tls13crypto.f_signature = v__sa ;
        Bertie.Tls13crypto.f_kem = v__gn ;
        Bertie.Tls13crypto.f_psk_mode = v__psk_mode ;
        Bertie.Tls13crypto.f_zero_rtt = v__zero_rtt }:Bertie.Tls13crypto.t_Algorithms =
        algs
      in
      let| th_scv:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| vd:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_tag ha sfk th_scv
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| sfin:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
        Core.Result.impl__map_err (Bertie.Tls13formats.finished vd
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.impl__Transcript__add tx sfin in
      let| th_sfin:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash tx
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| cak, sak, exp:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes) =
        Core.Result.impl__map_err (derive_app_keys ha ae ms th_sfin
            <:
            Core.Result.t_Result
              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 ae sak 0uL cak 0uL exp
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
            t_ServerPostServerFinished) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8) u8)

let put_server_finished
      (server_finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostCertificateVerify)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let
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
      let| transcript_hash:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| verify_data:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.parse_finished server_finished
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_verify hash
              server_finished_key
              transcript_hash
              verify_data
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add transcript server_finished
      in
      let| transcript_hash_server_finished:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| cak, sak, exp:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes) =
        Core.Result.impl__map_err (derive_app_keys hash
              aead
              master_secret
              transcript_hash_server_finished
            <:
            Core.Result.t_Result
              (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                Bertie.Tls13utils.t_Bytes) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 aead cak 0uL sak 0uL exp
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
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
            u8) u8)

let client_finish
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (handshake_state: t_ClientPostServerHello)
    : Core.Result.t_Result
      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ClientPostClientFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (match
        Bertie.Tls13crypto.impl__Algorithms__psk_mode (algs_post_server_hello handshake_state
            <:
            Bertie.Tls13crypto.t_Algorithms)
        <:
        bool
      with
      | false ->
        let| encrypted_extensions, server_certificate, server_certificate_verify, server_finished:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
          Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__to_four
                payload
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| client_state_certificate_verify:t_ClientPostCertificateVerify =
          Core.Result.impl__map_err (put_server_signature encrypted_extensions
                server_certificate
                server_certificate_verify
                handshake_state
              <:
              Core.Result.t_Result t_ClientPostCertificateVerify u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| cipher, client_state_server_finished:(Bertie.Tls13record.t_DuplexCipherState1 &
          t_ClientPostServerFinished) =
          Core.Result.impl__map_err (put_server_finished server_finished
                client_state_certificate_verify
              <:
              Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| client_finished, client_state:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          t_ClientPostClientFinished) =
          Core.Result.impl__map_err (get_client_finished client_state_server_finished
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8
            )
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok
          (client_finished, cipher, client_state
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished))
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8) u8
      | true ->
        let| encrypted_extensions, server_finished:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
          Core.Result.impl__map_err (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__to_two payload

              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| client_state_certificate_verify:t_ClientPostCertificateVerify =
          Core.Result.impl__map_err (put_psk_skip_server_signature encrypted_extensions
                handshake_state
              <:
              Core.Result.t_Result t_ClientPostCertificateVerify u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| cipher, client_state_server_finished:(Bertie.Tls13record.t_DuplexCipherState1 &
          t_ClientPostServerFinished) =
          Core.Result.impl__map_err (put_server_finished server_finished
                client_state_certificate_verify
              <:
              Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| client_finished, client_state:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          t_ClientPostClientFinished) =
          Core.Result.impl__map_err (get_client_finished client_state_server_finished
              <:
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ClientPostClientFinished) u8
            )
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok
          (client_finished, cipher, client_state
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished))
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8) u8)

let process_psk_binder_zero_rtt
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (th_trunc th: Bertie.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (match
        ciphersuite.Bertie.Tls13crypto.f_psk_mode, psko, bindero
        <:
        (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
          Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      with
      | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
        let| mk:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (derive_binder_key ciphersuite.Bertie.Tls13crypto.f_hash k
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        let| _:Prims.unit =
          Core.Result.impl__map_err (Bertie.Tls13crypto.hmac_verify ciphersuite
                  .Bertie.Tls13crypto.f_hash
                mk
                th_trunc
                binder
              <:
              Core.Result.t_Result Prims.unit u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        if ciphersuite.Bertie.Tls13crypto.f_zero_rtt
        then
          let| key_iv, early_exporter_ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes
          ) =
            Core.Result.impl__map_err (derive_0rtt_keys ciphersuite.Bertie.Tls13crypto.f_hash
                  ciphersuite.Bertie.Tls13crypto.f_aead
                  k
                  th
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
              (Core.Convert.f_from <: u8 -> u8)
          in
          Core.Result.Result_Ok
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
              Core.Option.Option_Some
              (Bertie.Tls13record.server_cipher_state0 key_iv 0uL early_exporter_ms)
              <:
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0
            in
            Core.Result.Result_Ok cipher0
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          <:
          Core.Result.t_Result
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            u8
        else
          Core.Result.Result_Ok
          (Core.Result.Result_Ok
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0
            )
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          <:
          Core.Result.t_Result
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            u8
      | false, Core.Option.Option_None , Core.Option.Option_None  ->
        Core.Result.Result_Ok
        (Core.Result.Result_Ok
          (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          u8
      | _ ->
        Core.Result.Result_Ok
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
        <:
        Core.Result.t_Result
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          u8)

let put_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
    : Core.Result.t_Result
      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let|
      client_randomness, session_id, sni, gx, tkto, bindero, trunc_len:(Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) =
        Core.Result.impl__map_err (Bertie.Tls13formats.parse_client_hello ciphersuite ch
            <:
            Core.Result.t_Result
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__new (Bertie.Tls13crypto.impl__Algorithms__hash ciphersuite

            <:
            Bertie.Tls13crypto.t_HashAlgorithm)
      in
      let| th_trunc:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash_without_client_hello
              tx
              ch
              trunc_len
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let transcript:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.impl__Transcript__add tx ch
      in
      let| th:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13formats.impl__Transcript__transcript_hash transcript
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| server:Bertie.Server.t_ServerInfo =
        Core.Result.impl__map_err (Bertie.Server.lookup_db ciphersuite db sni tkto
            <:
            Core.Result.t_Result Bertie.Server.t_ServerInfo u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
        Core.Result.impl__map_err (process_psk_binder_zero_rtt ciphersuite
              th
              th_trunc
              server.Bertie.Server.f_psk_opt
              bindero
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
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
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello))
        <:
        Core.Result.t_Result
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
            u8) u8)

let server_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Rand_core.t_RngCore impl_916461611_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! cipher0, st:(Core.Option.t_Option
        Bertie.Tls13record.t_ServerCipherState0 &
        t_ServerPostClientHello) =
        match
          Core.Ops.Try_trait.f_branch (put_client_hello algs ch db
              <:
              Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist215:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist215)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
      in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8) =
        get_server_hello st rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist217:Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8 =
        out
      in
      let hoist218:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
          Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) =
        Core.Ops.Try_trait.f_branch hoist217
      in
      let! sh, cipher_hs, st:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
        Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) =
        match hoist218 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let! hoist216:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist216)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello)
      in
      let! rng, hax_temp_output:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
        | false ->
          let tmp0, out:(impl_916461611_ &
            Core.Result.t_Result
              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                t_ServerPostCertificateVerify) u8) =
            get_server_signature st rng
          in
          let rng:impl_916461611_ = tmp0 in
          let hoist220:Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) u8 =
            out
          in
          let hoist221:Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Core.Convert.t_Infallible u8)
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              t_ServerPostCertificateVerify) =
            Core.Ops.Try_trait.f_branch hoist220
          in
          let! ee, sc, scv, st:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) =
            match hoist221 with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist219:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist219)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  t_ServerPostCertificateVerify)
          in
          let! sfin, cipher1, st:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) =
            match
              Core.Ops.Try_trait.f_branch (get_server_finished st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist222:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist222)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let flight:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
              Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat
                    (Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat ee sc
                      <:
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData)
                    scv
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData)
                sfin
            in
            rng,
            (Core.Result.Result_Ok
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
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
        | true ->
          let! ee, st:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            t_ServerPostCertificateVerify) =
            match
              Core.Ops.Try_trait.f_branch (get_skip_server_signature st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist223:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist223)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_ServerPostCertificateVerify)
          in
          let! sfin, cipher1, st:(Bertie.Tls13formats.Handshake_data.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) =
            match
              Core.Ops.Try_trait.f_branch (get_server_finished st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let! hoist224:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist224)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let flight:Bertie.Tls13formats.Handshake_data.t_HandshakeData =
              Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat ee sfin
            in
            rng,
            (Core.Result.Result_Ok
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
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Bertie.Tls13formats.Handshake_data.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
