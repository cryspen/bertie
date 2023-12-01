module Bertie.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let hash_empty (algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Bertie.Tls13crypto.impl__HashAlgorithm__hash algorithm
    (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)

let hkdf_expand_label
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (k label context: Bertie.Tls13utils.t_Bytes)
      (len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if len >=. sz 65536 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        let lenb:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__U16__to_be_bytes (Core.Convert.f_from (cast (len <: usize) <: u16)
              <:
              Bertie.Tls13utils.t_U16)
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
        let* hoist213:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 tls13_label
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist212:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist212)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist216:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat lenb hoist213
        in
        let* hoist215:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_u8 context
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist214:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist214)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let info:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat hoist216 hoist215
          in
          Bertie.Tls13crypto.hkdf_expand ha k info len)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let derive_finished_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label ha
    k
    (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_FINISHED
          <:
          t_Slice u8)
      <:
      Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)
    (Bertie.Tls13crypto.impl__HashAlgorithm__hmac_tag_len ha <: usize)

let derive_secret
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label hash_algorithm
    key
    label
    tx
    (Bertie.Tls13crypto.impl__HashAlgorithm__hash_len hash_algorithm <: usize)

let derive_binder_key (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* early_secret:Bertie.Tls13utils.t_Bytes
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha
                k
                (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist217:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist217)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist219:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hash_empty ha
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist218:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist218)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (derive_secret ha
          early_secret
          (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_RES_BINDER
                <:
                t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist219)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

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
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sender_write_key:Bertie.Tls13utils.t_Bytes
      =
        match
          Core.Ops.Try_trait.f_branch (hkdf_expand_label hash_algorithm
                key
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_KEY
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13crypto.impl__AeadAlgorithm__key_len aead_algorithm <: usize)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist438:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist438)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) Bertie.Tls13utils.t_Bytes
      in
      let* sender_write_iv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hkdf_expand_label hash_algorithm
                key
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_IV
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13crypto.impl__AeadAlgorithm__iv_len aead_algorithm <: usize)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist439:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist439)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13crypto.impl__AeadKeyIV__new (Bertie.Tls13crypto.impl__AeadKey__new sender_write_key
                aead_algorithm
              <:
              Bertie.Tls13crypto.t_AeadKey)
            sender_write_iv)
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        (Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8))

let derive_0rtt_keys
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (aead_algoorithm: Bertie.Tls13crypto.t_AeadAlgorithm)
      (key tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* early_secret:Bertie.Tls13utils.t_Bytes
      =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract hash_algorithm
                key
                (Bertie.Tls13crypto.zero_key hash_algorithm <: Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist440:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist440)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* client_early_traffic_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret hash_algorithm
                early_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_E_TRAFFIC

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist441:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist441)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* early_exporter_master_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret hash_algorithm
                early_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_E_EXP_MASTER

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist442:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist442)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sender_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv hash_algorithm
                aead_algoorithm
                client_early_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist443:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8
              )
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist443)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13crypto.t_AeadKeyIV
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13crypto.t_AeadKeyIV
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (sender_write_key_iv, early_exporter_master_secret
          <:
          (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) u8))

let derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* client_application_traffic_secret_0_:Bertie.Tls13utils.t_Bytes
      =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                master_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_AP_TRAFFIC

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist444:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist444)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* server_application_traffic_secret_0_:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                master_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_S_AP_TRAFFIC

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist445:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist445)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_application_traffic_secret_0_
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist446:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist446)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
      in
      let* server_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_application_traffic_secret_0_
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist447:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist447)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
      in
      let* exporter_master_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                master_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_EXP_MASTER

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist448:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist448)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
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
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes) u8))

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
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let psk:Bertie.Tls13utils.t_Bytes =
        match psko with
        | Core.Option.Option_Some k -> Core.Clone.f_clone k
        | _ -> Bertie.Tls13crypto.zero_key ha
      in
      let* early_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha
                psk
                (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist449:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist449)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* digest_emp:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hash_empty ha
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist450:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist450)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* derived_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                early_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_DERIVED
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                digest_emp
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist451:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist451)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* handshake_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha
                shared_secret
                derived_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist452:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist452)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_handshake_traffic_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                handshake_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_C_HS_TRAFFIC

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                transcript_hash
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist453:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist453)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* server_handshake_traffic_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                handshake_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_S_HS_TRAFFIC

                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                transcript_hash
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist454:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist454)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_finished_key:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_finished_key ha client_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist455:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist455)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* server_finished_key:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_finished_key ha server_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist456:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist456)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist457:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist457)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
      in
      let* server_write_key_iv:Bertie.Tls13crypto.t_AeadKeyIV =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_AeadKeyIV u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist458:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist458)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13crypto.t_AeadKeyIV
      in
      let* master_secret___:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
                handshake_secret
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_DERIVED
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                digest_emp
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist459:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist459)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* master_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha
                (Bertie.Tls13crypto.zero_key ha <: Bertie.Tls13utils.t_Bytes)
                master_secret___
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist460:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist460)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
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
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8))

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

type t_ServerPostClientHello =
  | ServerPostClientHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Server.t_ServerInfo ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostClientHello

type t_ServerPostServerFinished =
  | ServerPostServerFinished :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostServerFinished

type t_ServerPostServerHello =
  | ServerPostServerHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Server.t_ServerInfo ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostServerHello

let algs_post_client_finished (st: t_ClientPostClientFinished) : Bertie.Tls13crypto.t_Algorithms =
  st._2

let algs_post_client_hello (st: t_ClientPostClientHello) : Bertie.Tls13crypto.t_Algorithms = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) : Bertie.Tls13crypto.t_Algorithms = st._2

let get_client_finished (st: t_ClientPostServerFinished)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostServerFinished cr sr algs ms cfk tx:t_ClientPostServerFinished =
        st
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist465:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist465)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag (Bertie.Tls13crypto.impl__Algorithms__hash
                    algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                cfk
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist466:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist466)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
      in
      let* cfin:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.finished algs vd
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist467:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist467)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_HandshakeData
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx cfin in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist468:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist468)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
      in
      let* rms:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist469:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist469)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
                u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (cfin, (ClientPostClientFinished cr sr algs rms tx <: t_ClientPostClientFinished)
          <:
          (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8))

let get_server_signature
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Rand_core.t_RngCore impl_916461611_)
      (st: t_ServerPostServerHello)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
          Bertie.Tls13utils.t_HandshakeData &
          t_ServerPostCertificateVerify) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostServerHello cr sr algs server ms cfk sfk tx:t_ServerPostServerHello =
        st
      in
      let* ee:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.encrypted_extensions algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist470:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist470)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
      let* rng, hax_temp_output:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
            Bertie.Tls13utils.t_HandshakeData &
            t_ServerPostCertificateVerify) u8) =
        if ~.(Bertie.Tls13crypto.impl__Algorithms__psk_mode algs <: bool)
        then
          let* sc:Bertie.Tls13utils.t_HandshakeData =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_certificate algs
                    server.Bertie.Server.f_cert
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist471:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist471)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
          in
          let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sc in
          let* th:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist472:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist472)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
          in
          let sigval:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                      Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                    <:
                    t_Slice u8)
                <:
                Bertie.Tls13utils.t_Bytes)
              th
          in
          let* rng, sig:(impl_916461611_ & Bertie.Tls13utils.t_Bytes) =
            match Bertie.Tls13crypto.impl__Algorithms__signature algs with
            | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
              let tmp0, out:(impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
                Bertie.Tls13crypto.sign (Bertie.Tls13crypto.impl__Algorithms__signature algs
                    <:
                    Bertie.Tls13crypto.t_SignatureScheme)
                  server.Bertie.Server.f_sk
                  sigval
                  rng
              in
              let rng:impl_916461611_ = tmp0 in
              let hoist474:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = out in
              let hoist475:Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
                Core.Ops.Try_trait.f_branch hoist474
              in
              (match hoist475 with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let* hoist473:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, Rust_primitives.Hax.never_to_any hoist473
                    <:
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, v_val <: (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
            | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
              let* cert_scheme, cert_slice:(Bertie.Tls13crypto.t_SignatureScheme &
                Bertie.Tls13cert.t_CertificateKey) =
                match
                  Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert server
                          .Bertie.Server.f_cert
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
                        u8)
                with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let* hoist476:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (Rust_primitives.Hax.never_to_any hoist476)
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue v_val
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
              in
              let* pk:Bertie.Tls13crypto.t_RsaVerificationKey =
                match
                  Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.rsa_public_key server
                          .Bertie.Server.f_cert
                        cert_slice
                      <:
                      Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
                with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let* hoist477:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (Rust_primitives.Hax.never_to_any hoist477)
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8) Bertie.Tls13crypto.t_RsaVerificationKey
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue v_val
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8) Bertie.Tls13crypto.t_RsaVerificationKey
              in
              let tmp0, out:(impl_916461611_ & Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) =
                Bertie.Tls13crypto.sign_rsa server.Bertie.Server.f_sk
                  pk.Bertie.Tls13crypto.f_modulus
                  pk.Bertie.Tls13crypto.f_exponent
                  cert_scheme
                  sigval
                  rng
              in
              let rng:impl_916461611_ = tmp0 in
              let hoist479:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 = out in
              let hoist480:Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
                Core.Ops.Try_trait.f_branch hoist479
              in
              (match hoist480 with
                | Core.Ops.Control_flow.ControlFlow_Break residual ->
                  let* hoist478:Rust_primitives.Hax.t_Never =
                    Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                        (Core.Ops.Try_trait.f_from_residual residual
                          <:
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8)
                        <:
                        (impl_916461611_ &
                          Core.Result.t_Result
                            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                              Bertie.Tls13utils.t_HandshakeData &
                              t_ServerPostCertificateVerify) u8))
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, Rust_primitives.Hax.never_to_any hoist478
                    <:
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
                | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                  Core.Ops.Control_flow.ControlFlow_Continue
                  (rng, v_val <: (impl_916461611_ & Bertie.Tls13utils.t_Bytes))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
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
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
                (impl_916461611_ & Bertie.Tls13utils.t_Bytes)
          in
          let* scv:Bertie.Tls13utils.t_HandshakeData =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.certificate_verify algs sig
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist481:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist481)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx scv in
            rng,
            (Core.Result.Result_Ok
              (ee,
                sc,
                scv,
                (ServerPostCertificateVerify cr sr algs ms cfk sfk tx
                  <:
                  t_ServerPostCertificateVerify)
                <:
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify))
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
        else
          Core.Ops.Control_flow.ControlFlow_Continue
          (rng,
            (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) u8))

let get_skip_server_signature (st: t_ServerPostServerHello)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostServerHello cr sr algs server ms cfk sfk tx:t_ServerPostServerHello =
        st
      in
      if Bertie.Tls13crypto.impl__Algorithms__psk_mode algs
      then
        let* ee:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.encrypted_extensions algs
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist482:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist482)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
              Bertie.Tls13utils.t_HandshakeData
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
              Bertie.Tls13utils.t_HandshakeData
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
          Core.Result.Result_Ok
          (ee,
            (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
            <:
            (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
            u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
              u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
              u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
            u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
              u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
              u8))

let put_client_finished (cfin: Bertie.Tls13utils.t_HandshakeData) (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostServerFinished cr sr algs ms cfk tx:t_ServerPostServerFinished =
        st
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist483:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist483)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_finished algs cfin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist484:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist484)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify (Bertie.Tls13crypto.impl__Algorithms__hash
                    algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                cfk
                th
                vd
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist485:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist485)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Prims.unit
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx cfin in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist486:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist486)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* rms:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist487:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist487)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (ServerPostClientFinished cr sr algs rms tx <: t_ServerPostClientFinished)
        <:
        Core.Result.t_Result t_ServerPostClientFinished u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ServerPostClientFinished u8)
        (Core.Result.t_Result t_ServerPostClientFinished u8))

let put_psk_skip_server_signature
      (ee: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostServerHello cr sr algs ms cfk sfk tx:t_ClientPostServerHello =
        st
      in
      if Bertie.Tls13crypto.impl__Algorithms__psk_mode algs
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_encrypted_extensions algs ee
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist488:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist488)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
          Core.Result.Result_Ok
          (ClientPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ClientPostCertificateVerify)
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ClientPostCertificateVerify u8)
          (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ClientPostCertificateVerify u8)
          (Core.Result.t_Result t_ClientPostCertificateVerify u8))

let put_server_signature
      (ee sc scv: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostServerHello cr sr algs ms cfk sfk tx:t_ClientPostServerHello =
        st
      in
      if ~.(Bertie.Tls13crypto.impl__Algorithms__psk_mode algs <: bool)
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_encrypted_extensions algs ee
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist489:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist489)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
        let* cert:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_server_certificate algs sc
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist490:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist490)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sc in
        let* th_sc:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist491:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist491)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
        in
        let* spki:(Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert cert
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist492:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist492)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8)
              (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8)
              (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
        in
        let* pk:Bertie.Tls13crypto.t_PublicVerificationKey =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.cert_public_key cert spki
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist493:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist493)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8)
              Bertie.Tls13crypto.t_PublicVerificationKey
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8)
              Bertie.Tls13crypto.t_PublicVerificationKey
        in
        let* sig:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_certificate_verify algs scv
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist494:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist494)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Bertie.Tls13utils.t_Bytes
        in
        let sigval:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__from_slice (Rust_primitives.unsize
                    Bertie.Tls13formats.v_PREFIX_SERVER_SIGNATURE
                  <:
                  t_Slice u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            th_sc
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.verify (Bertie.Tls13crypto.impl__Algorithms__signature
                      algs
                    <:
                    Bertie.Tls13crypto.t_SignatureScheme)
                  pk
                  sigval
                  sig
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist495:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist495)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result t_ClientPostCertificateVerify u8) Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx scv in
          Core.Result.Result_Ok
          (ClientPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ClientPostCertificateVerify)
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ClientPostCertificateVerify u8)
          (Core.Result.t_Result t_ClientPostCertificateVerify u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result t_ClientPostCertificateVerify u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_ClientPostCertificateVerify u8)
          (Core.Result.t_Result t_ClientPostCertificateVerify u8))

let server_finish (cf: Bertie.Tls13utils.t_HandshakeData) (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 = put_client_finished cf st

let get_server_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Rand_core.t_RngCore impl_916461611_)
      (st: t_ServerPostClientHello)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostClientHello cr algs sid gx server tx:t_ServerPostClientHello =
        st
      in
      let
      { Bertie.Tls13crypto.f_hash = ha ;
        Bertie.Tls13crypto.f_aead = ae ;
        Bertie.Tls13crypto.f_signature = v__sa ;
        Bertie.Tls13crypto.f_kem = ks ;
        Bertie.Tls13crypto.f_psk_mode = v__psk_mode ;
        Bertie.Tls13crypto.f_zero_rtt = v__zero_rtt }:Bertie.Tls13crypto.t_Algorithms =
        algs
      in
      let sr:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
      let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) = Rand_core.f_fill_bytes rng sr in
      let rng:impl_916461611_ = tmp0 in
      let sr:t_Array u8 (sz 32) = tmp1 in
      let _:Prims.unit = () in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
        Bertie.Tls13crypto.kem_encap ks gx rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist497:Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
        out
      in
      let hoist498:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        Core.Ops.Try_trait.f_branch hoist497
      in
      let* shared_secret, gy:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match hoist498 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist496:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist496)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let* sh:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_hello algs
                (Core.Convert.f_into sr <: Bertie.Tls13utils.t_Bytes)
                sid
                gy
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist499:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist499)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_HandshakeData
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sh in
      let* transcript_hash:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist500:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist500)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
      in
      let* chk, shk, cfk, sfk, ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_hk_ms ha
                ae
                shared_secret
                server.Bertie.Server.f_psk_opt
                transcript_hash
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist501:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist501)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
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
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8 =
          Core.Result.Result_Ok
          (sh,
            Bertie.Tls13record.impl__DuplexCipherStateH__new shk 0uL chk 0uL,
            (ServerPostServerHello cr (Core.Convert.f_into sr) algs server ms cfk sfk tx
              <:
              t_ServerPostServerHello)
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8))

let put_server_hello (handshake: Bertie.Tls13utils.t_HandshakeData) (state: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostClientHello cr ciphersuite sk psk tx:t_ClientPostClientHello =
        state
      in
      let* sr, ct:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_server_hello ciphersuite handshake
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist502:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist502)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx handshake in
      let* shared_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_decap ciphersuite
                  .Bertie.Tls13crypto.f_kem
                ct
                sk
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist503:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist503)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist504:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist504)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* chk, shk, cfk, sfk, ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_hk_ms ciphersuite.Bertie.Tls13crypto.f_hash
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
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist505:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist505)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13record.impl__DuplexCipherStateH__new chk 0uL shk 0uL,
          (ClientPostServerHello cr sr ciphersuite ms cfk sfk tx <: t_ClientPostServerHello)
          <:
          (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello))
        <:
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
        )
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8
        ))

let client_set_params (payload: Bertie.Tls13utils.t_HandshakeData) (st: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  put_server_hello payload st

let compute_psk_binder_zero_rtt
      (algs0: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: usize)
      (psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (tx: Bertie.Tls13formats.t_Transcript)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
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
        let* th_trunc:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash_truncated_client_hello
                  tx
                  ch
                  trunc_len
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist506:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist506)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
        in
        let* mk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (derive_binder_key ha k
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist507:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist507)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
        in
        let* binder:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag ha mk th_trunc
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist508:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist508)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
        in
        let* nch:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.set_client_hello_binder algs0
                  (Core.Option.Option_Some binder <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                  ch
                  (Core.Option.Option_Some trunc_len <: Core.Option.t_Option usize)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist509:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist509)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_HandshakeData
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_HandshakeData
        in
        let tx_ch:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx nch in
        if zero_rtt
        then
          let* th:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx_ch
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist510:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist510)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8) Bertie.Tls13utils.t_Bytes
          in
          let* aek, key:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes) =
            match
              Core.Ops.Try_trait.f_branch (derive_0rtt_keys ha ae k th
                  <:
                  Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
                    u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist511:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist511)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 =
              Core.Option.Option_Some (Bertie.Tls13record.client_cipher_state0 ae aek 0uL key)
              <:
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
            in
            Core.Result.Result_Ok
            (nch, cipher0, tx_ch
              <:
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript))
            <:
            Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
        else
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (nch,
              (Core.Option.Option_None
                <:
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0),
              tx_ch
              <:
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript))
            <:
            Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
      | false, Core.Option.Option_None , 0uy ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx_ch:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ch in
          Core.Result.Result_Ok
          (ch,
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0
            ),
            tx_ch
            <:
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript) u8))

let build_client_hello
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Rand_core.t_RngCore impl_916461611_)
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let gx_len:usize =
        Bertie.Tls13crypto.impl__KemScheme__kem_priv_len (Bertie.Tls13crypto.impl__Algorithms__kem ciphersuite

            <:
            Bertie.Tls13crypto.t_KemScheme)
      in
      let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.impl__Algorithms__hash ciphersuite
            <:
            Bertie.Tls13crypto.t_HashAlgorithm)
      in
      let cr:t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
      let tmp0, tmp1:(impl_916461611_ & t_Array u8 (sz 32)) = Rand_core.f_fill_bytes rng cr in
      let rng:impl_916461611_ = tmp0 in
      let cr:t_Array u8 (sz 32) = tmp1 in
      let _:Prims.unit = () in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8) =
        Bertie.Tls13crypto.kem_keygen (Bertie.Tls13crypto.impl__Algorithms__kem ciphersuite
            <:
            Bertie.Tls13crypto.t_KemScheme)
          rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist513:Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
        out
      in
      let hoist514:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        Core.Ops.Try_trait.f_branch hoist513
      in
      let* x, gx:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match hoist514 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist512:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist512)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let* ch, trunc_len:(Bertie.Tls13utils.t_HandshakeData & usize) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.client_hello ciphersuite
                (Core.Convert.f_into cr <: Bertie.Tls13utils.t_Bytes)
                gx
                sn
                tkt
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist515:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist515)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8) (Bertie.Tls13utils.t_HandshakeData & usize)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8) (Bertie.Tls13utils.t_HandshakeData & usize)
      in
      let* nch, cipher0, tx_ch:(Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        Bertie.Tls13formats.t_Transcript) =
        match
          Core.Ops.Try_trait.f_branch (compute_psk_binder_zero_rtt ciphersuite ch trunc_len psk tx
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  Bertie.Tls13formats.t_Transcript) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist516:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist516)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                  t_ClientPostClientHello) u8)
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              Bertie.Tls13formats.t_Transcript)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hax_temp_output:Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
            t_ClientPostClientHello) u8 =
          Core.Result.Result_Ok
          (nch,
            cipher0,
            (ClientPostClientHello (Core.Convert.f_into cr) ciphersuite x psk tx_ch
              <:
              t_ClientPostClientHello)
            <:
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8
        in
        rng, hax_temp_output
        <:
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8))

let client_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Rand_core.t_RngCore impl_916461611_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          t_ClientPostClientHello) u8) =
  let tmp0, out:(impl_916461611_ &
    Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8) =
    build_client_hello algs sn tkt psk rng
  in
  let rng:impl_916461611_ = tmp0 in
  let hax_temp_output:Core.Result.t_Result
    (Bertie.Tls13utils.t_HandshakeData &
      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
      t_ClientPostClientHello) u8 =
    out
  in
  rng, hax_temp_output
  <:
  (impl_916461611_ &
    Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8)

let get_server_finished (st: t_ServerPostCertificateVerify)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
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
      let* th_scv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist532:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist532)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag ha sfk th_scv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist533:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist533)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
      in
      let* sfin:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.finished algs vd
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist534:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist534)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_HandshakeData
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sfin in
      let* th_sfin:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist535:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist535)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8) Bertie.Tls13utils.t_Bytes
      in
      let* cak, sak, exp:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_app_keys ha ae ms th_sfin
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist536:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist536)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 ae sak 0uL cak 0uL exp
        in
        Core.Result.Result_Ok
        (sfin,
          cipher1,
          (ServerPostServerFinished cr sr algs ms cfk tx <: t_ServerPostServerFinished)
          <:
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished))
        <:
        Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        (Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))

let put_server_finished
      (sfin: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostCertificateVerify)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostCertificateVerify cr sr algs ms cfk sfk tx:t_ClientPostCertificateVerify =
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
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist537:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist537)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_finished algs sfin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist538:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist538)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify ha sfk th vd
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist539:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist539)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Prims.unit
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sfin in
      let* th_sfin:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist540:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist540)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* cak, sak, exp:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_app_keys ha ae ms th_sfin
              <:
              Core.Result.t_Result
                (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist541:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist541)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13crypto.t_AeadKeyIV &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 ae cak 0uL sak 0uL exp
        in
        Core.Result.Result_Ok
        (cipher1, (ClientPostServerFinished cr sr algs ms cfk tx <: t_ClientPostServerFinished)
          <:
          (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished))
        <:
        Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
            u8)
        (Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
            u8))

let client_finish (payload: Bertie.Tls13utils.t_HandshakeData) (st: t_ClientPostServerHello)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ClientPostClientFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        Bertie.Tls13crypto.impl__Algorithms__psk_mode (algs_post_server_hello st
            <:
            Bertie.Tls13crypto.t_Algorithms)
        <:
        bool
      with
      | false ->
        let* ee, sc, scv, sfin:(Bertie.Tls13utils.t_HandshakeData &
          Bertie.Tls13utils.t_HandshakeData &
          Bertie.Tls13utils.t_HandshakeData &
          Bertie.Tls13utils.t_HandshakeData) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_handshake_messages4 payload
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist542:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist542)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData)
        in
        let* cstate_cv:t_ClientPostCertificateVerify =
          match
            Core.Ops.Try_trait.f_branch (put_server_signature ee sc scv st
                <:
                Core.Result.t_Result t_ClientPostCertificateVerify u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist543:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist543)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8) t_ClientPostCertificateVerify
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8) t_ClientPostCertificateVerify
        in
        let* cipher, cstate_fin:(Bertie.Tls13record.t_DuplexCipherState1 &
          t_ClientPostServerFinished) =
          match
            Core.Ops.Try_trait.f_branch (put_server_finished sfin cstate_cv
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist544:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist544)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
        in
        let* cfin, cstate:(Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) =
          match
            Core.Ops.Try_trait.f_branch (get_client_finished cstate_fin
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist545:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist545)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (cfin, cipher, cstate
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
      | true ->
        let* ee, sfin:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_handshake_messages2 payload
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist546:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist546)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
        in
        let* cstate_cv:t_ClientPostCertificateVerify =
          match
            Core.Ops.Try_trait.f_branch (put_psk_skip_server_signature ee st
                <:
                Core.Result.t_Result t_ClientPostCertificateVerify u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist547:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist547)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8) t_ClientPostCertificateVerify
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8) t_ClientPostCertificateVerify
        in
        let* cipher, cstate_fin:(Bertie.Tls13record.t_DuplexCipherState1 &
          t_ClientPostServerFinished) =
          match
            Core.Ops.Try_trait.f_branch (put_server_finished sfin cstate_cv
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist548:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist548)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished)
        in
        let* cfin, cstate:(Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) =
          match
            Core.Ops.Try_trait.f_branch (get_client_finished cstate_fin
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist549:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist549)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ClientPostClientFinished) u8)
              (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished)
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (cfin, cipher, cstate
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
              t_ClientPostClientFinished) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                t_ClientPostClientFinished) u8))

let process_psk_binder_zero_rtt
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (th_trunc th: Bertie.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        ciphersuite.Bertie.Tls13crypto.f_psk_mode, psko, bindero
        <:
        (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
          Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      with
      | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
        let* mk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (derive_binder_key ciphersuite.Bertie.Tls13crypto.f_hash k
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist560:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist560)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8) Bertie.Tls13utils.t_Bytes
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify ciphersuite
                    .Bertie.Tls13crypto.f_hash
                  mk
                  th_trunc
                  binder
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist561:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist561)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                  u8) Prims.unit
        in
        if ciphersuite.Bertie.Tls13crypto.f_zero_rtt
        then
          let* key_iv, early_exporter_ms:(Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes
          ) =
            match
              Core.Ops.Try_trait.f_branch (derive_0rtt_keys ciphersuite.Bertie.Tls13crypto.f_hash
                    ciphersuite.Bertie.Tls13crypto.f_aead
                    k
                    th
                  <:
                  Core.Result.t_Result (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
                    u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist562:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist562)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                    u8) (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                    u8) (Bertie.Tls13crypto.t_AeadKeyIV & Bertie.Tls13utils.t_Bytes)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
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
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
        else
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0
            )
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
      | false, Core.Option.Option_None , Core.Option.Option_None  ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
          (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8))

let put_client_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
    : Core.Result.t_Result
      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let*
      cr, sid, sni, gx, tkto, bindero, trunc_len:(Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_client_hello algs ch
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                  usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist563:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist563)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
              usize)
      in
      let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.impl__Algorithms__hash algs
            <:
            Bertie.Tls13crypto.t_HashAlgorithm)
      in
      let* th_trunc:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash_truncated_client_hello
                tx
                ch
                trunc_len
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist564:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist564)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Tls13utils.t_Bytes
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ch in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist565:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist565)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Tls13utils.t_Bytes
      in
      let* server:Bertie.Server.t_ServerInfo =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Server.lookup_db algs db sni tkto
              <:
              Core.Result.t_Result Bertie.Server.t_ServerInfo u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist566:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist566)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Server.t_ServerInfo
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8) Bertie.Server.t_ServerInfo
      in
      let* cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
        match
          Core.Ops.Try_trait.f_branch (process_psk_binder_zero_rtt algs
                th
                th_trunc
                server.Bertie.Server.f_psk_opt
                bindero
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist567:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist567)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  t_ServerPostClientHello) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (cipher0, (ServerPostClientHello cr algs sid gx server tx <: t_ServerPostClientHello)
          <:
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello))
        <:
        Core.Result.t_Result
          (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
          u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
            u8)
        (Core.Result.t_Result
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
            u8))

let server_init
      (#impl_916461611_: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Rand_core.t_CryptoRng impl_916461611_)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Rand_core.t_RngCore impl_916461611_)
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (rng: impl_916461611_)
    : (impl_916461611_ &
      Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
          Bertie.Tls13record.t_DuplexCipherStateH &
          Bertie.Tls13record.t_DuplexCipherState1 &
          t_ServerPostServerFinished) u8) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* cipher0, st:(Core.Option.t_Option
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
          let* hoist568:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist568)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
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
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
      in
      let tmp0, out:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
            t_ServerPostServerHello) u8) =
        get_server_hello st rng
      in
      let rng:impl_916461611_ = tmp0 in
      let hoist570:Core.Result.t_Result
        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) u8 =
        out
      in
      let hoist571:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8)
        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
          t_ServerPostServerHello) =
        Core.Ops.Try_trait.f_branch hoist570
      in
      let* sh, cipher_hs, st:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) =
        match hoist571 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist569:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                <:
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8))
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist569)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello)
      in
      let* rng, hax_temp_output:(impl_916461611_ &
        Core.Result.t_Result
          (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
            Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
            Bertie.Tls13record.t_DuplexCipherStateH &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) u8) =
        match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
        | false ->
          let tmp0, out:(impl_916461611_ &
            Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                t_ServerPostCertificateVerify) u8) =
            get_server_signature st rng
          in
          let rng:impl_916461611_ = tmp0 in
          let hoist573:Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) u8 =
            out
          in
          let hoist574:Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result Core.Convert.t_Infallible u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) =
            Core.Ops.Try_trait.f_branch hoist573
          in
          let* ee, sc, scv, st:(Bertie.Tls13utils.t_HandshakeData &
            Bertie.Tls13utils.t_HandshakeData &
            Bertie.Tls13utils.t_HandshakeData &
            t_ServerPostCertificateVerify) =
            match hoist574 with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist572:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist572)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify)
          in
          let* sfin, cipher1, st:(Bertie.Tls13utils.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) =
            match
              Core.Ops.Try_trait.f_branch (get_server_finished st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist575:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist575)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let flight:Bertie.Tls13utils.t_HandshakeData =
              Bertie.Tls13utils.handshake_concat ee
                (Bertie.Tls13utils.handshake_concat sc
                    (Bertie.Tls13utils.handshake_concat scv sfin
                      <:
                      Bertie.Tls13utils.t_HandshakeData)
                  <:
                  Bertie.Tls13utils.t_HandshakeData)
            in
            rng,
            (Core.Result.Result_Ok
              (sh, flight, cipher0, cipher_hs, cipher1, st
                <:
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished))
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
        | true ->
          let* ee, st:(Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) =
            match
              Core.Ops.Try_trait.f_branch (get_skip_server_signature st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist576:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist576)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify)
          in
          let* sfin, cipher1, st:(Bertie.Tls13utils.t_HandshakeData &
            Bertie.Tls13record.t_DuplexCipherState1 &
            t_ServerPostServerFinished) =
            match
              Core.Ops.Try_trait.f_branch (get_server_finished st
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist577:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (rng,
                    (Core.Ops.Try_trait.f_from_residual residual
                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8)
                    <:
                    (impl_916461611_ &
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                          Bertie.Tls13record.t_DuplexCipherStateH &
                          Bertie.Tls13record.t_DuplexCipherState1 &
                          t_ServerPostServerFinished) u8))
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist577)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (impl_916461611_ &
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished)
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let flight:Bertie.Tls13utils.t_HandshakeData =
              Bertie.Tls13utils.handshake_concat ee sfin
            in
            rng,
            (Core.Result.Result_Ok
              (sh, flight, cipher0, cipher_hs, cipher1, st
                <:
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished))
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            <:
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8))
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (impl_916461611_ &
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
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
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8)
        (impl_916461611_ &
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
              Bertie.Tls13record.t_DuplexCipherStateH &
              Bertie.Tls13record.t_DuplexCipherState1 &
              t_ServerPostServerFinished) u8))
