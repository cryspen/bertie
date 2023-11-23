module Bertie.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let hash_empty (ha: Bertie.Tls13crypto.t_HashAlgorithm)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Bertie.Tls13crypto.hash ha (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)

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
        let* hoist186:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 tls13_label
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist185:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist185)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              Bertie.Tls13utils.t_Bytes
        in
        let hoist189:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat lenb hoist186
        in
        let* hoist188:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 context
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist187:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist187)
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
            Bertie.Tls13utils.impl__Bytes__concat hoist189 hoist188
          in
          Bertie.Tls13crypto.hkdf_expand ha k info len)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let derive_aead_key_iv
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (k: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* sender_write_key:Bertie.Tls13utils.t_Bytes
      =
        match
          Core.Ops.Try_trait.f_branch (hkdf_expand_label ha
                k
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_KEY
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13crypto.ae_key_len ae <: usize)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist190:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist190)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* sender_write_iv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hkdf_expand_label ha
                k
                (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_IV
                      <:
                      t_Slice u8)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__new <: Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13crypto.ae_iv_len ae <: usize)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist191:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist191)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (sender_write_key, sender_write_iv
          <:
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8))

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
    (Bertie.Tls13crypto.hmac_tag_len ha <: usize)

let derive_secret (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k label tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label ha k label tx (Bertie.Tls13crypto.hash_len ha <: usize)

let derive_0rtt_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (k tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes) u8 =
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
          let* hoist192:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist192)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_early_traffic_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
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
          let* hoist193:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist193)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
      in
      let* early_exporter_master_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_secret ha
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
          let* hoist194:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist194)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) Bertie.Tls13utils.t_Bytes
      in
      let* sender_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_early_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist195:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist195)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                ) u8) (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (sender_write_key_iv, early_exporter_master_secret
          <:
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes) u8
        )
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes) u8
        ))

let derive_app_keys
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (master_secret tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        Bertie.Tls13utils.t_Bytes) u8 =
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
          let* hoist196:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist196)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist197:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist197)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_application_traffic_secret_0_
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist198:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist198)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let* server_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_application_traffic_secret_0_
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist199:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist199)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
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
          let* hoist200:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist200)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (client_write_key_iv, server_write_key_iv, exporter_master_secret
          <:
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes) u8))

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
          let* hoist201:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist201)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            Bertie.Tls13utils.t_Bytes
      in
      let* hoist203:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hash_empty ha
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist202:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist202)
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
          hoist203)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

let derive_hk_ms
      (ha: Bertie.Tls13crypto.t_HashAlgorithm)
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (gxy: Bertie.Tls13utils.t_Bytes)
      (psko: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        Bertie.Tls13utils.t_Bytes &
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
          let* hoist204:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist204)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist205:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist205)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist206:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist206)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* handshake_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha gxy derived_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist207:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist207)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist208:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist208)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
                tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist209:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist209)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist210:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist210)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist211:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist211)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
      in
      let* client_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_handshake_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist212:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist212)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
      in
      let* server_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_handshake_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist213:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist213)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
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
          let* hoist214:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist214)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          let* hoist215:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist215)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8) Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result
          ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8)
        (Core.Result.t_Result
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes) u8))

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

let process_psk_binder_zero_rtt
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (th_trunc th: Bertie.Tls13utils.t_Bytes)
      (psko bindero: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      Bertie.Tls13crypto.Algorithms ha ae v__sa v__ks psk_mode zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
        algs
      in
      match
        psk_mode, psko, bindero
        <:
        (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
          Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      with
      | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
        let* mk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (derive_binder_key ha k
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist333:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist333)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify ha mk th_trunc binder
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist334:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist334)
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
        if zero_rtt
        then
          let* aek, key:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes) =
            match
              Core.Ops.Try_trait.f_branch (derive_0rtt_keys ha ae k th
                  <:
                  Core.Result.t_Result
                    ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                      Bertie.Tls13utils.t_Bytes) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist335:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist335)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                    u8)
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                )
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0)
                    u8)
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                )
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
              Core.Option.Option_Some (Bertie.Tls13record.server_cipher_state0 ae aek 0uL key)
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
      Bertie.Tls13crypto.Algorithms ha ae v__sa v__ks psk_mode zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
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
            let* hoist460:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist460)
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
            let* hoist461:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist461)
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
            let* hoist462:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist462)
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
            let* hoist463:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist463)
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
              let* hoist464:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist464)
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
          let* aek, key:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
            Bertie.Tls13utils.t_Bytes) =
            match
              Core.Ops.Try_trait.f_branch (derive_0rtt_keys ha ae k th
                  <:
                  Core.Result.t_Result
                    ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                      Bertie.Tls13utils.t_Bytes) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist465:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist465)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                )
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) & Bertie.Tls13utils.t_Bytes
                )
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
          let* hoist470:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist470)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag (Bertie.Tls13crypto.impl__Algorithms__hash_alg
                    algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                cfk
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist471:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist471)
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
          let* hoist472:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist472)
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
          let* hoist473:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist473)
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
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash_alg algs

                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist474:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist474)
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

let get_client_hello
      (algs0: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let gx_len:usize =
        Bertie.Tls13crypto.kem_priv_len (Bertie.Tls13crypto.impl__Algorithms__kem_alg algs0
            <:
            Bertie.Tls13crypto.t_KemScheme)
      in
      if (Bertie.Tls13utils.impl__Bytes__len ent <: usize) <. (sz 32 +! gx_len <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_INSUFFICIENT_ENTROPY
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8)
      else
        let tx:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.impl__Algorithms__hash_alg algs0
              <:
              Bertie.Tls13crypto.t_HashAlgorithm)
        in
        let cr:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice_range ent
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 32 }
              <:
              Core.Ops.Range.t_Range usize)
        in
        let* x, gx:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_keygen (Bertie.Tls13crypto.impl__Algorithms__kem_alg
                      algs0
                    <:
                    Bertie.Tls13crypto.t_KemScheme)
                  (Bertie.Tls13utils.impl__Bytes__slice_range ent
                      ({
                          Core.Ops.Range.f_start = sz 32;
                          Core.Ops.Range.f_end = sz 32 +! gx_len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist475:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist475)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    t_ClientPostClientHello) u8)
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    t_ClientPostClientHello) u8)
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        in
        let* ch, trunc_len:(Bertie.Tls13utils.t_HandshakeData & usize) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.client_hello algs0 cr gx sn tkt
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist476:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist476)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    t_ClientPostClientHello) u8) (Bertie.Tls13utils.t_HandshakeData & usize)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    t_ClientPostClientHello) u8) (Bertie.Tls13utils.t_HandshakeData & usize)
        in
        let* nch, cipher0, tx_ch:(Bertie.Tls13utils.t_HandshakeData &
          Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
          Bertie.Tls13formats.t_Transcript) =
          match
            Core.Ops.Try_trait.f_branch (compute_psk_binder_zero_rtt algs0 ch trunc_len psk tx
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    Bertie.Tls13formats.t_Transcript) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist477:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist477)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                    t_ClientPostClientHello) u8)
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                Bertie.Tls13formats.t_Transcript)
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (nch, cipher0, (ClientPostClientHello cr algs0 x psk tx_ch <: t_ClientPostClientHello)
            <:
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData &
              Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
              t_ClientPostClientHello) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                t_ClientPostClientHello) u8))

let client_init
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8 = get_client_hello algs sn tkt psk ent

let get_server_finished (st: t_ServerPostCertificateVerify)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostCertificateVerify cr sr algs ms cfk sfk tx:t_ServerPostCertificateVerify =
        st
      in
      let Bertie.Tls13crypto.Algorithms ha ae v__sa v__gn v__psk_mode v__zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
        algs
      in
      let* th_scv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist480:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist480)
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
          let* hoist481:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist481)
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
          let* hoist482:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist482)
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
          let* hoist483:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist483)
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
      let* cak, sak, exp:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_app_keys ha ae ms th_sfin
              <:
              Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist484:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist484)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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

let get_server_hello (st: t_ServerPostClientHello) (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostClientHello cr algs sid gx server tx:t_ServerPostClientHello =
        st
      in
      let Bertie.Tls13crypto.Algorithms ha ae v__sa ks v__psk_mode v__zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
        algs
      in
      if
        (Bertie.Tls13utils.impl__Bytes__len ent <: usize) <.
        (sz 32 +! (Bertie.Tls13crypto.kem_priv_len ks <: usize) <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_INSUFFICIENT_ENTROPY
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                t_ServerPostServerHello) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                t_ServerPostServerHello) u8)
      else
        let sr:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice_range ent
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 32 }
              <:
              Core.Ops.Range.t_Range usize)
        in
        let* gxy, gy:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_encap ks
                  gx
                  (Bertie.Tls13utils.impl__Bytes__slice_range ent
                      ({
                          Core.Ops.Range.f_start = sz 32;
                          Core.Ops.Range.f_end
                          =
                          sz 32 +! (Bertie.Tls13crypto.kem_priv_len ks <: usize) <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist485:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist485)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8)
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8)
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
        in
        let* sh:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_hello algs sr sid gy
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist486:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist486)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8) Bertie.Tls13utils.t_HandshakeData
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8) Bertie.Tls13utils.t_HandshakeData
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sh in
        let* th:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist487:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist487)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8) Bertie.Tls13utils.t_Bytes
        in
        let* chk, shk, cfk, sfk, ms:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
          Bertie.Tls13utils.t_Bytes &
          Bertie.Tls13utils.t_Bytes &
          Bertie.Tls13utils.t_Bytes) =
          match
            Core.Ops.Try_trait.f_branch (derive_hk_ms ha ae gxy server.Bertie.Server.f_psk_opt th
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist488:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist488)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8)
              ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                    t_ServerPostServerHello) u8)
              ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes)
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (sh,
            Bertie.Tls13record.duplex_cipher_state_hs ae shk 0uL chk 0uL,
            (ServerPostServerHello cr sr algs server ms cfk sfk tx <: t_ServerPostServerHello)
            <:
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello))
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                t_ServerPostServerHello) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                t_ServerPostServerHello) u8))

let get_server_signature (st: t_ServerPostServerHello) (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData &
        t_ServerPostCertificateVerify) u8 =
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
          let* hoist489:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist489)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Bertie.Tls13utils.t_HandshakeData &
                  t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
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
            let* hoist490:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist490)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
            let* hoist491:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist491)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
        let* sig:Bertie.Tls13utils.t_Bytes =
          match Bertie.Tls13crypto.impl__Algorithms__sig_alg algs with
          | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
            (match
                Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.sign (Bertie.Tls13crypto.impl__Algorithms__sig_alg
                          algs
                        <:
                        Bertie.Tls13crypto.t_SignatureScheme)
                      server.Bertie.Server.f_sk
                      server.Bertie.Server.f_cert
                      sigval
                      ent
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist492:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist492)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes)
          | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
            let* cert_scheme, cert_slice:(Bertie.Tls13crypto.t_SignatureScheme &
              Bertie.Tls13cert.t_CertificateKey) =
              match
                Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert server
                        .Bertie.Server.f_cert
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist493:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist493)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8)
                  (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8)
                  (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey)
            in
            let* pk_modulus, pk_exponent:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
              match
                Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.rsa_public_key server
                        .Bertie.Server.f_cert
                      cert_slice
                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist494:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist494)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8)
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8)
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
            in
            (match
                Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.sign_rsa server.Bertie.Server.f_sk
                      pk_modulus
                      pk_exponent
                      cert_scheme
                      sigval
                      ent
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist495:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result
                        (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                          Bertie.Tls13utils.t_HandshakeData &
                          t_ServerPostCertificateVerify) u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist495)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                        Bertie.Tls13utils.t_HandshakeData &
                        t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes)
          | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
            Core.Ops.Control_flow.ControlFlow_Continue
            (Rust_primitives.Hax.never_to_any (Core.Panicking.panic "not implemented"
                  <:
                  Rust_primitives.Hax.t_Never))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_Bytes
        in
        let* scv:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.certificate_verify algs sig
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist496:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist496)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8) Bertie.Tls13utils.t_HandshakeData
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx scv in
          Core.Result.Result_Ok
          (ee,
            sc,
            scv,
            (ServerPostCertificateVerify cr sr algs ms cfk sfk tx <: t_ServerPostCertificateVerify)
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
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                t_ServerPostCertificateVerify) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                t_ServerPostCertificateVerify) u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH
          <:
          Core.Result.t_Result
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
              Bertie.Tls13utils.t_HandshakeData &
              t_ServerPostCertificateVerify) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Bertie.Tls13utils.t_HandshakeData &
                t_ServerPostCertificateVerify) u8)
          (Core.Result.t_Result
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
            let* hoist497:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist497)
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
          let* hoist498:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist498)
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
          let* hoist499:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist499)
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
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify (Bertie.Tls13crypto.impl__Algorithms__hash_alg
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
          let* hoist500:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist500)
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
          let* hoist501:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist501)
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
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.impl__Algorithms__hash_alg algs

                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist502:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist502)
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
          let* hoist503:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist503)
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
        Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.impl__Algorithms__hash_alg algs
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
          let* hoist504:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist504)
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
          let* hoist505:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist505)
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
          let* hoist506:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist506)
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
          let* hoist507:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist507)
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
            let* hoist508:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist508)
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

let put_server_finished
      (sfin: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostCertificateVerify)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostCertificateVerify cr sr algs ms cfk sfk tx:t_ClientPostCertificateVerify =
        st
      in
      let Bertie.Tls13crypto.Algorithms ha ae v__sa v__gn v__psk_mode v__zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
        algs
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist509:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist509)
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
          let* hoist510:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist510)
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
          let* hoist511:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist511)
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
          let* hoist512:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist512)
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
      let* cak, sak, exp:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_app_keys ha ae ms th_sfin
              <:
              Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist513:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist513)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
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

let put_server_hello (sh: Bertie.Tls13utils.t_HandshakeData) (st: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ClientPostClientHello cr algs0 x psk tx:t_ClientPostClientHello
      =
        st
      in
      let Bertie.Tls13crypto.Algorithms ha ae v__sa ks v__psk_mode v__zero_rtt:Bertie.Tls13crypto.t_Algorithms
      =
        algs0
      in
      let* sr, gy:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_server_hello algs0 sh
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist514:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist514)
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
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sh in
      let* gxy:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_decap ks gy x
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist515:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist515)
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
          let* hoist516:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist516)
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
      let* chk, shk, cfk, sfk, ms:((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_hk_ms ha ae gxy psk th
              <:
              Core.Result.t_Result
                ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes &
                  Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist517:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist517)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
            ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes &
              Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13record.duplex_cipher_state_hs ae chk 0uL shk 0uL,
          (ClientPostServerHello cr sr algs0 ms cfk sfk tx <: t_ClientPostServerHello)
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
            let* hoist518:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist518)
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
            let* hoist519:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist519)
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
            let* hoist520:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist520)
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
            let* hoist521:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist521)
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
            let* hoist522:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist522)
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
            let* hoist523:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist523)
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.verify (Bertie.Tls13crypto.impl__Algorithms__sig_alg
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
            let* hoist524:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist524)
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
            let* hoist525:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist525)
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
            let* hoist526:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist526)
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
            let* hoist527:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist527)
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
            let* hoist528:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist528)
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
            let* hoist529:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist529)
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
            let* hoist530:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist530)
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
            let* hoist531:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist531)
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
            let* hoist532:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist532)
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

let server_finish (cf: Bertie.Tls13utils.t_HandshakeData) (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 = put_client_finished cf st

let server_init
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (db: Bertie.Server.t_ServerDB)
      (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
        Bertie.Tls13record.t_DuplexCipherStateH &
        Bertie.Tls13record.t_DuplexCipherState1 &
        t_ServerPostServerFinished) u8 =
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
          let* hoist540:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist540)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
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
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 & t_ServerPostClientHello)
      in
      let* sh, cipher_hs, st:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) =
        match
          Core.Ops.Try_trait.f_branch (get_server_hello st
                (Bertie.Tls13utils.impl__Bytes__slice ent
                    (sz 0)
                    (sz 32 +!
                      (Bertie.Tls13crypto.kem_priv_len (Bertie.Tls13crypto.impl__Algorithms__kem_alg
                              algs
                            <:
                            Bertie.Tls13crypto.t_KemScheme)
                        <:
                        usize)
                      <:
                      usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                  t_ServerPostServerHello) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist541:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist541)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
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
            (Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                  Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                  Bertie.Tls13record.t_DuplexCipherStateH &
                  Bertie.Tls13record.t_DuplexCipherState1 &
                  t_ServerPostServerFinished) u8)
            (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
              t_ServerPostServerHello)
      in
      match Bertie.Tls13crypto.impl__Algorithms__psk_mode algs with
      | false ->
        let* ee, sc, scv, st:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
          Bertie.Tls13utils.t_HandshakeData &
          t_ServerPostCertificateVerify) =
          match
            Core.Ops.Try_trait.f_branch (get_server_signature st
                  (Bertie.Tls13utils.impl__Bytes__slice ent (sz 0) (sz 32)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist542:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist542)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
              (Core.Result.t_Result
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
            let* hoist543:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist543)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
              (Core.Result.t_Result
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
                  (Bertie.Tls13utils.handshake_concat scv sfin <: Bertie.Tls13utils.t_HandshakeData)
                <:
                Bertie.Tls13utils.t_HandshakeData)
          in
          Core.Result.Result_Ok
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
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                Bertie.Tls13record.t_DuplexCipherStateH &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ServerPostServerFinished) u8)
          (Core.Result.t_Result
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
            let* hoist544:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist544)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
              (Core.Result.t_Result
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
            let* hoist545:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist545)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result
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
              (Core.Result.t_Result
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
          Core.Result.Result_Ok
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
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                Bertie.Tls13record.t_DuplexCipherStateH &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ServerPostServerFinished) u8)
          (Core.Result.t_Result
              (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                Bertie.Tls13record.t_DuplexCipherStateH &
                Bertie.Tls13record.t_DuplexCipherState1 &
                t_ServerPostServerFinished) u8))
