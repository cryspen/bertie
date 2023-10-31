module Bertie.Tls13handshake
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

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
        (Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG)
      else
        let lenb:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__U16__to_be_bytes (Core.Convert.f_from (cast len <: u16)
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
        let* hoist277:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 tls13_label
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist276:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist276)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let hoist280:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat lenb hoist277
        in
        let* hoist279:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 context
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist278:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist278)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let info:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat hoist280 hoist279
          in
          Bertie.Tls13crypto.hkdf_expand ha k info len))

let derive_secret (ha: Bertie.Tls13crypto.t_HashAlgorithm) (k label tx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  hkdf_expand_label ha k label tx (Bertie.Tls13crypto.hash_len ha <: usize)

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
          let* hoist281:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist281)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist283:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hash_empty ha
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist282:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist282)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (derive_secret ha
          early_secret
          (Bertie.Tls13utils.bytes (Rust_primitives.unsize Bertie.Tls13formats.v_LABEL_RES_BINDER
                <:
                t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist283))

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
          let* hoist284:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist284)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist285:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist285)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (sender_write_key, sender_write_iv)))

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
          let* hoist286:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist286)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist287:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist287)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist288:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist288)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sender_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_early_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist289:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist289)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (sender_write_key_iv, early_exporter_master_secret)))

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
          let* hoist290:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist290)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* digest_emp:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (hash_empty ha
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist291:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist291)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist292:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist292)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* handshake_secret:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hkdf_extract ha gxy derived_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist293:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist293)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist294:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist294)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist295:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist295)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* client_finished_key:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_finished_key ha client_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist296:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist296)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* server_finished_key:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_finished_key ha server_handshake_traffic_secret
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist297:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist297)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* client_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_handshake_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist298:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist298)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* server_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_handshake_traffic_secret
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist299:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist299)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist300:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist300)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist301:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist301)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (client_write_key_iv,
          server_write_key_iv,
          client_finished_key,
          server_finished_key,
          master_secret)))

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
          let* hoist302:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist302)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist303:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist303)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* client_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae client_application_traffic_secret_0_
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist304:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist304)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* server_write_key_iv:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (derive_aead_key_iv ha ae server_application_traffic_secret_0_
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist305:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist305)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist306:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  ((Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) &
                    Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist306)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (client_write_key_iv, server_write_key_iv, exporter_master_secret)))

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

let algs_post_client_hello (st: t_ClientPostClientHello) : Bertie.Tls13crypto.t_Algorithms = st._1

let algs_post_server_hello (st: t_ClientPostServerHello) : Bertie.Tls13crypto.t_Algorithms = st._2

let algs_post_client_finished (st: t_ClientPostClientFinished) : Bertie.Tls13crypto.t_Algorithms =
  st._2

type t_ServerPostClientHello =
  | ServerPostClientHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostClientHello

type t_ServerPostServerHello =
  | ServerPostServerHello :
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13crypto.t_Algorithms ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13utils.t_Bytes ->
      Bertie.Tls13formats.t_Transcript
    -> t_ServerPostServerHello

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
        Bertie.Tls13crypto.kem_priv_len (Bertie.Tls13crypto.kem_alg algs0
            <:
            Bertie.Tls13crypto.t_KemScheme)
      in
      if (Bertie.Tls13utils.impl__Bytes__len ent <: usize) <. (sz 32 +! gx_len <: usize)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_INSUFFICIENT_ENTROPY)
      else
        let tx:Bertie.Tls13formats.t_Transcript =
          Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.hash_alg algs0
              <:
              Bertie.Tls13crypto.t_HashAlgorithm)
        in
        let cr:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice_range ent
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 32 })
        in
        let* x, gx:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_keygen (Bertie.Tls13crypto.kem_alg algs0

                    <:
                    Bertie.Tls13crypto.t_KemScheme)
                  (Bertie.Tls13utils.impl__Bytes__slice_range ent
                      ({
                          Core.Ops.Range.f_start = sz 32;
                          Core.Ops.Range.f_end = sz 32 +! gx_len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist307:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist307)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* ch, trunc_len:(Bertie.Tls13utils.t_HandshakeData & usize) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.client_hello algs0 cr gx sn tkt
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist308:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist308)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist309:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      t_ClientPostClientHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist309)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok (nch, cipher0, ClientPostClientHello cr algs0 x psk tx_ch)))

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
      match psk_mode, psk, (cast trunc_len <: u8) with
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
            let* hoist310:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist310)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* mk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (derive_binder_key ha k
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist311:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist311)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* binder:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag ha mk th_trunc
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist312:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist312)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* nch:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.set_client_hello_binder algs0
                  (Core.Option.Option_Some binder)
                  ch
                  (Core.Option.Option_Some trunc_len)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist313:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                      Bertie.Tls13formats.t_Transcript) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist313)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
              let* hoist314:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist314)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
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
              let* hoist315:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_HandshakeData &
                        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
                        Bertie.Tls13formats.t_Transcript) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist315)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 =
              Core.Option.Option_Some (Bertie.Tls13record.client_cipher_state0 ae aek 0uL key)
            in
            Core.Result.Result_Ok (nch, cipher0, tx_ch))
        else
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok (nch, Core.Option.Option_None, tx_ch))
      | false, Core.Option.Option_None , 0uy ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx_ch:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ch in
          Core.Result.Result_Ok (ch, Core.Option.Option_None, tx_ch))
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

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
          let* hoist316:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist316)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sh in
      let* gxy:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.kem_decap ks gy x
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist317:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist317)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist318:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist318)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist319:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist319)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13record.duplex_cipher_state_hs ae chk 0uL shk 0uL,
          ClientPostServerHello cr sr algs0 ms cfk sfk tx)))

let put_server_signature
      (ee sc scv: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostServerHello cr sr algs ms cfk sfk tx:t_ClientPostServerHello =
        st
      in
      if ~.(Bertie.Tls13crypto.psk_mode algs <: bool)
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_encrypted_extensions algs ee
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist320:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist320)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
        let* cert:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_server_certificate algs sc
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist321:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist321)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sc in
        let* th_sc:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist322:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist322)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* spki:(Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.verification_key_from_cert cert
                <:
                Core.Result.t_Result
                  (Bertie.Tls13crypto.t_SignatureScheme & Bertie.Tls13cert.t_CertificateKey) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist323:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist323)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* pk:Bertie.Tls13cert.t_PublicVerificationKey =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13cert.cert_public_key cert spki
                <:
                Core.Result.t_Result Bertie.Tls13cert.t_PublicVerificationKey u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist324:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist324)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* sig:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_certificate_verify algs scv
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist325:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist325)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.verify (Bertie.Tls13crypto.sig_alg algs
                    <:
                    Bertie.Tls13crypto.t_SignatureScheme)
                  pk
                  sigval
                  sig
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist326:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist326)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx scv in
          Core.Result.Result_Ok (ClientPostCertificateVerify cr sr algs ms cfk sfk tx))
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

let put_psk_skip_server_signature
      (ee: Bertie.Tls13utils.t_HandshakeData)
      (st: t_ClientPostServerHello)
    : Core.Result.t_Result t_ClientPostCertificateVerify u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ClientPostServerHello cr sr algs ms cfk sfk tx:t_ClientPostServerHello =
        st
      in
      if Bertie.Tls13crypto.psk_mode algs
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_encrypted_extensions algs ee
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist327:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_ClientPostCertificateVerify u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist327)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
          Core.Result.Result_Ok (ClientPostCertificateVerify cr sr algs ms cfk sfk tx))
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

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
          let* hoist328:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist328)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_finished algs sfin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist329:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist329)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify ha sfk th vd
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist330:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist330)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sfin in
      let* th_sfin:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist331:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist331)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist332:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13record.t_DuplexCipherState1 & t_ClientPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist332)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 ae cak 0uL sak 0uL exp
        in
        Core.Result.Result_Ok (cipher1, ClientPostServerFinished cr sr algs ms cfk tx)))

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
          let* hoist333:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist333)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag (Bertie.Tls13crypto.hash_alg algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                cfk
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist334:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist334)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* cfin:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.finished algs vd
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist335:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist335)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx cfin in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist336:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist336)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* rms:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.hash_alg algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist337:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist337)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (cfin, ClientPostClientFinished cr sr algs rms tx)))

let client_init
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sn: Bertie.Tls13utils.t_Bytes)
      (tkt psk: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData &
        Core.Option.t_Option Bertie.Tls13record.t_ClientCipherState0 &
        t_ClientPostClientHello) u8 = get_client_hello algs sn tkt psk ent

let client_set_params (payload: Bertie.Tls13utils.t_HandshakeData) (st: t_ClientPostClientHello)
    : Core.Result.t_Result (Bertie.Tls13record.t_DuplexCipherStateH & t_ClientPostServerHello) u8 =
  put_server_hello payload st

let client_finish (payload: Bertie.Tls13utils.t_HandshakeData) (st: t_ClientPostServerHello)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
        t_ClientPostClientFinished) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        Bertie.Tls13crypto.psk_mode (algs_post_server_hello st <: Bertie.Tls13crypto.t_Algorithms)
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
            let* hoist338:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist338)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* cstate_cv:t_ClientPostCertificateVerify =
          match
            Core.Ops.Try_trait.f_branch (put_server_signature ee sc scv st
                <:
                Core.Result.t_Result t_ClientPostCertificateVerify u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist339:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist339)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist340:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist340)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* cfin, cstate:(Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) =
          match
            Core.Ops.Try_trait.f_branch (get_client_finished cstate_fin
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist341:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist341)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (cfin, cipher, cstate))
      | true ->
        let* ee, sfin:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_handshake_messages2 payload
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist342:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist342)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* cstate_cv:t_ClientPostCertificateVerify =
          match
            Core.Ops.Try_trait.f_branch (put_psk_skip_server_signature ee st
                <:
                Core.Result.t_Result t_ClientPostCertificateVerify u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist343:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist343)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist344:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist344)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* cfin, cstate:(Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) =
          match
            Core.Ops.Try_trait.f_branch (get_client_finished cstate_fin
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ClientPostClientFinished) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist345:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ClientPostClientFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist345)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (cfin, cipher, cstate)))

let put_client_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (db: Bertie.Tls13utils.t_ServerDB)
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
          let* hoist346:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist346)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript =
        Bertie.Tls13formats.transcript_empty (Bertie.Tls13crypto.hash_alg algs
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
          let* hoist347:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist347)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ch in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist348:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist348)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* cert, sigk, psko:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lookup_db algs db sni tkto
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                  Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist349:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist349)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
        match
          Core.Ops.Try_trait.f_branch (process_psk_binder_zero_rtt algs th th_trunc psko bindero
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist350:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    t_ServerPostClientHello) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist350)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (cipher0, ServerPostClientHello cr algs sid gx cert sigk psko tx)))

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
      match psk_mode, psko, bindero with
      | true, Core.Option.Option_Some k, Core.Option.Option_Some binder ->
        let* mk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (derive_binder_key ha k
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist351:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist351)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify ha mk th_trunc binder
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist352:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist352)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
              let* hoist353:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result
                      (Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist353)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let cipher0:Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 =
              Core.Option.Option_Some (Bertie.Tls13record.server_cipher_state0 ae aek 0uL key)
            in
            Core.Result.Result_Ok cipher0)
        else
          Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok Core.Option.Option_None)
      | false, Core.Option.Option_None , Core.Option.Option_None  ->
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok Core.Option.Option_None)
      | _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

let get_server_hello (st: t_ServerPostClientHello) (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostClientHello cr algs sid gx cert sigk psk tx:t_ServerPostClientHello =
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
        (Core.Result.Result_Err Bertie.Tls13utils.v_INSUFFICIENT_ENTROPY)
      else
        let sr:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice_range ent
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 32 })
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
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist354:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist354)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* sh:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_hello algs sr sid gy
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist355:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist355)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sh in
        let* th:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist356:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist356)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist357:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherStateH &
                      t_ServerPostServerHello) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist357)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (sh,
            Bertie.Tls13record.duplex_cipher_state_hs ae shk 0uL chk 0uL,
            ServerPostServerHello cr sr algs cert sigk ms cfk sfk tx)))

let get_server_signature (st: t_ServerPostServerHello) (ent: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData &
        t_ServerPostCertificateVerify) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostServerHello cr sr algs cert sigk ms cfk sfk tx:t_ServerPostServerHello =
        st
      in
      let* ee:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.encrypted_extensions algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist358:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    t_ServerPostCertificateVerify) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist358)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
      if ~.(Bertie.Tls13crypto.psk_mode algs <: bool)
      then
        let* sc:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.server_certificate algs cert
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist359:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist359)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sc in
        let* th:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist360:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist360)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.sign (Bertie.Tls13crypto.sig_alg algs
                    <:
                    Bertie.Tls13crypto.t_SignatureScheme)
                  sigk
                  sigval
                  ent
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist361:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist361)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* scv:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.certificate_verify algs sig
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist362:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Bertie.Tls13utils.t_HandshakeData &
                      t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist362)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx scv in
          Core.Result.Result_Ok (ee, sc, scv, ServerPostCertificateVerify cr sr algs ms cfk sfk tx))
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

let get_skip_server_signature (st: t_ServerPostServerHello)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      ServerPostServerHello cr sr algs v__cert v__sigk ms cfk sfk tx:t_ServerPostServerHello =
        st
      in
      if Bertie.Tls13crypto.psk_mode algs
      then
        let* ee:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.encrypted_extensions algs
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist363:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist363)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx ee in
          Core.Result.Result_Ok (ee, ServerPostCertificateVerify cr sr algs ms cfk sfk tx))
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PSK_MODE_MISMATCH))

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
          let* hoist364:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist364)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_tag ha sfk th_scv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist365:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist365)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sfin:Bertie.Tls13utils.t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.finished algs vd
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist366:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist366)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx sfin in
      let* th_sfin:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist367:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist367)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
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
          let* hoist368:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist368)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let cipher1:Bertie.Tls13record.t_DuplexCipherState1 =
          Bertie.Tls13record.duplex_cipher_state1 ae sak 0uL cak 0uL exp
        in
        Core.Result.Result_Ok (sfin, cipher1, ServerPostServerFinished cr sr algs ms cfk tx)))

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
          let* hoist369:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist369)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* vd:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.parse_finished algs cfin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist370:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist370)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hmac_verify (Bertie.Tls13crypto.hash_alg algs

                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                cfk
                th
                vd
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist371:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist371)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tx:Bertie.Tls13formats.t_Transcript = Bertie.Tls13formats.transcript_add1 tx cfin in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.get_transcript_hash tx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist372:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist372)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* rms:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (derive_rms (Bertie.Tls13crypto.hash_alg algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
                ms
                th
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist373:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_ServerPostClientFinished u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist373)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok (ServerPostClientFinished cr sr algs rms tx)))

let server_init
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (db: Bertie.Tls13utils.t_ServerDB)
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
          let* hoist374:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist374)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sh, cipher_hs, st:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13record.t_DuplexCipherStateH &
        t_ServerPostServerHello) =
        match
          Core.Ops.Try_trait.f_branch (get_server_hello st
                (Bertie.Tls13utils.impl__Bytes__slice ent
                    (sz 0)
                    (sz 32 +!
                      (Bertie.Tls13crypto.kem_priv_len (Bertie.Tls13crypto.kem_alg algs
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
          let* hoist375:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                    Bertie.Tls13record.t_DuplexCipherStateH &
                    Bertie.Tls13record.t_DuplexCipherState1 &
                    t_ServerPostServerFinished) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist375)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      match Bertie.Tls13crypto.psk_mode algs with
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
            let* hoist376:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist376)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist377:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist377)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let flight:Bertie.Tls13utils.t_HandshakeData =
            Bertie.Tls13utils.handshake_concat ee
              (Bertie.Tls13utils.handshake_concat sc
                  (Bertie.Tls13utils.handshake_concat scv sfin <: Bertie.Tls13utils.t_HandshakeData)
                <:
                Bertie.Tls13utils.t_HandshakeData)
          in
          Core.Result.Result_Ok (sh, flight, cipher0, cipher_hs, cipher1, st))
      | true ->
        let* ee, st:(Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) =
          match
            Core.Ops.Try_trait.f_branch (get_skip_server_signature st
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & t_ServerPostCertificateVerify) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist378:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist378)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
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
            let* hoist379:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                      Core.Option.t_Option Bertie.Tls13record.t_ServerCipherState0 &
                      Bertie.Tls13record.t_DuplexCipherStateH &
                      Bertie.Tls13record.t_DuplexCipherState1 &
                      t_ServerPostServerFinished) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist379)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let flight:Bertie.Tls13utils.t_HandshakeData =
            Bertie.Tls13utils.handshake_concat ee sfin
          in
          Core.Result.Result_Ok (sh, flight, cipher0, cipher_hs, cipher1, st)))

let server_finish (cf: Bertie.Tls13utils.t_HandshakeData) (st: t_ServerPostServerFinished)
    : Core.Result.t_Result t_ServerPostClientFinished u8 = put_client_finished cf st