module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_LABEL_IV: t_Array u8 (sz 2) =
  let list = [105uy; 118uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_KEY: t_Array u8 (sz 3) =
  let list = [107uy; 101uy; 121uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_TLS13: t_Array u8 (sz 6) =
  let list = [116uy; 108uy; 115uy; 49uy; 51uy; 32uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_DERIVED: t_Array u8 (sz 7) =
  let list = [100uy; 101uy; 114uy; 105uy; 118uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_FINISHED: t_Array u8 (sz 8) =
  let list = [102uy; 105uy; 110uy; 105uy; 115uy; 104uy; 101uy; 100uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_RES_BINDER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 98uy; 105uy; 110uy; 100uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_EXT_BINDER: t_Array u8 (sz 10) =
  let list = [101uy; 120uy; 116uy; 32uy; 98uy; 105uy; 110uy; 100uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_EXP_MASTER: t_Array u8 (sz 10) =
  let list = [101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_RES_MASTER: t_Array u8 (sz 10) =
  let list = [114uy; 101uy; 115uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_C_E_TRAFFIC: t_Array u8 (sz 11) =
  let list = [99uy; 32uy; 101uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_E_EXP_MASTER: t_Array u8 (sz 12) =
  let list = [101uy; 32uy; 101uy; 120uy; 112uy; 32uy; 109uy; 97uy; 115uy; 116uy; 101uy; 114uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_C_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_S_HS_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 104uy; 115uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_C_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [99uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_LABEL_S_AP_TRAFFIC: t_Array u8 (sz 12) =
  let list = [115uy; 32uy; 97uy; 112uy; 32uy; 116uy; 114uy; 97uy; 102uy; 102uy; 105uy; 99uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let v_PREFIX_SERVER_SIGNATURE: t_Array u8 (sz 98) =
  let list =
    [
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy; 32uy;
      84uy; 76uy; 83uy; 32uy; 49uy; 46uy; 51uy; 44uy; 32uy; 115uy; 101uy; 114uy; 118uy; 101uy; 114uy;
      32uy; 67uy; 101uy; 114uy; 116uy; 105uy; 102uy; 105uy; 99uy; 97uy; 116uy; 101uy; 86uy; 101uy;
      114uy; 105uy; 102uy; 121uy; 0uy
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 98);
  Rust_primitives.Hax.array_of_list list

let ciphersuite (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match Bertie.Tls13crypto.hash_alg algs, Bertie.Tls13crypto.aead_alg algs with
  | Bertie.Tls13crypto.HashAlgorithm_SHA256 , Bertie.Tls13crypto.AeadAlgorithm_Aes128Gcm  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 1uy)
  | Bertie.Tls13crypto.HashAlgorithm_SHA384 , Bertie.Tls13crypto.AeadAlgorithm_Aes256Gcm  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 2uy)
  | Bertie.Tls13crypto.HashAlgorithm_SHA256 , Bertie.Tls13crypto.AeadAlgorithm_Chacha20Poly1305  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 19uy 3uy)
  | _ -> Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let supported_group (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match Bertie.Tls13crypto.kem_alg algs with
  | Bertie.Tls13crypto.KemScheme_X25519  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 0uy 29uy)
  | Bertie.Tls13crypto.KemScheme_Secp256r1  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 0uy 23uy)
  | Bertie.Tls13crypto.KemScheme_X448  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | Bertie.Tls13crypto.KemScheme_Secp384r1  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  | Bertie.Tls13crypto.KemScheme_Secp521r1  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let signature_algorithm (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  match Bertie.Tls13crypto.sig_alg algs with
  | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 8uy 4uy)
  | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.bytes2 4uy 3uy)
  | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
    Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let check_ciphersuites (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 b
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist1:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist1)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* cs:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist2:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist2)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let csl:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range b
          ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 2 +! len <: usize })
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_mem cs csl
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist3:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist3)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (len +! sz 2)))

let server_name (sn: Bertie.Tls13utils.t_Bytes) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist7:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 sn
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist6:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist6)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist8:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 0uy
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist7
      in
      let hoist9:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist8
      in
      let hoist10:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist9
      in
      let* hoist11:Bertie.Tls13utils.t_Bytes =
        match hoist10 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist5:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist5)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist12:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist11
      in
      let hoist13:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist12
      in
      let* hoist14:Bertie.Tls13utils.t_Bytes =
        match hoist13 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist4:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist4)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist15:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 0uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist14
        in
        Core.Result.Result_Ok hoist15))

let check_server_name (ext: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ext
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist16:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist16)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__slice_range ext
                    ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist17:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist17)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    ext
                    ({
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ext <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist18:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist18)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__Bytes__slice_range ext
            ({
                Core.Ops.Range.f_start = sz 5;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ext <: usize
              }))))

let supported_versions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist21:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes2 3uy 4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist20:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist20)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist22:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist21
      in
      let hoist23:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist22
      in
      let* hoist24:Bertie.Tls13utils.t_Bytes =
        match hoist23 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist19:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist19)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist25:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 43uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist24
        in
        Core.Result.Result_Ok hoist25))

let check_supported_versions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist26:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist26)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem (Bertie.Tls13utils.bytes2 3uy 4uy <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                })
            <:
            Bertie.Tls13utils.t_Bytes)))

let server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist28:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.bytes2 3uy 4uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist27:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist27)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist29:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 43uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist28
        in
        Core.Result.Result_Ok hoist29))

let check_server_supported_version
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes2 3uy 4uy <: Bertie.Tls13utils.t_Bytes) b

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist33:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist32:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist32)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist34:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist33
      in
      let hoist35:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist34
      in
      let* hoist36:Bertie.Tls13utils.t_Bytes =
        match hoist35 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist31:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist31)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist37:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist36
      in
      let hoist38:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist37
      in
      let* hoist39:Bertie.Tls13utils.t_Bytes =
        match hoist38 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist30:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist30)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist40:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 10uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist39
        in
        Core.Result.Result_Ok hoist40))

let check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist41:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist41)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist43:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist42:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist42)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem hoist43
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                })
            <:
            Bertie.Tls13utils.t_Bytes)))

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist47:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist46:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist46)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist48:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist47
      in
      let hoist49:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist48
      in
      let* hoist50:Bertie.Tls13utils.t_Bytes =
        match hoist49 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist45:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist45)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist51:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist50
      in
      let hoist52:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist51
      in
      let* hoist53:Bertie.Tls13utils.t_Bytes =
        match hoist52 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist44:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist44)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist54:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist53
        in
        Core.Result.Result_Ok hoist54))

let check_signature_algorithms
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist55:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist55)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist57:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist56:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist56)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_mem hoist57
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                })
            <:
            Bertie.Tls13utils.t_Bytes)))

let psk_key_exchange_modes (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist60:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist59:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist59)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist61:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist60
      in
      let hoist62:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist61
      in
      let* hoist63:Bertie.Tls13utils.t_Bytes =
        match hoist62 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist58:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist58)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist64:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 45uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist63
        in
        Core.Result.Result_Ok hoist64))

let check_psk_key_exchange_modes
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist65:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist65)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 1uy <: Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 2 })
            <:
            Bertie.Tls13utils.t_Bytes)))

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist69:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist66:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist66)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist68:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist67:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist67)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist69 hoist68 in
      let* hoist72:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist71:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist71)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist73:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist72
      in
      let hoist74:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist73
      in
      let* hoist75:Bertie.Tls13utils.t_Bytes =
        match hoist74 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist70:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist70)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist76:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist75
        in
        Core.Result.Result_Ok hoist76))

let find_key_share (g ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len ch <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        if
          Bertie.Tls13utils.eq g
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 })
              <:
              Bertie.Tls13utils.t_Bytes)
          <:
          bool
        then
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                        ch
                        ({
                            Core.Ops.Range.f_start = sz 2;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist77:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist77)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize })))
        else
          let* len:usize =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                        ch
                        ({
                            Core.Ops.Range.f_start = sz 2;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result usize u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist78:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist78)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (find_key_share g
              (Bertie.Tls13utils.impl__Bytes__slice_range ch
                  ({
                      Core.Ops.Range.f_start = sz 4 +! len <: usize;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                    })
                <:
                Bertie.Tls13utils.t_Bytes)))

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full ch
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist79:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist79)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist81:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist80:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist80)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (find_key_share hoist81
          (Bertie.Tls13utils.impl__Bytes__slice_range ch
              ({
                  Core.Ops.Range.f_start = sz 2;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                })
            <:
            Bertie.Tls13utils.t_Bytes)))

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist85:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist82:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist82)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist84:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist83:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist83)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist85 hoist84 in
      let* hoist87:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 ks
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist86:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist86)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist88:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist87
        in
        Core.Result.Result_Ok hoist88))

let check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist91:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_group algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist90:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist90)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist92:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist91
          (Bertie.Tls13utils.impl__Bytes__slice_range b
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 })
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist93:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist92
      in
      let* _:Prims.unit =
        match hoist93 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist89:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist89)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    b
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist94:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist94)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__Bytes__slice_range b
            ({
                Core.Ops.Range.f_start = sz 4;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
              }))))

let pre_shared_key (algs: Bertie.Tls13crypto.t_Algorithms) (tkt: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist97:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist96:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist96)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist98:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat hoist97
          (Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 4294967295ul
                <:
                Bertie.Tls13utils.t_U32)
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist99:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist98
      in
      let hoist100:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist99
      in
      let* identities:Bertie.Tls13utils.t_Bytes =
        match hoist100 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist95:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist95)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist103:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13crypto.zero_key (Bertie.Tls13crypto.hash_alg
                        algs
                      <:
                      Bertie.Tls13crypto.t_HashAlgorithm)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist102:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist102)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist104:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist103
      in
      let hoist105:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist104
      in
      let* binders:Bertie.Tls13utils.t_Bytes =
        match hoist105 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist101:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist101)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist107:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__concat
                    identities
                    binders
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist106:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist106)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let ext:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist107
        in
        Core.Result.Result_Ok (ext, Bertie.Tls13utils.impl__Bytes__len binders)))

let check_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (ch: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len_id:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 ch
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist108:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist108)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* len_tkt:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    ch
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = sz 2 +! len_id <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist109:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist109)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      if len_id =. (len_tkt +! sz 6 <: usize)
      then
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                      ch
                      ({
                          Core.Ops.Range.f_start = sz 2 +! len_id <: usize;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist110:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist110)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
                      ch
                      ({
                          Core.Ops.Range.f_start = sz 4 +! len_id <: usize;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist111:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Prims.unit u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist111)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (if
            (((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -! sz 6 <: usize) -! len_id <: usize) <>.
            sz 32
          then Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          else Core.Result.Result_Ok ())
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)))

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist113:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.bytes2 0uy 0uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist112:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist112)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist114:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist113
        in
        Core.Result.Result_Ok hoist114))

let check_server_psk_shared_key
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes2 0uy 0uy <: Bertie.Tls13utils.t_Bytes) b

type t_EXTS =
  | EXTS :
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes ->
      Core.Option.t_Option Bertie.Tls13utils.t_Bytes
    -> t_EXTS

let merge_opts
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_T)
      (o1 o2: Core.Option.t_Option v_T)
    : Core.Result.t_Result (Core.Option.t_Option v_T) u8 =
  match o1, o2 with
  | Core.Option.Option_None , Core.Option.Option_Some o ->
    Core.Result.Result_Ok (Core.Option.Option_Some o)
  | Core.Option.Option_Some o, Core.Option.Option_None  ->
    Core.Result.Result_Ok (Core.Option.Option_Some o)
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok Core.Option.Option_None
  | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

let merge_exts (e1 e2: t_EXTS) : Core.Result.t_Result t_EXTS u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let EXTS sn1 ks1 tkt1 bd1:t_EXTS = e1 in
      let EXTS sn2 ks2 tkt2 bd2:t_EXTS = e2 in
      let* hoist122:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts sn1 sn2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist115:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist115)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist121:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts ks1 ks2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist116:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist116)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist120:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts tkt1 tkt2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist117:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist117)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist119:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (merge_opts bd1 bd2
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist118:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist118)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist123:t_EXTS = EXTS hoist122 hoist121 hoist120 hoist119 in
        Core.Result.Result_Ok hoist123))

let missing_key_share: Core.Result.t_Result (usize & t_EXTS) u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (usize & t_EXTS) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let l0:usize =
        cast (Bertie.Tls13utils.f_declassify (b.[ sz 0 ] <: Bertie.Tls13utils.t_U8)) <: usize
      in
      let l1:usize =
        cast (Bertie.Tls13utils.f_declassify (b.[ sz 1 ] <: Bertie.Tls13utils.t_U8)) <: usize
      in
      let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    b
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist124:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & t_EXTS) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist124)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let out:t_EXTS =
        EXTS Core.Option.Option_None
          Core.Option.Option_None
          Core.Option.Option_None
          Core.Option.Option_None
      in
      match (cast l0 <: u8), (cast l1 <: u8) with
      | 0uy, 0uy ->
        let* hoist126:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_name (Bertie.Tls13utils.impl__Bytes__slice_range
                      b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist125:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist125)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist127:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
            Core.Option.Option_Some hoist126
          in
          let hoist128:t_EXTS =
            EXTS hoist127 Core.Option.Option_None Core.Option.Option_None Core.Option.Option_None
          in
          let hoist129:(usize & t_EXTS) = sz 4 +! len, hoist128 in
          Core.Result.Result_Ok hoist129)
      | 0uy, 45uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_key_exchange_modes algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist130:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist130)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out))
      | 0uy, 43uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_versions algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist131:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist131)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out))
      | 0uy, 10uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_supported_groups algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist132:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist132)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out))
      | 0uy, 13uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_signature_algorithms algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist133:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist133)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out))
      | 0uy, 51uy ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (match
            check_key_shares algs
              (Bertie.Tls13utils.impl__Bytes__slice_range b
                  ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize })
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok gx ->
            Core.Result.Result_Ok
            (sz 4 +! len,
              EXTS Core.Option.Option_None
                (Core.Option.Option_Some gx)
                Core.Option.Option_None
                Core.Option.Option_None)
          | Core.Result.Result_Err _ ->
            Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE)
      | 0uy, 41uy ->
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_psk_shared_key algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = sz 4;
                          Core.Ops.Range.f_end = sz 4 +! len <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist134:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & t_EXTS) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist134)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out))
      | _ -> Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out)))

let check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let l0:usize =
        cast (Bertie.Tls13utils.f_declassify (b.[ sz 0 ] <: Bertie.Tls13utils.t_U8)) <: usize
      in
      let l1:usize =
        cast (Bertie.Tls13utils.f_declassify (b.[ sz 1 ] <: Bertie.Tls13utils.t_U8)) <: usize
      in
      let* len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    b
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist135:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist135)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes = Core.Option.Option_None in
      let* out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match (cast l0 <: u8), (cast l1 <: u8) with
        | 0uy, 43uy ->
          (match
              Core.Ops.Try_trait.f_branch (check_server_supported_version algs
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist136:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue out
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue out)
        | 0uy, 51uy ->
          let* gx:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (check_server_key_share algs
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist137:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist137)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Core.Option.Option_Some gx)
        | 0uy, 41uy ->
          (match
              Core.Ops.Try_trait.f_branch (check_server_psk_shared_key algs
                    (Bertie.Tls13utils.impl__Bytes__slice_range b
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = sz 4 +! len <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist138:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                  )
              in
              Core.Ops.Control_flow.ControlFlow_Continue out
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue out)
        | _ -> Core.Ops.Control_flow.ControlFlow_Continue out
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (sz 4 +! len, out)))

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_EXTS u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize & t_EXTS) =
        match
          Core.Ops.Try_trait.f_branch (check_extension algs b
              <:
              Core.Result.t_Result (usize & t_EXTS) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist139:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_EXTS u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist139)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
      then Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok out)
      else
        let* out_rest:t_EXTS =
          match
            Core.Ops.Try_trait.f_branch (check_extensions algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = len;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result t_EXTS u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist140:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result t_EXTS u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist140)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (merge_exts out out_rest))

let check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* len, out:(usize &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (check_server_extension algs b
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist141:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist141)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
      then Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok out)
      else
        let* out_rest:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (check_server_extensions algs
                  (Bertie.Tls13utils.impl__Bytes__slice_range b
                      ({
                          Core.Ops.Range.f_start = len;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist142:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist142)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (merge_opts out out_rest))

type t_HandshakeType =
  | HandshakeType_ClientHello : t_HandshakeType
  | HandshakeType_ServerHello : t_HandshakeType
  | HandshakeType_NewSessionTicket : t_HandshakeType
  | HandshakeType_EndOfEarlyData : t_HandshakeType
  | HandshakeType_EncryptedExtensions : t_HandshakeType
  | HandshakeType_Certificate : t_HandshakeType
  | HandshakeType_CertificateRequest : t_HandshakeType
  | HandshakeType_CertificateVerify : t_HandshakeType
  | HandshakeType_Finished : t_HandshakeType
  | HandshakeType_KeyUpdate : t_HandshakeType
  | HandshakeType_MessageHash : t_HandshakeType

let hs_type (t: t_HandshakeType) : u8 =
  match t with
  | HandshakeType_ClientHello  -> 1uy
  | HandshakeType_ServerHello  -> 2uy
  | HandshakeType_NewSessionTicket  -> 4uy
  | HandshakeType_EndOfEarlyData  -> 5uy
  | HandshakeType_EncryptedExtensions  -> 8uy
  | HandshakeType_Certificate  -> 11uy
  | HandshakeType_CertificateRequest  -> 13uy
  | HandshakeType_CertificateVerify  -> 15uy
  | HandshakeType_Finished  -> 20uy
  | HandshakeType_KeyUpdate  -> 24uy
  | HandshakeType_MessageHash  -> 254uy

let get_hs_type (t: u8) : Core.Result.t_Result t_HandshakeType u8 =
  match t with
  | 1uy -> Core.Result.Result_Ok HandshakeType_ClientHello
  | 2uy -> Core.Result.Result_Ok HandshakeType_ServerHello
  | 4uy -> Core.Result.Result_Ok HandshakeType_NewSessionTicket
  | 5uy -> Core.Result.Result_Ok HandshakeType_EndOfEarlyData
  | 8uy -> Core.Result.Result_Ok HandshakeType_EncryptedExtensions
  | 11uy -> Core.Result.Result_Ok HandshakeType_Certificate
  | 13uy -> Core.Result.Result_Ok HandshakeType_CertificateRequest
  | 15uy -> Core.Result.Result_Ok HandshakeType_CertificateVerify
  | 20uy -> Core.Result.Result_Ok HandshakeType_Finished
  | 24uy -> Core.Result.Result_Ok HandshakeType_KeyUpdate
  | 254uy -> Core.Result.Result_Ok HandshakeType_MessageHash
  | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

type t_AlertLevel =
  | AlertLevel_Warning : t_AlertLevel
  | AlertLevel_Fatal : t_AlertLevel

let alert_level (t: t_AlertLevel) : u8 =
  match t with
  | AlertLevel_Warning  -> 1uy
  | AlertLevel_Fatal  -> 2uy

let get_alert_level (t: u8) : Core.Result.t_Result t_AlertLevel u8 =
  match t with
  | 1uy -> Core.Result.Result_Ok AlertLevel_Warning
  | 2uy -> Core.Result.Result_Ok AlertLevel_Fatal
  | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

type t_AlertDescription =
  | AlertDescription_CloseNotify : t_AlertDescription
  | AlertDescription_UnexpectedMessage : t_AlertDescription
  | AlertDescription_BadRecordMac : t_AlertDescription
  | AlertDescription_RecordOverflow : t_AlertDescription
  | AlertDescription_HandshakeFailure : t_AlertDescription
  | AlertDescription_BadCertificate : t_AlertDescription
  | AlertDescription_UnsupportedCertificate : t_AlertDescription
  | AlertDescription_CertificateRevoked : t_AlertDescription
  | AlertDescription_CertificateExpired : t_AlertDescription
  | AlertDescription_CertificateUnknown : t_AlertDescription
  | AlertDescription_IllegalParameter : t_AlertDescription
  | AlertDescription_UnknownCa : t_AlertDescription
  | AlertDescription_AccessDenied : t_AlertDescription
  | AlertDescription_DecodeError : t_AlertDescription
  | AlertDescription_DecryptError : t_AlertDescription
  | AlertDescription_ProtocolVersion : t_AlertDescription
  | AlertDescription_InsufficientSecurity : t_AlertDescription
  | AlertDescription_InternalError : t_AlertDescription
  | AlertDescription_InappropriateFallback : t_AlertDescription
  | AlertDescription_UserCanceled : t_AlertDescription
  | AlertDescription_MissingExtension : t_AlertDescription
  | AlertDescription_UnsupportedExtension : t_AlertDescription
  | AlertDescription_UnrecognizedName : t_AlertDescription
  | AlertDescription_BadCertificateStatusResponse : t_AlertDescription
  | AlertDescription_UnknownPskIdentity : t_AlertDescription
  | AlertDescription_CertificateRequired : t_AlertDescription
  | AlertDescription_NoApplicationProtocol : t_AlertDescription

let alert_description (t: t_AlertDescription) : u8 =
  match t with
  | AlertDescription_CloseNotify  -> 0uy
  | AlertDescription_UnexpectedMessage  -> 10uy
  | AlertDescription_BadRecordMac  -> 20uy
  | AlertDescription_RecordOverflow  -> 22uy
  | AlertDescription_HandshakeFailure  -> 40uy
  | AlertDescription_BadCertificate  -> 42uy
  | AlertDescription_UnsupportedCertificate  -> 43uy
  | AlertDescription_CertificateRevoked  -> 44uy
  | AlertDescription_CertificateExpired  -> 45uy
  | AlertDescription_CertificateUnknown  -> 46uy
  | AlertDescription_IllegalParameter  -> 47uy
  | AlertDescription_UnknownCa  -> 48uy
  | AlertDescription_AccessDenied  -> 49uy
  | AlertDescription_DecodeError  -> 50uy
  | AlertDescription_DecryptError  -> 51uy
  | AlertDescription_ProtocolVersion  -> 70uy
  | AlertDescription_InsufficientSecurity  -> 71uy
  | AlertDescription_InternalError  -> 80uy
  | AlertDescription_InappropriateFallback  -> 86uy
  | AlertDescription_UserCanceled  -> 90uy
  | AlertDescription_MissingExtension  -> 109uy
  | AlertDescription_UnsupportedExtension  -> 110uy
  | AlertDescription_UnrecognizedName  -> 112uy
  | AlertDescription_BadCertificateStatusResponse  -> 113uy
  | AlertDescription_UnknownPskIdentity  -> 115uy
  | AlertDescription_CertificateRequired  -> 116uy
  | AlertDescription_NoApplicationProtocol  -> 120uy

let get_alert_description (t: u8) : Core.Result.t_Result t_AlertDescription u8 =
  match t with
  | 0uy -> Core.Result.Result_Ok AlertDescription_CloseNotify
  | 10uy -> Core.Result.Result_Ok AlertDescription_UnexpectedMessage
  | 20uy -> Core.Result.Result_Ok AlertDescription_BadRecordMac
  | 22uy -> Core.Result.Result_Ok AlertDescription_RecordOverflow
  | 40uy -> Core.Result.Result_Ok AlertDescription_HandshakeFailure
  | 42uy -> Core.Result.Result_Ok AlertDescription_BadCertificate
  | 43uy -> Core.Result.Result_Ok AlertDescription_UnsupportedCertificate
  | 44uy -> Core.Result.Result_Ok AlertDescription_CertificateRevoked
  | 45uy -> Core.Result.Result_Ok AlertDescription_CertificateExpired
  | 46uy -> Core.Result.Result_Ok AlertDescription_CertificateUnknown
  | 47uy -> Core.Result.Result_Ok AlertDescription_IllegalParameter
  | 48uy -> Core.Result.Result_Ok AlertDescription_UnknownCa
  | 49uy -> Core.Result.Result_Ok AlertDescription_AccessDenied
  | 50uy -> Core.Result.Result_Ok AlertDescription_DecodeError
  | 51uy -> Core.Result.Result_Ok AlertDescription_DecryptError
  | 70uy -> Core.Result.Result_Ok AlertDescription_ProtocolVersion
  | 71uy -> Core.Result.Result_Ok AlertDescription_InsufficientSecurity
  | 80uy -> Core.Result.Result_Ok AlertDescription_InternalError
  | 86uy -> Core.Result.Result_Ok AlertDescription_InappropriateFallback
  | 90uy -> Core.Result.Result_Ok AlertDescription_UserCanceled
  | 109uy -> Core.Result.Result_Ok AlertDescription_MissingExtension
  | 110uy -> Core.Result.Result_Ok AlertDescription_UnsupportedExtension
  | 112uy -> Core.Result.Result_Ok AlertDescription_UnrecognizedName
  | 113uy -> Core.Result.Result_Ok AlertDescription_BadCertificateStatusResponse
  | 115uy -> Core.Result.Result_Ok AlertDescription_UnknownPskIdentity
  | 116uy -> Core.Result.Result_Ok AlertDescription_CertificateRequired
  | 120uy -> Core.Result.Result_Ok AlertDescription_NoApplicationProtocol
  | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

let handshake_message (ty: t_HandshakeType) (v_by: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist144:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 v_by
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist143:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist143)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist145:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 (hs_type ty <: u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist144
        in
        let hoist146:Bertie.Tls13utils.t_HandshakeData =
          Bertie.Tls13utils.handshake_data hoist145
        in
        Core.Result.Result_Ok hoist146))

let get_first_handshake_message (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let p:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.handshake_data_bytes p
      in
      if (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 4
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8))
      else
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range
                      p
                      ({
                          Core.Ops.Range.f_start = sz 1;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist147:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist147)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let msg:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range p
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 +! len <: usize })
          in
          let rest:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range p
              ({
                  Core.Ops.Range.f_start = sz 4 +! len <: usize;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                })
          in
          Core.Result.Result_Ok
          (Bertie.Tls13utils.HandshakeData msg, Bertie.Tls13utils.HandshakeData rest)))

let get_handshake_message (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist148:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist148)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
        else Core.Result.Result_Ok m1))

let get_handshake_message_ty (ty: t_HandshakeType) (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData m:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message p
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist149:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist149)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let tyb:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (hs_type ty <: u8) in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq tyb
                (Bertie.Tls13utils.impl__Bytes__slice_range m
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist150:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist150)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.HandshakeData
          (Bertie.Tls13utils.impl__Bytes__slice_range m
              ({
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len m <: usize
                })))))

let get_handshake_messages2 (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist151:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist151)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* m2, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist152:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist152)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
        else Core.Result.Result_Ok (m1, m2)))

let get_handshake_messages4 (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* m1, p:(Bertie.Tls13utils.t_HandshakeData &
        Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist153:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist153)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* m2, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist154:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist154)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* m3, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist155:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist155)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* m4, p:(Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (get_first_handshake_message p
              <:
              Core.Result.t_Result
                (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist156:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_HandshakeData & Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData &
                    Bertie.Tls13utils.t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist156)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (Bertie.Tls13utils.handshake_data_len p <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
        else Core.Result.Result_Ok (m1, m2, m3, m4)))

let find_handshake_message
      (ty: t_HandshakeType)
      (payload: Bertie.Tls13utils.t_HandshakeData)
      (start: usize)
    : bool =
  let Bertie.Tls13utils.HandshakeData p:Bertie.Tls13utils.t_HandshakeData = payload in
  if (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. (start +! sz 4 <: usize)
  then false
  else
    match
      Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range p
            ({
                Core.Ops.Range.f_start = start +! sz 1 <: usize;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
              })
          <:
          Bertie.Tls13utils.t_Bytes)
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        Bertie.Tls13utils.eq1 (p.[ start ] <: Bertie.Tls13utils.t_U8)
          (Core.Convert.f_from (hs_type ty <: u8) <: Bertie.Tls13utils.t_U8)
      then true
      else find_handshake_message ty payload ((start +! sz 4 <: usize) +! len <: usize)

let client_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (cr gx sn: Bertie.Tls13utils.t_Bytes)
      (tkt: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let* sid:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.impl__Bytes__zeroes
                    (sz 32)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist157:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist157)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist160:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist159:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist159)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist161:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes2 hoist160
      in
      let hoist162:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist161
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match hoist162 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist158:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist158)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let* sn:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_name sn
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist163:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist163)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_versions algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist164:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist164)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sg:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (supported_groups algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist165:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist165)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sa:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithms algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist166:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist166)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* ks:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (key_shares algs gx
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist167:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist167)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let exts:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat sn sv <: Bertie.Tls13utils.t_Bytes)
                  sg
                <:
                Bertie.Tls13utils.t_Bytes)
              sa
            <:
            Bertie.Tls13utils.t_Bytes)
          ks
      in
      let trunc_len:usize = sz 0 in
      let* exts, trunc_len:(Bertie.Tls13utils.t_Bytes & usize) =
        match Bertie.Tls13crypto.psk_mode algs, tkt with
        | true, Core.Option.Option_Some tkt ->
          let* pskm:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (psk_key_exchange_modes algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist168:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist168)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          let* psk, len:(Bertie.Tls13utils.t_Bytes & usize) =
            match
              Core.Ops.Try_trait.f_branch (pre_shared_key algs tkt
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist169:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist169)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let exts:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat exts pskm
                  <:
                  Bertie.Tls13utils.t_Bytes)
                psk
            in
            let trunc_len:usize = len in
            exts, trunc_len)
        | false, Core.Option.Option_None  ->
          Core.Ops.Control_flow.ControlFlow_Continue (exts, trunc_len)
        | _ ->
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_PSK_MODE_MISMATCH

                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist170:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (exts, trunc_len)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue (exts, trunc_len)
      in
      let* hoist173:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist172:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist172)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist174:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ver
                          cr
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      sid
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  cip
                <:
                Bertie.Tls13utils.t_Bytes)
              comp
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist173
      in
      let hoist175:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message HandshakeType_ClientHello hoist174
      in
      let hoist176:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist175
      in
      let* ch:Bertie.Tls13utils.t_HandshakeData =
        match hoist176 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist171:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist171)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (ch, trunc_len)))

let set_client_hello_binder
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  let Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData = ch in
  let chlen:usize = Bertie.Tls13utils.impl__Bytes__len ch in
  let hlen:usize =
    Bertie.Tls13crypto.hash_len (Bertie.Tls13crypto.hash_alg algs
        <:
        Bertie.Tls13crypto.t_HashAlgorithm)
  in
  match binder, trunc_len with
  | Core.Option.Option_Some m, Core.Option.Option_Some trunc_len ->
    if (chlen -! hlen <: usize) =. trunc_len
    then
      Core.Result.Result_Ok
      (Bertie.Tls13utils.HandshakeData
        (Bertie.Tls13utils.impl__Bytes__update_slice ch trunc_len m (sz 0) hlen))
    else Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok (Bertie.Tls13utils.HandshakeData ch)
  | _, _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

let invalid_compression_list: Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_COMPRESSION_LIST

let parse_client_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (ch: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_ClientHello ch
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist177:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist177)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
      let next:usize = sz 0 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ver
                (Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize }
                    )
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist178:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist178)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let crand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ch
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize })
      in
      let next:usize = next +! sz 32 in
      let* sidlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
                    ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist179:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist179)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let sid:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ch
          ({
              Core.Ops.Range.f_start = next +! sz 1 <: usize;
              Core.Ops.Range.f_end = (next +! sz 1 <: usize) +! sidlen <: usize
            })
      in
      let next:usize = (next +! sz 1 <: usize) +! sidlen in
      let* cslen:usize =
        match
          Core.Ops.Try_trait.f_branch (check_ciphersuites algs
                (Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist180:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist180)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! cslen in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq comp
            (Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize })
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ -> Core.Ops.Control_flow.ControlFlow_Continue ()
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (invalid_compression_list
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist181:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes &
                      Bertie.Tls13utils.t_Bytes &
                      Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                      Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                      usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist181)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist182:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist182)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let* exts:t_EXTS =
        match
          Core.Ops.Try_trait.f_branch (check_extensions algs
                (Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result t_EXTS u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist183:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist183)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let trunc_len:usize =
          ((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -!
            (Bertie.Tls13crypto.hash_len (Bertie.Tls13crypto.hash_alg algs
                  <:
                  Bertie.Tls13crypto.t_HashAlgorithm)
              <:
              usize)
            <:
            usize) -!
          sz 3
        in
        match Bertie.Tls13crypto.psk_mode algs, exts with
        | _, EXTS _ (Core.Option.Option_None ) _ _ ->
          Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_MISSING_KEY_SHARE
        | true,
        EXTS
          (Core.Option.Option_Some sn)
          (Core.Option.Option_Some gx)
          (Core.Option.Option_Some tkt)
          (Core.Option.Option_Some binder) ->
          Core.Result.Result_Ok
          (crand,
            sid,
            sn,
            gx,
            Core.Option.Option_Some tkt,
            Core.Option.Option_Some binder,
            trunc_len)
        | true,
        EXTS
          (Core.Option.Option_None )
          (Core.Option.Option_Some gx)
          (Core.Option.Option_Some tkt)
          (Core.Option.Option_Some binder) ->
          Core.Result.Result_Ok
          (crand,
            sid,
            Bertie.Tls13utils.impl__Bytes__new,
            gx,
            Core.Option.Option_Some tkt,
            Core.Option.Option_Some binder,
            trunc_len)
        | false,
        EXTS
          (Core.Option.Option_Some sn)
          (Core.Option.Option_Some gx)
          (Core.Option.Option_None )
          (Core.Option.Option_None ) ->
          Core.Result.Result_Ok
          (crand, sid, sn, gx, Core.Option.Option_None, Core.Option.Option_None, sz 0)
        | false,
        EXTS
          (Core.Option.Option_None )
          (Core.Option.Option_Some gx)
          (Core.Option.Option_None )
          (Core.Option.Option_None ) ->
          Core.Result.Result_Ok
          (crand,
            sid,
            Bertie.Tls13utils.impl__Bytes__new,
            gx,
            Core.Option.Option_None,
            Core.Option.Option_None,
            sz 0)
        | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)))

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ver:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes2 3uy 3uy
      in
      let* sid:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 sid
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist184:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist184)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist185:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist185)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let* ks:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_key_shares algs gy
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist186:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist186)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* sv:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (server_supported_version algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist187:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist187)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ks sv in
      let* exts:Bertie.Tls13utils.t_Bytes =
        match Bertie.Tls13crypto.psk_mode algs with
        | true ->
          let* hoist189:Bertie.Tls13utils.t_Bytes =
            match
              Core.Ops.Try_trait.f_branch (server_pre_shared_key algs
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist188:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist188)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hoist190:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat exts hoist189
            in
            hoist190)
        | false -> Core.Ops.Control_flow.ControlFlow_Continue exts
      in
      let* hoist193:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 exts
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist192:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist192)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist194:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                  (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ver
                          sr
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      sid
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  cip
                <:
                Bertie.Tls13utils.t_Bytes)
              comp
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist193
      in
      let hoist195:Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
        handshake_message HandshakeType_ServerHello hoist194
      in
      let hoist196:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_HandshakeData =
        Core.Ops.Try_trait.f_branch hoist195
      in
      let* sh:Bertie.Tls13utils.t_HandshakeData =
        match hoist196 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist191:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist191)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok sh))

let unsupported_cipher_alert: Core.Result.t_Result Prims.unit u8 =
  Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM

let parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (sh: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData sh:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_ServerHello sh
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist197:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist197)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* cip:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (ciphersuite algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist198:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist198)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
      let next:usize = sz 0 in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq ver
            (Bertie.Tls13utils.impl__Bytes__slice_range sh
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize })
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ -> Core.Ops.Control_flow.ControlFlow_Continue ()
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (protocol_version_alert
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist199:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist199)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let srand:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range sh
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize })
      in
      let next:usize = next +! sz 32 in
      let* sidlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist200:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist200)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = (next +! sz 1 <: usize) +! sidlen in
      let* _:Prims.unit =
        match
          Bertie.Tls13utils.check_eq cip
            (Bertie.Tls13utils.impl__Bytes__slice_range sh
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 2 <: usize })
              <:
              Bertie.Tls13utils.t_Bytes)
        with
        | Core.Result.Result_Ok _ -> Core.Ops.Control_flow.ControlFlow_Continue ()
        | Core.Result.Result_Err _ ->
          match
            Core.Ops.Try_trait.f_branch (unsupported_cipher_alert
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist201:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist201)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq comp
                (Bertie.Tls13utils.impl__Bytes__slice_range sh
                    ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 1 <: usize }
                    )
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist202:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist202)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 1 in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist203:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist203)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 2 in
      let* gy:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (check_server_extensions algs
                (Bertie.Tls13utils.impl__Bytes__slice_range sh
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sh <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist204:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist204)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (match gy with
        | Core.Option.Option_Some gy -> Core.Result.Result_Ok (srand, gy)
        | _ -> Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE))

let encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (hs_type HandshakeType_EncryptedExtensions <: u8)
      in
      let* hoist207:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist206:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist206)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist208:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
        Bertie.Tls13utils.lbytes3 hoist207
      in
      let hoist209:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
        Core.Ops.Try_trait.f_branch hoist208
      in
      let* hoist210:Bertie.Tls13utils.t_Bytes =
        match hoist209 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist205:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist205)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist211:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ty hoist210 in
        let hoist212:Bertie.Tls13utils.t_HandshakeData = Bertie.Tls13utils.HandshakeData hoist211 in
        Core.Result.Result_Ok hoist212))

let parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (ee: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let Bertie.Tls13utils.HandshakeData ee:Bertie.Tls13utils.t_HandshakeData
      =
        ee
      in
      let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (hs_type HandshakeType_EncryptedExtensions <: u8)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ty
                (Bertie.Tls13utils.impl__Bytes__slice_range ee
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist213:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Prims.unit u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist213)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Bertie.Tls13utils.check_lbytes3_full (Bertie.Tls13utils.impl__Bytes__slice_range ee
              ({
                  Core.Ops.Range.f_start = sz 1;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ee <: usize
                })
            <:
            Bertie.Tls13utils.t_Bytes)))

let server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* creq:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist214:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist214)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* crt:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 cert
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist215:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist215)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist216:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist216)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* crts:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes3 (Bertie.Tls13utils.impl__Bytes__concat
                    crt
                    ext
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist217:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist217)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (handshake_message HandshakeType_Certificate
          (Bertie.Tls13utils.impl__Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes)))

let parse_server_certificate
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (sc: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData sc:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_Certificate sc
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist218:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist218)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = sz 0 in
      let* creqlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = sz 4;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist219:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist219)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = (next +! sz 1 <: usize) +! creqlen in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist220:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist220)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 3 in
      let* crtlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes3 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist221:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist221)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let next:usize = next +! sz 3 in
      let crt:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range sc
          ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! crtlen <: usize })
      in
      let next:usize = next +! crtlen in
      let* v__extlen:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist222:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist222)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok crt))

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sv <: usize) <>. sz 64 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        let b0:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
        let b1:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 48uy in
        let b2:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 2uy in
        let (r: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sv (sz 0) (sz 32)
        in
        let (s: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sv (sz 32) (sz 32)
        in
        let r:Bertie.Tls13utils.t_Bytes =
          if (Bertie.Tls13utils.f_declassify (r.[ sz 0 ] <: Bertie.Tls13utils.t_U8) <: u8) >=. 128uy
          then
            let r:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 r in
            r
          else r
        in
        let s:Bertie.Tls13utils.t_Bytes =
          if (Bertie.Tls13utils.f_declassify (s.[ sz 0 ] <: Bertie.Tls13utils.t_U8) <: u8) >=. 128uy
          then
            let s:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 s in
            s
          else s
        in
        let* hoist225:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 r
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist224:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist224)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let hoist226:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat b2 hoist225
        in
        let hoist229:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist226 b2
        in
        let* hoist228:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 s
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist227:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist227)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let hoist230:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist229 hoist228
        in
        let hoist231:Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
          Bertie.Tls13utils.lbytes1 hoist230
        in
        let hoist232:Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result Core.Convert.t_Infallible u8) Bertie.Tls13utils.t_Bytes =
          Core.Ops.Try_trait.f_branch hoist231
        in
        let* hoist233:Bertie.Tls13utils.t_Bytes =
          match hoist232 with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist223:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist223)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist234:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__concat b1 hoist233
          in
          Core.Result.Result_Ok hoist234))

let check_r_len (rlen: usize) : Core.Result.t_Result Prims.unit u8 =
  if rlen <. sz 32 || rlen >. sz 33
  then Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
  else Core.Result.Result_Ok ()

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 48uy
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  (Bertie.Tls13utils.impl__Bytes__slice_range sig
                      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist235:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist235)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
                      sig
                      ({
                          Core.Ops.Range.f_start = sz 1;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist236:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist236)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  (Bertie.Tls13utils.impl__Bytes__slice_range sig
                      ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist237:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist237)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* rlen:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
                      sig
                      ({
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist238:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist238)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (check_r_len rlen <: Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist239:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist239)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let r:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice sig
            ((sz 4 +! rlen <: usize) -! sz 32 <: usize)
            (sz 32)
        in
        if
          (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <.
          ((sz 6 +! rlen <: usize) +! sz 32 <: usize)
        then
          Core.Ops.Control_flow.ControlFlow_Continue
          (Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE)
        else
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
                      <:
                      Bertie.Tls13utils.t_Bytes)
                    (Bertie.Tls13utils.impl__Bytes__slice_range sig
                        ({
                            Core.Ops.Range.f_start = sz 4 +! rlen <: usize;
                            Core.Ops.Range.f_end = sz 5 +! rlen <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist240:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist240)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          let* _:Prims.unit =
            match
              Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1_full (Bertie.Tls13utils.impl__Bytes__slice_range
                        sig
                        ({
                            Core.Ops.Range.f_start = sz 5 +! rlen <: usize;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
                          })
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist241:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist241)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let s:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__slice sig
                ((Bertie.Tls13utils.impl__Bytes__len sig <: usize) -! sz 32 <: usize)
                (sz 32)
            in
            Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat r s)))

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len cv <: usize) <>. sz 64 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
      else
        let* sv:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (ecdsa_signature cv
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist242:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist242)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* hoist246:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (signature_algorithm algs
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist243:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist243)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* hoist245:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 sv
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist244:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist244)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let sig:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist246 hoist245
        in
        let* hoist248:Bertie.Tls13utils.t_HandshakeData =
          match
            Core.Ops.Try_trait.f_branch (handshake_message HandshakeType_CertificateVerify sig
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist247:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist247)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok hoist248))

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (cv: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData cv:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_CertificateVerify cv
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist249:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist249)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let sa:Bertie.Tls13crypto.t_SignatureScheme = Bertie.Tls13crypto.sig_alg algs in
      let* hoist252:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (signature_algorithm algs
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist251:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist251)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let hoist253:Core.Result.t_Result Prims.unit u8 =
        Bertie.Tls13utils.check_eq hoist252
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 })
            <:
            Bertie.Tls13utils.t_Bytes)
      in
      let hoist254:Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result Core.Convert.t_Infallible u8) Prims.unit =
        Core.Ops.Try_trait.f_branch hoist253
      in
      let* _:Prims.unit =
        match hoist254 with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist250:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist250)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    cv
                    ({
                        Core.Ops.Range.f_start = sz 2;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist255:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist255)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (match sa with
        | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
          parse_ecdsa_signature (Bertie.Tls13utils.impl__Bytes__slice_range cv
                ({
                    Core.Ops.Range.f_start = sz 4;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                  })
              <:
              Bertie.Tls13utils.t_Bytes)
        | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
          Core.Result.Result_Ok
          (Bertie.Tls13utils.impl__Bytes__slice_range cv
              ({
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                }))
        | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
          if ((Bertie.Tls13utils.impl__Bytes__len cv <: usize) -! sz 4 <: usize) =. sz 64
          then
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__slice_range cv
                ({
                    Core.Ops.Range.f_start = sz 8;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                  }))
          else Bertie.Tls13utils.tlserr Bertie.Tls13utils.v_INVALID_SIGNATURE))

let finished (v__algs: Bertie.Tls13crypto.t_Algorithms) (vd: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  handshake_message HandshakeType_Finished vd

let parse_finished
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (fin: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData fin:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_Finished fin
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist256:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist256)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok fin))

let session_ticket (v__algs: Bertie.Tls13crypto.t_Algorithms) (tkt: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let lifetime:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 172800ul
            <:
            Bertie.Tls13utils.t_U32)
      in
      let age:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__U32__to_be_bytes (Core.Convert.f_from 9999ul
            <:
            Bertie.Tls13utils.t_U32)
      in
      let* nonce:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes1 (Bertie.Tls13utils.bytes1 1uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist257:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist257)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* stkt:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist258:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist258)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist260:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 (Bertie.Tls13utils.impl__Bytes__new
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist259:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist259)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let grease_ext:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 90uy 90uy
            <:
            Bertie.Tls13utils.t_Bytes)
          hoist260
      in
      let* ext:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 grease_ext
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist261:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist261)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (handshake_message HandshakeType_NewSessionTicket
          (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                      (Bertie.Tls13utils.impl__Bytes__concat lifetime age
                        <:
                        Bertie.Tls13utils.t_Bytes)
                      nonce
                    <:
                    Bertie.Tls13utils.t_Bytes)
                  stkt
                <:
                Bertie.Tls13utils.t_Bytes)
              ext
            <:
            Bertie.Tls13utils.t_Bytes)))

let parse_session_ticket
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (tkt: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* Bertie.Tls13utils.HandshakeData tkt:Bertie.Tls13utils.t_HandshakeData
      =
        match
          Core.Ops.Try_trait.f_branch (get_handshake_message_ty HandshakeType_NewSessionTicket tkt
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist262:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist262)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* lifetime:Bertie.Tls13utils.t_U32 =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__U32__from_be_bytes (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_U32 u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist263:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist263)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* age:Bertie.Tls13utils.t_U32 =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__U32__from_be_bytes (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({ Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 8 })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_U32 u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist264:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist264)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* nonce_len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes1 (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = sz 8;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist265:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist265)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* stkt_len:usize =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = sz 9 +! nonce_len <: usize;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist266:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist266)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let stkt:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range tkt
          ({
              Core.Ops.Range.f_start = sz 11 +! nonce_len <: usize;
              Core.Ops.Range.f_end = (sz 11 +! nonce_len <: usize) +! stkt_len <: usize
            })
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2_full (Bertie.Tls13utils.impl__Bytes__slice_range
                    tkt
                    ({
                        Core.Ops.Range.f_start = (sz 11 +! nonce_len <: usize) +! stkt_len <: usize;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len tkt <: usize
                      })
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist267:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_U32 & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist267)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok (lifetime +! age, stkt)))

type t_ContentType =
  | ContentType_Invalid : t_ContentType
  | ContentType_ChangeCipherSpec : t_ContentType
  | ContentType_Alert : t_ContentType
  | ContentType_Handshake : t_ContentType
  | ContentType_ApplicationData : t_ContentType

let content_type (t: t_ContentType) : u8 =
  match t with
  | ContentType_Invalid  -> 0uy
  | ContentType_ChangeCipherSpec  -> 20uy
  | ContentType_Alert  -> 21uy
  | ContentType_Handshake  -> 22uy
  | ContentType_ApplicationData  -> 23uy

let get_content_type (t: u8) : Core.Result.t_Result t_ContentType u8 =
  match t with
  | 0uy -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
  | 20uy -> Core.Result.Result_Ok ContentType_ChangeCipherSpec
  | 21uy -> Core.Result.Result_Ok ContentType_Alert
  | 22uy -> Core.Result.Result_Ok ContentType_Handshake
  | 23uy -> Core.Result.Result_Ok ContentType_ApplicationData
  | _ -> Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)

let handshake_record (p: Bertie.Tls13utils.t_HandshakeData)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let Bertie.Tls13utils.HandshakeData p:Bertie.Tls13utils.t_HandshakeData
      =
        p
      in
      let ty:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (content_type ContentType_Handshake <: u8)
      in
      let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
      let* hoist269:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.lbytes2 p
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist268:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist268)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist270:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist269
        in
        Core.Result.Result_Ok hoist270))

let protocol_version_alert: Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_PROTOCOL_VERSION_ALERT

let application_data_instead_of_handshake: Core.Result.t_Result Prims.unit u8 =
  Core.Result.Result_Err Bertie.Tls13utils.v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 5 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
      else
        let ty:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.bytes1 (content_type ContentType_Handshake <: u8)
        in
        let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
        let* _:Prims.unit =
          match
            Bertie.Tls13utils.check_eq ty
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 })
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok _ -> Core.Ops.Control_flow.ControlFlow_Continue ()
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (application_data_instead_of_handshake
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist271:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist271)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* _:Prims.unit =
          match
            Bertie.Tls13utils.check_eq ver
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 3 })
                <:
                Bertie.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok _ -> Core.Ops.Control_flow.ControlFlow_Continue ()
          | Core.Result.Result_Err _ ->
            match
              Core.Ops.Try_trait.f_branch (protocol_version_alert
                  <:
                  Core.Result.t_Result Prims.unit u8)
            with
            | Core.Ops.Control_flow.ControlFlow_Break residual ->
              let* hoist272:Rust_primitives.Hax.t_Never =
                Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
              in
              Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist272)
            | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
              Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_lbytes2 (Bertie.Tls13utils.impl__Bytes__slice_range
                      p
                      ({
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
                        })
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist273:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist273)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Ok
          (Bertie.Tls13utils.HandshakeData
            (Bertie.Tls13utils.impl__Bytes__slice_range p
                ({ Core.Ops.Range.f_start = sz 5; Core.Ops.Range.f_end = sz 5 +! len <: usize })),
            sz 5 +! len)))

let get_handshake_record (p: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hd, len:(Bertie.Tls13utils.t_HandshakeData &
        usize) =
        match
          Core.Ops.Try_trait.f_branch (check_handshake_record p
              <:
              Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist274:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist274)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if len =. (Bertie.Tls13utils.impl__Bytes__len p <: usize)
        then Core.Result.Result_Ok hd
        else Bertie.Tls13utils.tlserr (Bertie.parse_failed <: u8)))

type t_Transcript =
  | Transcript : Bertie.Tls13crypto.t_HashAlgorithm -> Bertie.Tls13utils.t_HandshakeData
    -> t_Transcript

let transcript_empty (ha: Bertie.Tls13crypto.t_HashAlgorithm) : t_Transcript =
  Transcript ha (Bertie.Tls13utils.HandshakeData Bertie.Tls13utils.impl__Bytes__new)

let transcript_add1 (tx: t_Transcript) (msg: Bertie.Tls13utils.t_HandshakeData) : t_Transcript =
  let Transcript ha tx:t_Transcript = tx in
  Transcript ha (Bertie.Tls13utils.handshake_concat tx msg)

let get_transcript_hash (tx: t_Transcript) : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let
      Transcript ha (Bertie.Tls13utils.HandshakeData txby):t_Transcript =
        tx
      in
      let* th:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.hash ha txby
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist275:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist275)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Core.Result.Result_Ok th))

let get_transcript_hash_truncated_client_hello
      (tx: t_Transcript)
      (ch: Bertie.Tls13utils.t_HandshakeData)
      (trunc_len: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  let Transcript ha (Bertie.Tls13utils.HandshakeData tx):t_Transcript = tx in
  let Bertie.Tls13utils.HandshakeData ch:Bertie.Tls13utils.t_HandshakeData = ch in
  Bertie.Tls13crypto.hash ha
    (Bertie.Tls13utils.impl__Bytes__concat tx
        (Bertie.Tls13utils.impl__Bytes__slice_range ch
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = trunc_len })
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Bertie.Tls13utils.t_Bytes)