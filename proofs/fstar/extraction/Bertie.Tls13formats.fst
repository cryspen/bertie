module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

let build_server_name (name: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
          #FStar.Tactics.Typeclasses.solve
          name
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist4 ->
    (match
        Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl_Bytes__prefix hoist4
              (build_server_name__v_PREFIX2 <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist7 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist7
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist9 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl_Bytes__prefix hoist9
                (build_server_name__v_PREFIX1 <: t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_server_name (extension: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice extension
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13utils.check_eq_with_slice ((let list = [Bertie.Tls13utils.v_U8 (mk_u8 0)] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
          extension
          (mk_usize 2)
          (mk_usize 3)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        (match
            Bertie.Tls13utils.check_length_encoding_u16_slice (extension.[ {
                    Core.Ops.Range.f_start = mk_usize 3;
                    Core.Ops.Range.f_end = Core.Slice.impl__len #u8 extension <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            Core.Result.Result_Ok
            (Core.Convert.f_into #(t_Slice u8)
                #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                (extension.[ {
                      Core.Ops.Range.f_start = mk_usize 5;
                      Core.Ops.Range.f_end = Core.Slice.impl__len #u8 extension <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let supported_versions (_: Prims.unit) =
  match
    Bertie.Tls13utils.encode_length_u8 ((let list =
            [Bertie.Tls13utils.v_U8 (mk_u8 3); Bertie.Tls13utils.v_U8 (mk_u8 4)]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist11 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist11
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist13 ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl_Bytes__concat (Core.Convert.f_from #Bertie.Tls13utils.t_Bytes
                #(t_Array u8 (mk_usize 2))
                #FStar.Tactics.Typeclasses.solve
                (let list = [mk_u8 0; mk_u8 43] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list 2 list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist13)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_supported_versions (client_hello: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    Bertie.Tls13utils.check_mem ((let list =
            [Bertie.Tls13utils.v_U8 (mk_u8 3); Bertie.Tls13utils.v_U8 (mk_u8 4)]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
      (client_hello.[ {
            Core.Ops.Range.f_start = mk_usize 1;
            Core.Ops.Range.f_end = Core.Slice.impl__len #u8 client_hello <: usize
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let server_supported_version (e_algorithms: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 4)
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist15 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl_Bytes__prefix hoist15
        (server_supported_version__v_SUPPORTED_VERSION_PREFIX <: t_Slice u8))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_server_supported_version (e_algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  Bertie.Tls13utils.check_eq_slice ((let list =
          [Bertie.Tls13utils.v_U8 (mk_u8 3); Bertie.Tls13utils.v_U8 (mk_u8 4)]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    b

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13crypto.impl_Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist17 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist17
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist19 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist19
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist21 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl_Bytes__prefix hoist21
                (supported_groups__v_SUPPORTED_GROUPS_PREFIX <: t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__supported_group algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist23 ->
        Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl_Bytes__as_raw hoist23 <: t_Slice u8)
          (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13crypto.impl_Algorithms__signature_algorithm algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist25 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist25
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist27 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist27
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist29 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 13)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                hoist29)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist31 ->
        Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl_Bytes__as_raw hoist31 <: t_Slice u8)
          (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let psk_key_exchange_modes (_: Prims.unit) =
  match
    Bertie.Tls13utils.encode_length_u8 ((let list = [Bertie.Tls13utils.v_U8 (mk_u8 1)] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist33 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist33
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist35 ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl_Bytes__prefix hoist35
            (psk_key_exchange_modes__v_PSK_MODE_PREFIX <: t_Slice u8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_psk_key_exchange_modes (client_hello: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    Bertie.Tls13utils.check_eq_with_slice ((let list = [Bertie.Tls13utils.v_U8 (mk_u8 1)] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
      client_hello
      (mk_usize 1)
      (mk_usize 2)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13crypto.impl_Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist38 ->
    (match
        Bertie.Tls13utils.encode_length_u16 gx <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist37 ->
        let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl_Bytes__concat hoist38 hoist37 in
        (match
            Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist39 ->
            (match
                Bertie.Tls13utils.encode_length_u16 hoist39
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok hoist41 ->
                Core.Result.Result_Ok
                (Bertie.Tls13utils.impl_Bytes__prefix hoist41 (key_shares__v_PREFIX <: t_Slice u8))
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13crypto.impl_Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist45 ->
    (match
        Bertie.Tls13utils.encode_length_u16 gx <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist44 ->
        let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl_Bytes__concat hoist45 hoist44 in
        (match
            Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist46 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 51)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                hoist46)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  match
    Bertie.Tls13crypto.impl_Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist48 ->
    (match
        Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw hoist48
            <:
            t_Slice u8)
          b
          (mk_usize 0)
          (mk_usize 2)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        (match
            Bertie.Tls13utils.check_length_encoding_u16_slice (b.[ {
                    Core.Ops.Range.f_start = mk_usize 2;
                    Core.Ops.Range.f_end = Core.Slice.impl__len #u8 b <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            Core.Result.Result_Ok
            (Core.Convert.f_from #Bertie.Tls13utils.t_Bytes
                #(t_Slice u8)
                #FStar.Tactics.Typeclasses.solve
                (b.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = Core.Slice.impl__len #u8 b <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let pre_shared_key
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket: Bertie.Tls13utils.t_Bytes)
     =
  match
    Bertie.Tls13utils.encode_length_u16 (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
          #FStar.Tactics.Typeclasses.solve
          session_ticket
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist51 ->
    (match
        Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl_Bytes__concat_array (mk_usize 4)
              hoist51
              (Bertie.Tls13utils.u32_as_be_bytes (Bertie.Tls13utils.v_U32 (mk_u32 4294967295) <: u32
                  )
                <:
                t_Array u8 (mk_usize 4))
            <:
            Bertie.Tls13utils.t_Bytes)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok identities ->
        (match
            Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw (Bertie.Tls13crypto.zero_key
                      (Bertie.Tls13crypto.impl_Algorithms__hash algs
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist54 ->
            (match
                Bertie.Tls13utils.encode_length_u16 hoist54
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok binders ->
                let binders_len:usize = Bertie.Tls13utils.impl_Bytes__len binders in
                (match
                    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl_Bytes__concat identities
                          binders
                        <:
                        Bertie.Tls13utils.t_Bytes)
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok hoist56 ->
                    let ext:Bertie.Tls13utils.t_Bytes =
                      Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.bytes2 (mk_u8 0)
                            (mk_u8 41)
                          <:
                          Bertie.Tls13utils.t_Bytes)
                        hoist56
                    in
                    Core.Result.Result_Ok (ext, binders_len <: (Bertie.Tls13utils.t_Bytes & usize))
                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8

let check_psk_shared_key (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match Bertie.Tls13utils.length_u16_encoded ch <: Core.Result.t_Result usize u8 with
  | Core.Result.Result_Ok len_id ->
    (match
        Bertie.Tls13utils.length_u16_encoded (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = mk_usize 2 +! len_id <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok len_tkt ->
        if len_id =. (len_tkt +! mk_usize 6 <: usize)
        then
          match
            Bertie.Tls13utils.check_length_encoding_u16_slice (ch.[ {
                    Core.Ops.Range.f_start = mk_usize 2 +! len_id <: usize;
                    Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            (match
                Bertie.Tls13utils.check_length_encoding_u8_slice (ch.[ {
                        Core.Ops.Range.f_start = mk_usize 4 +! len_id <: usize;
                        Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result Prims.unit u8
              with
              | Core.Result.Result_Ok _ ->
                if
                  (((Core.Slice.impl__len #u8 ch <: usize) -! mk_usize 5 <: usize) -! len_id
                    <:
                    usize) <>.
                  (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len (Bertie.Tls13crypto.impl_Algorithms__hash
                          algs
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                    <:
                    usize)
                then Bertie.Tls13utils.tlserr #Prims.unit (Bertie.Tls13utils.parse_failed () <: u8)
                else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8
        else Bertie.Tls13utils.tlserr #Prims.unit (Bertie.Tls13utils.parse_failed () <: u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let server_pre_shared_key (e_algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 0)
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist57 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.bytes2 (mk_u8 0) (mk_u8 41)
          <:
          Bertie.Tls13utils.t_Bytes)
        hoist57)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_server_psk_shared_key (e_algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  Bertie.Tls13utils.check_eq_slice ((let list =
          [Bertie.Tls13utils.v_U8 (mk_u8 0); Bertie.Tls13utils.v_U8 (mk_u8 0)]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    b

let merge_opts (#v_T: Type0) (o1 o2: Core.Option.t_Option v_T) =
  match o1, o2 <: (Core.Option.t_Option v_T & Core.Option.t_Option v_T) with
  | Core.Option.Option_None , Core.Option.Option_Some o ->
    Core.Result.Result_Ok (Core.Option.Option_Some o <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | Core.Option.Option_Some o, Core.Option.Option_None  ->
    Core.Result.Result_Ok (Core.Option.Option_Some o <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok (Core.Option.Option_None <: Core.Option.t_Option v_T)
    <:
    Core.Result.t_Result (Core.Option.t_Option v_T) u8
  | _ ->
    Bertie.Tls13utils.tlserr #(Core.Option.t_Option v_T) (Bertie.Tls13utils.parse_failed () <: u8)

let impl_Extensions__merge (self e2: t_Extensions) =
  match
    merge_opts #Bertie.Tls13utils.t_Bytes self.f_sni e2.f_sni
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok hoist62 ->
    (match
        merge_opts #Bertie.Tls13utils.t_Bytes self.f_key_share e2.f_key_share
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
      with
      | Core.Result.Result_Ok hoist61 ->
        (match
            merge_opts #Bertie.Tls13utils.t_Bytes self.f_ticket e2.f_ticket
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
          with
          | Core.Result.Result_Ok hoist60 ->
            (match
                merge_opts #Bertie.Tls13utils.t_Bytes self.f_binder e2.f_binder
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok hoist59 ->
                Core.Result.Result_Ok
                ({ f_sni = hoist62; f_key_share = hoist61; f_ticket = hoist60; f_binder = hoist59 }
                  <:
                  t_Extensions)
                <:
                Core.Result.t_Result t_Extensions u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8

let check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  if (Core.Slice.impl__len #u8 b <: usize) <. mk_usize 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
  else
    let l0:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (b.[ mk_usize 0 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    let l1:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (b.[ mk_usize 1 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    match
      Bertie.Tls13utils.length_u16_encoded (b.[ {
              Core.Ops.Range.f_start = mk_usize 2;
              Core.Ops.Range.f_end = Core.Slice.impl__len #u8 b <: usize
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result usize u8
    with
    | Core.Result.Result_Ok len ->
      let out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
        Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
      in
      (match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 43 ->
          (match
              check_server_supported_version algs
                (b.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok ok ->
              Core.Result.Result_Ok
              (mk_usize 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 51 ->
          (match
              check_server_key_share algs
                (b.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok gx ->
              let out:Core.Option.t_Option Bertie.Tls13utils.t_Bytes =
                Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
              in
              Core.Result.Result_Ok
              (mk_usize 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 41 ->
          (match
              check_server_psk_shared_key algs
                (b.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok ok ->
              Core.Result.Result_Ok
              (mk_usize 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | _ ->
          Core.Result.Result_Ok
          (mk_usize 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8

let t_AlertLevel_cast_to_repr (x: t_AlertLevel) =
  match x <: t_AlertLevel with
  | AlertLevel_Warning  -> anon_const_AlertLevel_Warning__anon_const_0
  | AlertLevel_Fatal  -> anon_const_AlertLevel_Fatal__anon_const_0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Clone.t_Clone t_AlertLevel

let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Marker.t_Copy t_AlertLevel

let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core.Fmt.t_Debug t_AlertLevel

let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Marker.t_StructuralPartialEq t_AlertLevel

let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core.Cmp.t_PartialEq t_AlertLevel t_AlertLevel

let impl_10 = impl_10'

let t_AlertDescription_cast_to_repr (x: t_AlertDescription) =
  match x <: t_AlertDescription with
  | AlertDescription_CloseNotify  -> anon_const_AlertDescription_CloseNotify__anon_const_0
  | AlertDescription_UnexpectedMessage  ->
    anon_const_AlertDescription_UnexpectedMessage__anon_const_0
  | AlertDescription_BadRecordMac  -> anon_const_AlertDescription_BadRecordMac__anon_const_0
  | AlertDescription_RecordOverflow  -> anon_const_AlertDescription_RecordOverflow__anon_const_0
  | AlertDescription_HandshakeFailure  -> anon_const_AlertDescription_HandshakeFailure__anon_const_0
  | AlertDescription_BadCertificate  -> anon_const_AlertDescription_BadCertificate__anon_const_0
  | AlertDescription_UnsupportedCertificate  ->
    anon_const_AlertDescription_UnsupportedCertificate__anon_const_0
  | AlertDescription_CertificateRevoked  ->
    anon_const_AlertDescription_CertificateRevoked__anon_const_0
  | AlertDescription_CertificateExpired  ->
    anon_const_AlertDescription_CertificateExpired__anon_const_0
  | AlertDescription_CertificateUnknown  ->
    anon_const_AlertDescription_CertificateUnknown__anon_const_0
  | AlertDescription_IllegalParameter  -> anon_const_AlertDescription_IllegalParameter__anon_const_0
  | AlertDescription_UnknownCa  -> anon_const_AlertDescription_UnknownCa__anon_const_0
  | AlertDescription_AccessDenied  -> anon_const_AlertDescription_AccessDenied__anon_const_0
  | AlertDescription_DecodeError  -> anon_const_AlertDescription_DecodeError__anon_const_0
  | AlertDescription_DecryptError  -> anon_const_AlertDescription_DecryptError__anon_const_0
  | AlertDescription_ProtocolVersion  -> anon_const_AlertDescription_ProtocolVersion__anon_const_0
  | AlertDescription_InsufficientSecurity  ->
    anon_const_AlertDescription_InsufficientSecurity__anon_const_0
  | AlertDescription_InternalError  -> anon_const_AlertDescription_InternalError__anon_const_0
  | AlertDescription_InappropriateFallback  ->
    anon_const_AlertDescription_InappropriateFallback__anon_const_0
  | AlertDescription_UserCanceled  -> anon_const_AlertDescription_UserCanceled__anon_const_0
  | AlertDescription_MissingExtension  -> anon_const_AlertDescription_MissingExtension__anon_const_0
  | AlertDescription_UnsupportedExtension  ->
    anon_const_AlertDescription_UnsupportedExtension__anon_const_0
  | AlertDescription_UnrecognizedName  -> anon_const_AlertDescription_UnrecognizedName__anon_const_0
  | AlertDescription_BadCertificateStatusResponse  ->
    anon_const_AlertDescription_BadCertificateStatusResponse__anon_const_0
  | AlertDescription_UnknownPskIdentity  ->
    anon_const_AlertDescription_UnknownPskIdentity__anon_const_0
  | AlertDescription_CertificateRequired  ->
    anon_const_AlertDescription_CertificateRequired__anon_const_0
  | AlertDescription_NoApplicationProtocol  ->
    anon_const_AlertDescription_NoApplicationProtocol__anon_const_0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core.Clone.t_Clone t_AlertDescription

let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core.Marker.t_Copy t_AlertDescription

let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core.Fmt.t_Debug t_AlertDescription

let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core.Marker.t_StructuralPartialEq t_AlertDescription

let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core.Cmp.t_PartialEq t_AlertDescription t_AlertDescription

let impl_15 = impl_15'

let get_psk_extensions
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (session_ticket extensions: Bertie.Tls13utils.t_Bytes)
     =
  match psk_key_exchange_modes () <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
  | Core.Result.Result_Ok pskm ->
    (match
        pre_shared_key algorithms session_ticket
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & usize) u8
      with
      | Core.Result.Result_Ok (psk, len) ->
        let extensions:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__concat extensions pskm
              <:
              Bertie.Tls13utils.t_Bytes)
            psk
        in
        Core.Result.Result_Ok (len, extensions <: (usize & Bertie.Tls13utils.t_Bytes))
        <:
        Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8

let client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
     =
  let version:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
  let compression_methods:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes2 (mk_u8 1) (mk_u8 0)
  in
  match
    Bertie.Tls13utils.encode_length_u8 (Rust_primitives.Hax.repeat (Bertie.Tls13utils.v_U8 (mk_u8 0)
            <:
            u8)
          (mk_usize 32)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok legacy_session_id ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__ciphersuite algorithms
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist68 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist68
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok cipher_suites ->
            (match
                build_server_name server_name <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok server_name ->
                (match
                    supported_versions () <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok supported_versions ->
                    (match
                        supported_groups algorithms
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      with
                      | Core.Result.Result_Ok supported_groups ->
                        (match
                            signature_algorithms algorithms
                            <:
                            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                          with
                          | Core.Result.Result_Ok signature_algorithms ->
                            (match
                                key_shares algorithms
                                  (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                                      #FStar.Tactics.Typeclasses.solve
                                      kem_pk
                                    <:
                                    Bertie.Tls13utils.t_Bytes)
                                <:
                                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                              with
                              | Core.Result.Result_Ok key_shares ->
                                let len:usize =
                                  (Bertie.Tls13utils.impl_Bytes__len server_name <: usize) +!
                                  (Bertie.Tls13utils.impl_Bytes__len supported_versions <: usize)
                                in
                                let len:usize =
                                  len +!
                                  (Bertie.Tls13utils.impl_Bytes__len supported_groups <: usize)
                                in
                                let len:usize =
                                  len +!
                                  (Bertie.Tls13utils.impl_Bytes__len signature_algorithms <: usize)
                                in
                                let len:usize =
                                  len +! (Bertie.Tls13utils.impl_Bytes__len key_shares <: usize)
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__new_alloc len
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__append out server_name
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__append out supported_versions
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__append out supported_groups
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__append out signature_algorithms
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__append out key_shares
                                in
                                let extensions:Bertie.Tls13utils.t_Bytes = out in
                                (match
                                    (match
                                        Bertie.Tls13crypto.impl_Algorithms__psk_mode algorithms,
                                        session_ticket
                                        <:
                                        (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                                      with
                                      | true, Core.Option.Option_Some session_ticket ->
                                        get_psk_extensions algorithms session_ticket extensions
                                      | false, Core.Option.Option_None  ->
                                        Core.Result.Result_Ok
                                        (mk_usize 0, extensions
                                          <:
                                          (usize & Bertie.Tls13utils.t_Bytes))
                                        <:
                                        Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8
                                      | _ ->
                                        Bertie.Tls13utils.tlserr #(usize & Bertie.Tls13utils.t_Bytes
                                          )
                                          Bertie.Tls13utils.v_PSK_MODE_MISMATCH)
                                    <:
                                    Core.Result.t_Result (usize & Bertie.Tls13utils.t_Bytes) u8
                                  with
                                  | Core.Result.Result_Ok (trunc_len, extensions) ->
                                    (match
                                        Bertie.Tls13utils.encode_length_u16 extensions
                                        <:
                                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                                      with
                                      | Core.Result.Result_Ok encoded_extensions ->
                                        let len:usize =
                                          (Bertie.Tls13utils.impl_Bytes__len version <: usize) +!
                                          (Bertie.Tls13utils.impl_Bytes__len client_random <: usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl_Bytes__len legacy_session_id
                                            <:
                                            usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl_Bytes__len cipher_suites <: usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl_Bytes__len compression_methods
                                            <:
                                            usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl_Bytes__len encoded_extensions
                                            <:
                                            usize)
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__new_alloc len
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out version
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out client_random
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out legacy_session_id
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out cipher_suites
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out
                                            compression_methods
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl_Bytes__append out
                                            encoded_extensions
                                        in
                                        let handshake_bytes:Bertie.Tls13utils.t_Bytes = out in
                                        (match
                                            Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes
                                              (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
                                                <:
                                                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                                              handshake_bytes
                                            <:
                                            Core.Result.t_Result
                                              Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                                          with
                                          | Core.Result.Result_Ok client_hello ->
                                            Core.Result.Result_Ok
                                            (client_hello, trunc_len
                                              <:
                                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                                usize))
                                            <:
                                            Core.Result.t_Result
                                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                                usize) u8
                                          | Core.Result.Result_Err err ->
                                            Core.Result.Result_Err err
                                            <:
                                            Core.Result.t_Result
                                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                                usize) u8)
                                      | Core.Result.Result_Err err ->
                                        Core.Result.Result_Err err
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13formats.Handshake_data.t_HandshakeData &
                                            usize) u8)
                                  | Core.Result.Result_Err err ->
                                    Core.Result.Result_Err err
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                                      u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
            )
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8

let set_client_hello_binder
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (binder: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: Core.Option.t_Option usize)
     =
  let Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    client_hello
  in
  let chlen:usize = Bertie.Tls13utils.impl_Bytes__len ch in
  let hlen:usize =
    Bertie.Tls13crypto.impl_HashAlgorithm__hash_len (Bertie.Tls13crypto.impl_Algorithms__hash ciphersuite

        <:
        Bertie.Tls13crypto.t_HashAlgorithm)
  in
  match
    binder, trunc_len
    <:
    (Core.Option.t_Option Bertie.Tls13utils.t_Bytes & Core.Option.t_Option usize)
  with
  | Core.Option.Option_Some m, Core.Option.Option_Some trunc_len ->
    if (chlen -! hlen <: usize) =. trunc_len
    then
      Core.Result.Result_Ok
      (Bertie.Tls13formats.Handshake_data.HandshakeData
        (Bertie.Tls13utils.impl_Bytes__update_slice ch trunc_len m (mk_usize 0) hlen)
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      <:
      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
    else
      Bertie.Tls13utils.tlserr #Bertie.Tls13formats.Handshake_data.t_HandshakeData
        (Bertie.Tls13utils.parse_failed () <: u8)
  | Core.Option.Option_None , Core.Option.Option_None  ->
    Core.Result.Result_Ok
    (Bertie.Tls13formats.Handshake_data.HandshakeData ch
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeData)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  | _, _ ->
    Bertie.Tls13utils.tlserr #Bertie.Tls13formats.Handshake_data.t_HandshakeData
      (Bertie.Tls13utils.parse_failed () <: u8)

let invalid_compression_list (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_COMPRESSION_LIST
  <:
  Core.Result.t_Result Prims.unit u8

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes) =
  let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
  match
    Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw sid <: t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok sid ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__ciphersuite algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok cip ->
        let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (mk_u8 0) in
        (match
            server_key_shares algs
              (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve gy
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok ks ->
            (match
                server_supported_version algs <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok sv ->
                let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl_Bytes__concat ks sv in
                if Bertie.Tls13crypto.impl_Algorithms__psk_mode algs
                then
                  match
                    server_pre_shared_key algs <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok hoist70 ->
                    let exts:Bertie.Tls13utils.t_Bytes =
                      Bertie.Tls13utils.impl_Bytes__concat exts hoist70
                    in
                    (match
                        Bertie.Tls13utils.encode_length_u16 exts
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      with
                      | Core.Result.Result_Ok encoded_extensions ->
                        let len:usize =
                          (Bertie.Tls13utils.impl_Bytes__len ver <: usize) +!
                          (Bertie.Tls13utils.impl_Bytes__len sr <: usize)
                        in
                        let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len sid <: usize) in
                        let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len cip <: usize) in
                        let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len comp <: usize) in
                        let len:usize =
                          len +! (Bertie.Tls13utils.impl_Bytes__len encoded_extensions <: usize)
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__new_alloc len
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out ver
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out sr
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out sid
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out cip
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out comp
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__append out encoded_extensions
                        in
                        (match
                            Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
                                <:
                                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                              out
                            <:
                            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData
                              u8
                          with
                          | Core.Result.Result_Ok sh ->
                            Core.Result.Result_Ok sh
                            <:
                            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData
                              u8
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData
                              u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                else
                  (match
                      Bertie.Tls13utils.encode_length_u16 exts
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                    with
                    | Core.Result.Result_Ok encoded_extensions ->
                      let len:usize =
                        (Bertie.Tls13utils.impl_Bytes__len ver <: usize) +!
                        (Bertie.Tls13utils.impl_Bytes__len sr <: usize)
                      in
                      let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len sid <: usize) in
                      let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len cip <: usize) in
                      let len:usize = len +! (Bertie.Tls13utils.impl_Bytes__len comp <: usize) in
                      let len:usize =
                        len +! (Bertie.Tls13utils.impl_Bytes__len encoded_extensions <: usize)
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__new_alloc len
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out ver
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out sr
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out sid
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out cip
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out comp
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__append out encoded_extensions
                      in
                      (match
                          Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
                              <:
                              Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                            out
                          <:
                          Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                        with
                        | Core.Result.Result_Ok sh ->
                          Core.Result.Result_Ok sh
                          <:
                          Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                        | Core.Result.Result_Err err ->
                          Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
                      )
                    | Core.Result.Result_Err err ->
                      Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8

let unsupported_cipher_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  <:
  Core.Result.t_Result Prims.unit u8

let invalid_compression_method_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_DECODE_ERROR <: Core.Result.t_Result Prims.unit u8

let encrypted_extensions (e_algs: Bertie.Tls13crypto.t_Algorithms) =
  let handshake_type:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.anon_const_HandshakeType_EncryptedExtensions__anon_const_0 +!
            mk_u8 0
            <:
            u8)
        <:
        u8)
  in
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl_Bytes__new ()
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist74 ->
    (match
        Bertie.Tls13utils.encode_length_u24 hoist74
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist76 ->
        Core.Result.Result_Ok
        (Bertie.Tls13formats.Handshake_data.HandshakeData
          (Bertie.Tls13utils.impl_Bytes__concat handshake_type hoist76)
          <:
          Bertie.Tls13formats.Handshake_data.t_HandshakeData)
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8

let parse_encrypted_extensions
      (e_algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  let Bertie.Tls13formats.Handshake_data.HandshakeData encrypted_extension_bytes:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    encrypted_extensions
  in
  let expected_handshake_type:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.anon_const_HandshakeType_EncryptedExtensions__anon_const_0 +!
            mk_u8 0
            <:
            u8)
        <:
        u8)
  in
  match
    Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw expected_handshake_type

        <:
        t_Slice u8)
      (Bertie.Tls13utils.impl_Bytes__as_raw encrypted_extension_bytes <: t_Slice u8)
      (mk_usize 0)
      (mk_usize 1)
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl_Bytes__raw_slice encrypted_extension_bytes
          ({
              Core.Ops.Range.f_start = mk_usize 1;
              Core.Ops.Range.f_end
              =
              Bertie.Tls13utils.impl_Bytes__len encrypted_extension_bytes <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        t_Slice u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let server_certificate (e_algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13utils.encode_length_u8 ((let list:Prims.list u8 = [] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
          Rust_primitives.Hax.array_of_list 0 list)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok creq ->
    (match
        Bertie.Tls13utils.encode_length_u24 cert
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok crt ->
        (match
            Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl_Bytes__new ()
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok ext ->
            (match
                Bertie.Tls13utils.encode_length_u24 (Bertie.Tls13utils.impl_Bytes__concat crt ext
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok crts ->
                Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                  (Bertie.Tls13utils.impl_Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8

let parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  match
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__as_handshake_message certificate
      (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData sc) ->
    let next:usize = mk_usize 0 in
    (match
        Bertie.Tls13utils.length_u8_encoded (sc.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sc <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok creqlen ->
        let next:usize = (next +! mk_usize 1 <: usize) +! creqlen in
        (match
            Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl_Bytes__raw_slice sc
                  ({
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let next:usize = next +! mk_usize 3 in
            (match
                Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl_Bytes__raw_slice sc
                      ({
                          Core.Ops.Range.f_start = next;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sc <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8
              with
              | Core.Result.Result_Ok crtlen ->
                let next:usize = next +! mk_usize 3 in
                let crt:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl_Bytes__slice_range sc
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = next +! crtlen <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                in
                let next:usize = next +! crtlen in
                (match
                    Bertie.Tls13utils.length_u16_encoded (sc.[ {
                            Core.Ops.Range.f_start = next;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sc <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result usize u8
                  with
                  | Core.Result.Result_Ok e_extlen ->
                    Core.Result.Result_Ok crt <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl_Bytes__len sv <: usize) <>. mk_usize 64
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    let b0:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (mk_u8 0) in
    let b1:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (mk_u8 48) in
    let b2:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (mk_u8 2) in
    let (r: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__slice sv (mk_usize 0) (mk_usize 32)
    in
    let (s: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__slice sv (mk_usize 32) (mk_usize 32)
    in
    let r:Bertie.Tls13utils.t_Bytes =
      if
        (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (r.[ mk_usize 0 ] <: u8)
          <:
          u8) >=.
        mk_u8 128
      then
        let r:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl_Bytes__concat (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                #FStar.Tactics.Typeclasses.solve
                b0
              <:
              Bertie.Tls13utils.t_Bytes)
            r
        in
        r
      else r
    in
    let s:Bertie.Tls13utils.t_Bytes =
      if
        (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (s.[ mk_usize 0 ] <: u8)
          <:
          u8) >=.
        mk_u8 128
      then
        let s:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl_Bytes__concat b0 s in
        s
      else s
    in
    match
      Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw r <: t_Slice u8)
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    with
    | Core.Result.Result_Ok hoist79 ->
      (match
          Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw s <: t_Slice u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok hoist81 ->
          (match
              Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw (Bertie.Tls13utils.impl_Bytes__concat
                        (Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__concat (
                                  Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                                    #FStar.Tactics.Typeclasses.solve
                                    b2
                                  <:
                                  Bertie.Tls13utils.t_Bytes)
                                hoist79
                              <:
                              Bertie.Tls13utils.t_Bytes)
                            b2
                          <:
                          Bertie.Tls13utils.t_Bytes)
                        hoist81
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok hoist86 ->
              Core.Result.Result_Ok (Bertie.Tls13utils.impl_Bytes__concat b1 hoist86)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_r_len (rlen: usize) =
  if rlen <. mk_usize 32 || rlen >. mk_usize 33
  then
    Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
    <:
    Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl_Bytes__len sig <: usize) <. mk_usize 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    match
      Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 (mk_u8 48) <: Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl_Bytes__slice_range sig
            ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 1 }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      (match
          Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl_Bytes__slice_range sig
                ({
                    Core.Ops.Range.f_start = mk_usize 1;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sig <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
          <:
          Core.Result.t_Result Prims.unit u8
        with
        | Core.Result.Result_Ok _ ->
          (match
              Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 (mk_u8 2)
                  <:
                  Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl_Bytes__slice_range sig
                    ({ Core.Ops.Range.f_start = mk_usize 2; Core.Ops.Range.f_end = mk_usize 3 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              (match
                  Bertie.Tls13utils.length_u8_encoded (sig.[ {
                          Core.Ops.Range.f_start = mk_usize 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len sig <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                  <:
                  Core.Result.t_Result usize u8
                with
                | Core.Result.Result_Ok rlen ->
                  (match check_r_len rlen <: Core.Result.t_Result Prims.unit u8 with
                    | Core.Result.Result_Ok _ ->
                      let r:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl_Bytes__slice sig
                          ((mk_usize 4 +! rlen <: usize) -! mk_usize 32 <: usize)
                          (mk_usize 32)
                      in
                      if
                        (Bertie.Tls13utils.impl_Bytes__len sig <: usize) <.
                        ((mk_usize 6 +! rlen <: usize) +! mk_usize 32 <: usize)
                      then
                        Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      else
                        (match
                            Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 (mk_u8 2)
                                <:
                                Bertie.Tls13utils.t_Bytes)
                              (Bertie.Tls13utils.impl_Bytes__slice_range sig
                                  ({
                                      Core.Ops.Range.f_start = mk_usize 4 +! rlen <: usize;
                                      Core.Ops.Range.f_end = mk_usize 5 +! rlen <: usize
                                    }
                                    <:
                                    Core.Ops.Range.t_Range usize)
                                <:
                                Bertie.Tls13utils.t_Bytes)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            (match
                                Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl_Bytes__slice_range
                                      sig
                                      ({
                                          Core.Ops.Range.f_start = mk_usize 5 +! rlen <: usize;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl_Bytes__len sig <: usize
                                        }
                                        <:
                                        Core.Ops.Range.t_Range usize)
                                    <:
                                    Bertie.Tls13utils.t_Bytes)
                                <:
                                Core.Result.t_Result Prims.unit u8
                              with
                              | Core.Result.Result_Ok _ ->
                                let s:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl_Bytes__slice sig
                                    ((Bertie.Tls13utils.impl_Bytes__len sig <: usize) -! mk_usize 32
                                      <:
                                      usize)
                                    (mk_usize 32)
                                in
                                Core.Result.Result_Ok (Bertie.Tls13utils.impl_Bytes__concat r s)
                                <:
                                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                    | Core.Result.Result_Err err ->
                      Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let certificate_verify (algs: Bertie.Tls13crypto.t_Algorithms) (cv: Bertie.Tls13utils.t_Bytes) =
  match
    (match algs.Bertie.Tls13crypto.f_signature <: Bertie.Tls13crypto.t_SignatureScheme with
      | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
        Core.Result.Result_Ok
        (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve cv)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
        if (Bertie.Tls13utils.impl_Bytes__len cv <: usize) <>. mk_usize 64
        then
          Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        else ecdsa_signature cv
      | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
        Core.Result.Result_Err Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok sv ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist89 ->
        (match
            Bertie.Tls13utils.encode_length_u16 sv
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist88 ->
            let sig:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl_Bytes__concat hoist89 hoist88
            in
            Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
                <:
                Bertie.Tls13formats.Handshake_data.t_HandshakeType)
              sig
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (certificate_verify: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__as_handshake_message certificate_verify
      (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData cv) ->
    let sa:Bertie.Tls13crypto.t_SignatureScheme =
      Bertie.Tls13crypto.impl_Algorithms__signature algs
    in
    (match
        Bertie.Tls13crypto.impl_Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist90 ->
        (match
            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw hoist90
                <:
                t_Slice u8)
              (Bertie.Tls13utils.impl_Bytes__as_raw cv <: t_Slice u8)
              (mk_usize 0)
              (mk_usize 2)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            (match
                Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl_Bytes__slice_range
                      cv
                      ({
                          Core.Ops.Range.f_start = mk_usize 2;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len cv <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8
              with
              | Core.Result.Result_Ok _ ->
                (match sa <: Bertie.Tls13crypto.t_SignatureScheme with
                  | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
                    parse_ecdsa_signature (Bertie.Tls13utils.impl_Bytes__slice_range cv
                          ({
                              Core.Ops.Range.f_start = mk_usize 4;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len cv <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        Bertie.Tls13utils.t_Bytes)
                  | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
                    Core.Result.Result_Ok
                    (Bertie.Tls13utils.impl_Bytes__slice_range cv
                        ({
                            Core.Ops.Range.f_start = mk_usize 4;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len cv <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
                    if
                      ((Bertie.Tls13utils.impl_Bytes__len cv <: usize) -! mk_usize 4 <: usize) =.
                      mk_usize 64
                    then
                      Core.Result.Result_Ok
                      (Bertie.Tls13utils.impl_Bytes__slice_range cv
                          ({
                              Core.Ops.Range.f_start = mk_usize 4;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len cv <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize))
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                    else
                      Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
                      <:
                      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let finished (vd: Bertie.Tls13utils.t_Bytes) =
  Bertie.Tls13formats.Handshake_data.impl_HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    vd

let parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  match
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__as_handshake_message finished
      (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData fin) ->
    Core.Result.Result_Ok fin <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let t_ContentType_cast_to_repr (x: t_ContentType) =
  match x <: t_ContentType with
  | ContentType_Invalid  -> anon_const_ContentType_Invalid__anon_const_0
  | ContentType_ChangeCipherSpec  -> anon_const_ContentType_ChangeCipherSpec__anon_const_0
  | ContentType_Alert  -> anon_const_ContentType_Alert__anon_const_0
  | ContentType_Handshake  -> anon_const_ContentType_Handshake__anon_const_0
  | ContentType_ApplicationData  -> anon_const_ContentType_ApplicationData__anon_const_0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core.Clone.t_Clone t_ContentType

let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_17': Core.Marker.t_Copy t_ContentType

let impl_17 = impl_17'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': Core.Fmt.t_Debug t_ContentType

let impl_18 = impl_18'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': Core.Marker.t_StructuralPartialEq t_ContentType

let impl_19 = impl_19'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20': Core.Cmp.t_PartialEq t_ContentType t_ContentType

let impl_20 = impl_20'

let impl_ContentType__try_from_u8 (t: u8) =
  match t <: u8 with
  | Rust_primitives.Integers.MkInt 20 ->
    Core.Result.Result_Ok (ContentType_ChangeCipherSpec <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | Rust_primitives.Integers.MkInt 21 ->
    Core.Result.Result_Ok (ContentType_Alert <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | Rust_primitives.Integers.MkInt 22 ->
    Core.Result.Result_Ok (ContentType_Handshake <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | Rust_primitives.Integers.MkInt 23 ->
    Core.Result.Result_Ok (ContentType_ApplicationData <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | _ ->
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result t_ContentType u8

let handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  let ty:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (anon_const_ContentType_Handshake__anon_const_0 +! mk_u8 0 <: u8)
        <:
        u8)
  in
  let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
  match
    Bertie.Tls13utils.encode_length_u16 p.Bertie.Tls13formats.Handshake_data._0
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist93 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__concat ty ver
          <:
          Bertie.Tls13utils.t_Bytes)
        hoist93)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let protocol_version_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_PROTOCOL_VERSION_ALERT
  <:
  Core.Result.t_Result Prims.unit u8

let application_data_instead_of_handshake (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE
  <:
  Core.Result.t_Result Prims.unit u8

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl_Bytes__len p <: usize) <. mk_usize 5
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
  else
    let ty:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.bytes1 (cast (anon_const_ContentType_Handshake__anon_const_0 +! mk_u8 0
              <:
              u8)
          <:
          u8)
    in
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
    match
      Bertie.Tls13utils.check_eq ty
        (Bertie.Tls13utils.impl_Bytes__slice_range p
            ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 1 }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let _:Prims.unit = () <: Prims.unit in
      (match
          Bertie.Tls13utils.check_eq ver
            (Bertie.Tls13utils.impl_Bytes__slice_range p
                ({ Core.Ops.Range.f_start = mk_usize 1; Core.Ops.Range.f_end = mk_usize 3 }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Bertie.Tls13utils.t_Bytes)
          <:
          Core.Result.t_Result Prims.unit u8
        with
        | Core.Result.Result_Ok _ ->
          let _:Prims.unit = () <: Prims.unit in
          (match
              Bertie.Tls13utils.length_u16_encoded (p.[ {
                      Core.Ops.Range.f_start = mk_usize 3;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len p <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result usize u8
            with
            | Core.Result.Result_Ok len ->
              Core.Result.Result_Ok
              ((Bertie.Tls13formats.Handshake_data.HandshakeData
                  (Bertie.Tls13utils.impl_Bytes__slice_range p
                      ({
                          Core.Ops.Range.f_start = mk_usize 5;
                          Core.Ops.Range.f_end = mk_usize 5 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize))
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                mk_usize 5 +! len
                <:
                (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
              <:
              Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
        | Core.Result.Result_Err _ ->
          match protocol_version_alert () <: Core.Result.t_Result Prims.unit u8 with
          | Core.Result.Result_Ok ok ->
            let _:Prims.unit = ok in
            (match
                Bertie.Tls13utils.length_u16_encoded (p.[ {
                        Core.Ops.Range.f_start = mk_usize 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len p <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8
              with
              | Core.Result.Result_Ok len ->
                Core.Result.Result_Ok
                ((Bertie.Tls13formats.Handshake_data.HandshakeData
                    (Bertie.Tls13utils.impl_Bytes__slice_range p
                        ({
                            Core.Ops.Range.f_start = mk_usize 5;
                            Core.Ops.Range.f_end = mk_usize 5 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                  mk_usize 5 +! len
                  <:
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
            )
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
    | Core.Result.Result_Err _ ->
      match application_data_instead_of_handshake () <: Core.Result.t_Result Prims.unit u8 with
      | Core.Result.Result_Ok ok ->
        let _:Prims.unit = ok in
        (match
            Bertie.Tls13utils.check_eq ver
              (Bertie.Tls13utils.impl_Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = mk_usize 1; Core.Ops.Range.f_end = mk_usize 3 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let _:Prims.unit = () <: Prims.unit in
            (match
                Bertie.Tls13utils.length_u16_encoded (p.[ {
                        Core.Ops.Range.f_start = mk_usize 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len p <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8
              with
              | Core.Result.Result_Ok len ->
                Core.Result.Result_Ok
                ((Bertie.Tls13formats.Handshake_data.HandshakeData
                    (Bertie.Tls13utils.impl_Bytes__slice_range p
                        ({
                            Core.Ops.Range.f_start = mk_usize 5;
                            Core.Ops.Range.f_end = mk_usize 5 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                  mk_usize 5 +! len
                  <:
                  (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
            )
          | Core.Result.Result_Err _ ->
            match protocol_version_alert () <: Core.Result.t_Result Prims.unit u8 with
            | Core.Result.Result_Ok ok ->
              let _:Prims.unit = ok in
              (match
                  Bertie.Tls13utils.length_u16_encoded (p.[ {
                          Core.Ops.Range.f_start = mk_usize 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len p <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                  <:
                  Core.Result.t_Result usize u8
                with
                | Core.Result.Result_Ok len ->
                  Core.Result.Result_Ok
                  ((Bertie.Tls13formats.Handshake_data.HandshakeData
                      (Bertie.Tls13utils.impl_Bytes__slice_range p
                          ({
                              Core.Ops.Range.f_start = mk_usize 5;
                              Core.Ops.Range.f_end = mk_usize 5 +! len <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize))
                      <:
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                    mk_usize 5 +! len
                    <:
                    (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize))
                  <:
                  Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8
                | Core.Result.Result_Err err ->
                  Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize)
                    u8)
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8

let get_handshake_record (p: Bertie.Tls13utils.t_Bytes) =
  match
    check_handshake_record p
    <:
    Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
  with
  | Core.Result.Result_Ok (hd, len) ->
    if len =. (Bertie.Tls13utils.impl_Bytes__len p <: usize)
    then
      Core.Result.Result_Ok hd
      <:
      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
    else
      Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
      <:
      Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8

let impl_Transcript__new (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm) =
  {
    f_hash_algorithm = hash_algorithm;
    f_transcript
    =
    Bertie.Tls13formats.Handshake_data.HandshakeData (Bertie.Tls13utils.impl_Bytes__new ())
    <:
    Bertie.Tls13formats.Handshake_data.t_HandshakeData
  }
  <:
  t_Transcript

let impl_Transcript__add
      (self: t_Transcript)
      (msg: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  let self:t_Transcript =
    {
      self with
      f_transcript
      =
      Bertie.Tls13formats.Handshake_data.impl_HandshakeData__concat self.f_transcript msg
    }
    <:
    t_Transcript
  in
  self

let impl_Transcript__transcript_hash (self: t_Transcript) =
  match
    Bertie.Tls13crypto.impl_HashAlgorithm__hash self.f_hash_algorithm
      self.f_transcript.Bertie.Tls13formats.Handshake_data._0
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th ->
    Core.Result.Result_Ok th <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let impl_Transcript__transcript_hash_without_client_hello
      (self: t_Transcript)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
     =
  let Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    client_hello
  in
  Bertie.Tls13crypto.impl_HashAlgorithm__hash self.f_hash_algorithm
    (Bertie.Tls13utils.impl_Bytes__concat (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
            #FStar.Tactics.Typeclasses.solve
            self.f_transcript.Bertie.Tls13formats.Handshake_data._0
          <:
          Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl_Bytes__slice_range client_hello
              .Bertie.Tls13formats.Handshake_data._0
            ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = trunc_len }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Bertie.Tls13utils.t_Bytes)

let rec find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice u8) =
  if (Core.Slice.impl__len #u8 ch <: usize) <. mk_usize 4
  then Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes (Bertie.Tls13utils.parse_failed () <: u8)
  else
    if
      Bertie.Tls13utils.eq_slice (Bertie.Tls13utils.impl_Bytes__as_raw g <: t_Slice u8)
        (ch.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 2 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
    then
      match
        Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok len ->
        Core.Result.Result_Ok
        (Core.Convert.f_into #(t_Slice u8)
            #Bertie.Tls13utils.t_Bytes
            #FStar.Tactics.Typeclasses.solve
            (ch.[ {
                  Core.Ops.Range.f_start = mk_usize 4;
                  Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    else
      match
        Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok len ->
        find_key_share g
          (ch.[ {
                Core.Ops.Range.f_start = mk_usize 4 +! len <: usize;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let rec check_server_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  match
    check_server_extension algs b
    <:
    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (len, out) ->
    if len =. (Core.Slice.impl__len #u8 b <: usize)
    then
      Core.Result.Result_Ok out
      <:
      Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
    else
      (match
          check_server_extensions algs
            (b.[ {
                  Core.Ops.Range.f_start = len;
                  Core.Ops.Range.f_end = Core.Slice.impl__len #u8 b <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
        with
        | Core.Result.Result_Ok out_rest -> merge_opts #Bertie.Tls13utils.t_Bytes out out_rest
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl_Algorithms__supported_group algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist43 ->
        find_key_share hoist43
          (ch.[ {
                Core.Ops.Range.f_start = mk_usize 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_extension (algs: Bertie.Tls13crypto.t_Algorithms) (bytes: t_Slice u8) =
  if (Core.Slice.impl__len #u8 bytes <: usize) <. mk_usize 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (usize & t_Extensions) u8
  else
    let l0:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 0 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    let l1:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ mk_usize 1 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    match
      Bertie.Tls13utils.length_u16_encoded_slice (bytes.[ {
              Core.Ops.Range.f_start = mk_usize 2;
              Core.Ops.Range.f_end = Core.Slice.impl__len #u8 bytes <: usize
            }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result usize u8
    with
    | Core.Result.Result_Ok len ->
      let out:t_Extensions =
        {
          f_sni = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_key_share = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_ticket = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
          f_binder = Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
        }
        <:
        t_Extensions
      in
      (match (cast (l0 <: usize) <: u8), (cast (l1 <: usize) <: u8) <: (u8 & u8) with
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 0 ->
          (match
              check_server_name (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok hoist64 ->
              Core.Result.Result_Ok
              (mk_usize 4 +! len,
                ({
                    f_sni
                    =
                    Core.Option.Option_Some hoist64
                    <:
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_key_share
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_ticket
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_binder
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
                  }
                  <:
                  t_Extensions)
                <:
                (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 45 ->
          (match
              check_psk_key_exchange_modes (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 43 ->
          (match
              check_supported_versions (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 10 ->
          (match
              check_supported_groups algs
                (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 13 ->
          (match
              check_signature_algorithms algs
                (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 51 ->
          (match
              check_key_shares algs
                (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok gx ->
              Core.Result.Result_Ok
              (mk_usize 4 +! len,
                ({
                    f_sni
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_key_share
                    =
                    Core.Option.Option_Some gx <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_ticket
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes;
                    f_binder
                    =
                    Core.Option.Option_None <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes
                  }
                  <:
                  t_Extensions)
                <:
                (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err _ ->
              Bertie.Tls13utils.tlserr #(usize & t_Extensions) Bertie.Tls13utils.v_MISSING_KEY_SHARE
          )
        | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 41 ->
          (match
              check_psk_shared_key algs
                (bytes.[ {
                      Core.Ops.Range.f_start = mk_usize 4;
                      Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | _ ->
          Core.Result.Result_Ok (mk_usize 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8

let parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__as_handshake_message server_hello
      (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData server_hello) ->
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
    (match
        Bertie.Tls13crypto.impl_Algorithms__ciphersuite algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok cip ->
        let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 (mk_u8 0) in
        let next:usize = mk_usize 0 in
        (match
            (match
                Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw ver
                    <:
                    t_Slice u8)
                  (Bertie.Tls13utils.impl_Bytes__as_raw server_hello <: t_Slice u8)
                  next
                  (next +! mk_usize 2 <: usize)
                <:
                Core.Result.t_Result Prims.unit u8
              with
              | Core.Result.Result_Ok _ ->
                Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
              | Core.Result.Result_Err _ -> protocol_version_alert ())
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let next:usize = next +! mk_usize 2 in
            (match
                Bertie.Tls13utils.check ((Bertie.Tls13utils.impl_Bytes__len server_hello <: usize) >=.
                    (next +! mk_usize 32 <: usize)
                    <:
                    bool)
                <:
                Core.Result.t_Result Prims.unit u8
              with
              | Core.Result.Result_Ok _ ->
                let srand:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl_Bytes__slice_range server_hello
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = next +! mk_usize 32 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                in
                let next:usize = next +! mk_usize 32 in
                (match
                    Bertie.Tls13utils.length_u8_encoded (server_hello.[ {
                            Core.Ops.Range.f_start = next;
                            Core.Ops.Range.f_end
                            =
                            Bertie.Tls13utils.impl_Bytes__len server_hello <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result usize u8
                  with
                  | Core.Result.Result_Ok sidlen ->
                    let next:usize = (next +! mk_usize 1 <: usize) +! sidlen in
                    (match
                        (match
                            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw
                                  cip
                                <:
                                t_Slice u8)
                              (Bertie.Tls13utils.impl_Bytes__as_raw server_hello <: t_Slice u8)
                              next
                              (next +! mk_usize 2 <: usize)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            Core.Result.Result_Ok (() <: Prims.unit)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          | Core.Result.Result_Err _ -> unsupported_cipher_alert ())
                        <:
                        Core.Result.t_Result Prims.unit u8
                      with
                      | Core.Result.Result_Ok _ ->
                        let next:usize = next +! mk_usize 2 in
                        (match
                            (match
                                Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw
                                      comp
                                    <:
                                    t_Slice u8)
                                  (Bertie.Tls13utils.impl_Bytes__as_raw server_hello <: t_Slice u8)
                                  next
                                  (next +! mk_usize 1 <: usize)
                                <:
                                Core.Result.t_Result Prims.unit u8
                              with
                              | Core.Result.Result_Ok _ ->
                                Core.Result.Result_Ok (() <: Prims.unit)
                                <:
                                Core.Result.t_Result Prims.unit u8
                              | Core.Result.Result_Err _ -> invalid_compression_method_alert ())
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            let next:usize = next +! mk_usize 1 in
                            (match
                                Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl_Bytes__slice_range
                                      server_hello
                                      ({
                                          Core.Ops.Range.f_start = next;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl_Bytes__len server_hello <: usize
                                        }
                                        <:
                                        Core.Ops.Range.t_Range usize)
                                    <:
                                    Bertie.Tls13utils.t_Bytes)
                                <:
                                Core.Result.t_Result Prims.unit u8
                              with
                              | Core.Result.Result_Ok _ ->
                                let next:usize = next +! mk_usize 2 in
                                (match
                                    check_server_extensions algs
                                      (server_hello.[ {
                                            Core.Ops.Range.f_start = next;
                                            Core.Ops.Range.f_end
                                            =
                                            Bertie.Tls13utils.impl_Bytes__len server_hello <: usize
                                          }
                                          <:
                                          Core.Ops.Range.t_Range usize ]
                                        <:
                                        t_Slice u8)
                                    <:
                                    Core.Result.t_Result
                                      (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
                                  with
                                  | Core.Result.Result_Ok gy ->
                                    (match gy <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes with
                                      | Core.Option.Option_Some gy ->
                                        Core.Result.Result_Ok
                                        (srand, gy
                                          <:
                                          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes))
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
                                      | _ ->
                                        Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8
                                    )
                                  | Core.Result.Result_Err err ->
                                    Core.Result.Result_Err err
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes)
                          u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8

let rec check_extensions_slice (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  match check_extension algs b <: Core.Result.t_Result (usize & t_Extensions) u8 with
  | Core.Result.Result_Ok (len, out) ->
    if len =. (Core.Slice.impl__len #u8 b <: usize)
    then Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8
    else
      (match
          check_extensions_slice algs
            (b.[ {
                  Core.Ops.Range.f_start = len;
                  Core.Ops.Range.f_end = Core.Slice.impl__len #u8 b <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result t_Extensions u8
        with
        | Core.Result.Result_Ok out_rest -> impl_Extensions__merge out out_rest
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes) =
  match
    check_extension algs (Bertie.Tls13utils.impl_Bytes__as_raw b <: t_Slice u8)
    <:
    Core.Result.t_Result (usize & t_Extensions) u8
  with
  | Core.Result.Result_Ok (len, out) ->
    if len =. (Bertie.Tls13utils.impl_Bytes__len b <: usize)
    then Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8
    else
      (match
          check_extensions_slice algs
            (Bertie.Tls13utils.impl_Bytes__raw_slice b
                ({
                    Core.Ops.Range.f_start = len;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len b <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result t_Extensions u8
        with
        | Core.Result.Result_Ok out_rest -> impl_Extensions__merge out out_rest
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8

let parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__as_handshake_message client_hello
      (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData ch) ->
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 3) (mk_u8 3) in
    let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 (mk_u8 1) (mk_u8 0) in
    let next:usize = mk_usize 0 in
    (match
        Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw ver
            <:
            t_Slice u8)
          (Bertie.Tls13utils.impl_Bytes__as_raw ch <: t_Slice u8)
          next
          (next +! mk_usize 2 <: usize)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        let next:usize = next +! mk_usize 2 in
        (match
            Bertie.Tls13utils.check ((Bertie.Tls13utils.impl_Bytes__len ch <: usize) >=.
                (next +! mk_usize 32 <: usize)
                <:
                bool)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let crand:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl_Bytes__slice_range ch
                ({
                    Core.Ops.Range.f_start = next;
                    Core.Ops.Range.f_end = next +! mk_usize 32 <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
            in
            let next:usize = next +! mk_usize 32 in
            (match
                Bertie.Tls13utils.length_u8_encoded (ch.[ {
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len ch <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8
              with
              | Core.Result.Result_Ok sidlen ->
                let sid:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl_Bytes__slice_range ch
                    ({
                        Core.Ops.Range.f_start = next +! mk_usize 1 <: usize;
                        Core.Ops.Range.f_end = (next +! mk_usize 1 <: usize) +! sidlen <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                in
                let next:usize = (next +! mk_usize 1 <: usize) +! sidlen in
                (match
                    Bertie.Tls13crypto.impl_Algorithms__check ciphersuite
                      (Bertie.Tls13utils.impl_Bytes__raw_slice ch
                          ({
                              Core.Ops.Range.f_start = next;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len ch <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result usize u8
                  with
                  | Core.Result.Result_Ok cslen ->
                    let next:usize = next +! cslen in
                    (match
                        (match
                            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl_Bytes__as_raw
                                  comp
                                <:
                                t_Slice u8)
                              (Bertie.Tls13utils.impl_Bytes__as_raw ch <: t_Slice u8)
                              next
                              (next +! mk_usize 2 <: usize)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            Core.Result.Result_Ok (() <: Prims.unit)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          | Core.Result.Result_Err _ -> invalid_compression_list ())
                        <:
                        Core.Result.t_Result Prims.unit u8
                      with
                      | Core.Result.Result_Ok _ ->
                        let next:usize = next +! mk_usize 2 in
                        (match
                            Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl_Bytes__slice_range
                                  ch
                                  ({
                                      Core.Ops.Range.f_start = next;
                                      Core.Ops.Range.f_end
                                      =
                                      Bertie.Tls13utils.impl_Bytes__len ch <: usize
                                    }
                                    <:
                                    Core.Ops.Range.t_Range usize)
                                <:
                                Bertie.Tls13utils.t_Bytes)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            let next:usize = next +! mk_usize 2 in
                            (match
                                check_extensions ciphersuite
                                  (Bertie.Tls13utils.impl_Bytes__slice_range ch
                                      ({
                                          Core.Ops.Range.f_start = next;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl_Bytes__len ch <: usize
                                        }
                                        <:
                                        Core.Ops.Range.t_Range usize)
                                    <:
                                    Bertie.Tls13utils.t_Bytes)
                                <:
                                Core.Result.t_Result t_Extensions u8
                              with
                              | Core.Result.Result_Ok exts ->
                                let trunc_len:usize =
                                  ((Bertie.Tls13utils.impl_Bytes__len ch <: usize) -!
                                    (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len (Bertie.Tls13crypto.impl_Algorithms__hash
                                            ciphersuite
                                          <:
                                          Bertie.Tls13crypto.t_HashAlgorithm)
                                      <:
                                      usize)
                                    <:
                                    usize) -!
                                  mk_usize 3
                                in
                                (match
                                    Bertie.Tls13crypto.impl_Algorithms__psk_mode ciphersuite, exts
                                    <:
                                    (bool & t_Extensions)
                                  with
                                  | _,
                                  { f_sni = _ ;
                                    f_key_share = Core.Option.Option_None  ;
                                    f_ticket = _ ;
                                    f_binder = _ } ->
                                    Core.Result.Result_Err Bertie.Tls13utils.v_MISSING_KEY_SHARE
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8
                                  | true,
                                  { f_sni = Core.Option.Option_Some sn ;
                                    f_key_share = Core.Option.Option_Some gx ;
                                    f_ticket = Core.Option.Option_Some tkt ;
                                    f_binder = Core.Option.Option_Some binder } ->
                                    Core.Result.Result_Ok
                                    (crand,
                                      sid,
                                      sn,
                                      gx,
                                      (Core.Option.Option_Some tkt
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      (Core.Option.Option_Some binder
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      trunc_len
                                      <:
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize))
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8
                                  | true,
                                  { f_sni = Core.Option.Option_None  ;
                                    f_key_share = Core.Option.Option_Some gx ;
                                    f_ticket = Core.Option.Option_Some tkt ;
                                    f_binder = Core.Option.Option_Some binder } ->
                                    Core.Result.Result_Ok
                                    (crand,
                                      sid,
                                      Bertie.Tls13utils.impl_Bytes__new (),
                                      gx,
                                      (Core.Option.Option_Some tkt
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      (Core.Option.Option_Some binder
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      trunc_len
                                      <:
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize))
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8
                                  | false,
                                  { f_sni = Core.Option.Option_Some sn ;
                                    f_key_share = Core.Option.Option_Some gx ;
                                    f_ticket = Core.Option.Option_None  ;
                                    f_binder = Core.Option.Option_None  } ->
                                    Core.Result.Result_Ok
                                    (crand,
                                      sid,
                                      sn,
                                      gx,
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      mk_usize 0
                                      <:
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize))
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8
                                  | false,
                                  { f_sni = Core.Option.Option_None  ;
                                    f_key_share = Core.Option.Option_Some gx ;
                                    f_ticket = Core.Option.Option_None  ;
                                    f_binder = Core.Option.Option_None  } ->
                                    Core.Result.Result_Ok
                                    (crand,
                                      sid,
                                      Bertie.Tls13utils.impl_Bytes__new (),
                                      gx,
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      mk_usize 0
                                      <:
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize))
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8
                                  | _ ->
                                    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
                                    <:
                                    Core.Result.t_Result
                                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                        usize) u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                    Bertie.Tls13utils.t_Bytes &
                                    Bertie.Tls13utils.t_Bytes &
                                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                    usize) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                                Bertie.Tls13utils.t_Bytes &
                                Bertie.Tls13utils.t_Bytes &
                                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                                usize) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                            Bertie.Tls13utils.t_Bytes &
                            Bertie.Tls13utils.t_Bytes &
                            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                            usize) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result
                      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                        Bertie.Tls13utils.t_Bytes &
                        Bertie.Tls13utils.t_Bytes &
                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                        usize) u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                    Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                    usize) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
                Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
                usize) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result
          (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
            Bertie.Tls13utils.t_Bytes &
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
            usize) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes &
        Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        Core.Option.t_Option Bertie.Tls13utils.t_Bytes &
        usize) u8
