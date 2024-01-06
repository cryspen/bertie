module Bertie.Tls13record
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let derive_iv_ctr (iv: Bertie.Tls13utils.t_Bytes) (n: u64) : Bertie.Tls13utils.t_Bytes =
  let (counter: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
    Core.Convert.f_into (Core.Num.impl__u64__to_be_bytes n <: t_Array u8 (sz 8))
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl__Bytes__zeroes (Bertie.Tls13utils.impl__Bytes__len iv <: usize)
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              (Bertie.Tls13utils.impl__Bytes__len iv <: usize) -! sz 8 <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      iv_ctr
      (fun iv_ctr i ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize iv_ctr
            i
            (iv.[ i ] <: Bertie.Tls13utils.t_U8)
          <:
          Bertie.Tls13utils.t_Bytes)
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 8
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      iv_ctr
      (fun iv_ctr i ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize iv_ctr
            ((i +! (Bertie.Tls13utils.impl__Bytes__len iv <: usize) <: usize) -! sz 8 <: usize)
            ((iv.[ (i +! (Bertie.Tls13utils.impl__Bytes__len iv <: usize) <: usize) -! sz 8 <: usize
                ]
                <:
                Bertie.Tls13utils.t_U8) ^.
              (counter.[ i ] <: Bertie.Tls13utils.t_U8)
              <:
              Bertie.Tls13utils.t_U8)
          <:
          Bertie.Tls13utils.t_Bytes)
  in
  iv_ctr

let padlen (b: Bertie.Tls13utils.t_Bytes) (n: usize) : usize =
  if
    n >. sz 0 &&
    (Bertie.Tls13utils.impl__U8__declassify (b.[ n -! sz 1 <: usize ] <: Bertie.Tls13utils.t_U8)
      <:
      u8) =.
    0uy
  then sz 1 +! (padlen b (n -! sz 1 <: usize) <: usize)
  else sz 0

let decrypt_record_payload
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ciphertext: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let iv_ctr:Bertie.Tls13utils.t_Bytes =
        derive_iv_ctr kiv.Bertie.Tls13crypto.f_iv n
      in
      let clen:usize = (Bertie.Tls13utils.impl__Bytes__len ciphertext <: usize) -! sz 5 in
      if clen <=. sz 65536 && clen >. sz 16
      then
        let clen_bytes:t_Array u8 (sz 2) =
          Core.Num.impl__u16__to_be_bytes (cast (clen <: usize) <: u16)
        in
        let ad:Bertie.Tls13utils.t_Bytes =
          Core.Convert.f_into (let list =
                [23uy; 3uy; 3uy; clen_bytes.[ sz 0 ] <: u8; clen_bytes.[ sz 1 ] <: u8]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
              Rust_primitives.Hax.array_of_list list)
        in
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq ad
                  (Bertie.Tls13utils.impl__Bytes__slice_range ciphertext
                      ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist461:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist461)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Prims.unit
        in
        let cip:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__slice_range ciphertext
            ({
                Core.Ops.Range.f_start = sz 5;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ciphertext <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
        in
        let* plain:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.aead_decrypt kiv
                    .Bertie.Tls13crypto.f_key
                  iv_ctr
                  cip
                  ad
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist462:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist462)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Bertie.Tls13utils.t_Bytes
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Bertie.Tls13utils.t_Bytes
        in
        let payload_len:usize =
          ((Bertie.Tls13utils.impl__Bytes__len plain <: usize) -!
            (padlen plain (Bertie.Tls13utils.impl__Bytes__len plain <: usize) <: usize)
            <:
            usize) -!
          sz 1
        in
        let* ct:Bertie.Tls13formats.t_ContentType =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13formats.impl__ContentType__try_from_u8 (Bertie.Tls13utils.impl__U8__declassify
                      (plain.[ payload_len ] <: Bertie.Tls13utils.t_U8)
                    <:
                    u8)
                <:
                Core.Result.t_Result Bertie.Tls13formats.t_ContentType u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist463:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result
                    (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist463)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Bertie.Tls13formats.t_ContentType
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                  u8) Bertie.Tls13formats.t_ContentType
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let payload:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range plain
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = payload_len }
                <:
                Core.Ops.Range.t_Range usize)
          in
          Core.Result.Result_Ok
          (ct, payload <: (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
          (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
          <:
          Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
          (Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8))

let encrypt_record_payload
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ct: Bertie.Tls13formats.t_ContentType)
      (payload: Bertie.Tls13utils.t_Bytes)
      (pad: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let iv_ctr:Bertie.Tls13utils.t_Bytes =
        derive_iv_ctr key_iv.Bertie.Tls13crypto.f_iv n
      in
      let inner_plaintext:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat payload
              (Bertie.Tls13utils.bytes1 (Bertie.Tls13formats.impl__ContentType__as_u8 ct <: u8)
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Bertie.Tls13utils.t_Bytes)
          (Bertie.Tls13utils.impl__Bytes__zeroes pad <: Bertie.Tls13utils.t_Bytes)
      in
      let clen:usize = (Bertie.Tls13utils.impl__Bytes__len inner_plaintext <: usize) +! sz 16 in
      if clen <=. sz 65536
      then
        let clenb:t_Array u8 (sz 2) =
          Core.Num.impl__u16__to_be_bytes (cast (clen <: usize) <: u16)
        in
        let ad:Bertie.Tls13utils.t_Bytes =
          Core.Convert.f_into (let list =
                [23uy; 3uy; 3uy; clenb.[ sz 0 ] <: u8; clenb.[ sz 1 ] <: u8]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
              Rust_primitives.Hax.array_of_list list)
        in
        let* cip:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13crypto.aead_encrypt key_iv
                    .Bertie.Tls13crypto.f_key
                  iv_ctr
                  inner_plaintext
                  ad
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist464:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist464)
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
        (let v_rec:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ad cip in
          Core.Result.Result_Ok v_rec <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      else
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8))

type t_ClientCipherState0 =
  | ClientCipherState0 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13utils.t_Bytes
    -> t_ClientCipherState0

type t_DuplexCipherState1 =
  | DuplexCipherState1 :
      Bertie.Tls13crypto.t_AeadAlgorithm ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13crypto.t_AeadKeyIV ->
      u64 ->
      Bertie.Tls13utils.t_Bytes
    -> t_DuplexCipherState1

type t_DuplexCipherStateH = {
  f_sender_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_sender_counter:u64;
  f_receiver_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_receiver_counter:u64
}

let impl__DuplexCipherStateH__new
      (sender_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (sender_counter: u64)
      (receiver_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (receiver_counter: u64)
    : t_DuplexCipherStateH =
  {
    f_sender_key_iv = sender_key_iv;
    f_sender_counter = sender_counter;
    f_receiver_key_iv = receiver_key_iv;
    f_receiver_counter = receiver_counter
  }
  <:
  t_DuplexCipherStateH

type t_ServerCipherState0 = {
  f_key_iv:Bertie.Tls13crypto.t_AeadKeyIV;
  f_counter:u64;
  f_early_exporter_ms:Bertie.Tls13utils.t_Bytes
}

let client_cipher_state0
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (c: u64)
      (k: Bertie.Tls13utils.t_Bytes)
    : t_ClientCipherState0 = ClientCipherState0 ae kiv c k <: t_ClientCipherState0

let decrypt_data (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1
      =
        st
      in
      let* ct, payload:(Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (decrypt_record_payload kiv n ciphertext
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist521:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist521)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check (ct =.
                  (Bertie.Tls13formats.ContentType_ApplicationData
                    <:
                    Bertie.Tls13formats.t_ContentType)
                  <:
                  bool)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist522:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist522)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__AppData__new payload,
          (DuplexCipherState1 ae x y kiv (n +! 1uL) exp <: t_DuplexCipherState1)
          <:
          (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8))

let decrypt_data_or_hs (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1)
    : Core.Result.t_Result
      (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1
      =
        st
      in
      let* ct, payload:(Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (decrypt_record_payload kiv n ciphertext
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist524:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes &
                    t_DuplexCipherState1) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist524)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes &
                  t_DuplexCipherState1) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes &
                  t_DuplexCipherState1) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (ct, payload, (DuplexCipherState1 ae x y kiv (n +! 1uL) exp <: t_DuplexCipherState1)
          <:
          (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1))
        <:
        Core.Result.t_Result
          (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1)
            u8)
        (Core.Result.t_Result
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1)
            u8))

let decrypt_handshake (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_DuplexCipherStateH)
    : Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* ct, payload:(Bertie.Tls13formats.t_ContentType &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (decrypt_record_payload state.f_receiver_key_iv
                state.f_receiver_counter
                ciphertext
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist526:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist526)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
      in
      if ct =. (Bertie.Tls13formats.ContentType_Alert <: Bertie.Tls13formats.t_ContentType)
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err Bertie.Tls13utils.v_GOT_HANDSHAKE_FAILURE_ALERT
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
      else
        let* _:Prims.unit =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check (ct =.
                    (Bertie.Tls13formats.ContentType_Handshake <: Bertie.Tls13formats.t_ContentType)
                    <:
                    bool)
                <:
                Core.Result.t_Result Prims.unit u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist527:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8
                )
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist527)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
              Prims.unit
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
              Prims.unit
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let state:t_DuplexCipherStateH =
            { state with f_receiver_counter = state.f_receiver_counter +! 1uL }
            <:
            t_DuplexCipherStateH
          in
          Core.Result.Result_Ok
          (Core.Convert.f_from payload, state
            <:
            (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH))
          <:
          Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8)
          (Core.Result.t_Result (Bertie.Tls13utils.t_HandshakeData & t_DuplexCipherStateH) u8))

let decrypt_zerortt (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_ServerCipherState0)
    : Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* ct, payload:(Bertie.Tls13formats.t_ContentType &
        Bertie.Tls13utils.t_Bytes) =
        match
          Core.Ops.Try_trait.f_branch (decrypt_record_payload state.f_key_iv
                state.f_counter
                ciphertext
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist530:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist530)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
            (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check (ct =.
                  (Bertie.Tls13formats.ContentType_ApplicationData
                    <:
                    Bertie.Tls13formats.t_ContentType)
                  <:
                  bool)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist531:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist531)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
            Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
            Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__AppData__new payload,
          ({
              f_key_iv = state.f_key_iv;
              f_counter = state.f_counter +! 1uL;
              f_early_exporter_ms = state.f_early_exporter_ms
            }
            <:
            t_ServerCipherState0)
          <:
          (Bertie.Tls13utils.t_AppData & t_ServerCipherState0))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8))

let duplex_cipher_state1
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv1: Bertie.Tls13crypto.t_AeadKeyIV)
      (c1: u64)
      (kiv2: Bertie.Tls13crypto.t_AeadKeyIV)
      (c2: u64)
      (k: Bertie.Tls13utils.t_Bytes)
    : t_DuplexCipherState1 = DuplexCipherState1 ae kiv1 c1 kiv2 c2 k <: t_DuplexCipherState1

let encrypt_data (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_DuplexCipherState1)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let DuplexCipherState1 ae kiv n x y exp:t_DuplexCipherState1
      =
        st
      in
      let* v_rec:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (encrypt_record_payload kiv
                n
                (Bertie.Tls13formats.ContentType_ApplicationData
                  <:
                  Bertie.Tls13formats.t_ContentType)
                (Bertie.Tls13utils.impl__AppData__as_raw payload <: Bertie.Tls13utils.t_Bytes)
                pad
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist550:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist550)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (v_rec, (DuplexCipherState1 ae kiv (n +! 1uL) x y exp <: t_DuplexCipherState1)
          <:
          (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8))

let encrypt_handshake
      (payload: Bertie.Tls13utils.t_HandshakeData)
      (pad: usize)
      (state: t_DuplexCipherStateH)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let payload:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__HandshakeData__to_bytes payload
      in
      let* v_rec:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (encrypt_record_payload state.f_sender_key_iv
                state.f_sender_counter
                (Bertie.Tls13formats.ContentType_Handshake <: Bertie.Tls13formats.t_ContentType)
                payload
                pad
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist553:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist553)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let state:t_DuplexCipherStateH =
          { state with f_sender_counter = state.f_sender_counter +! 1uL } <: t_DuplexCipherStateH
        in
        Core.Result.Result_Ok (v_rec, state <: (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8))

let encrypt_zerortt (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_ClientCipherState0)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let ClientCipherState0 ae kiv n exp:t_ClientCipherState0
      =
        st
      in
      let* v_rec:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (encrypt_record_payload kiv
                n
                (Bertie.Tls13formats.ContentType_ApplicationData
                  <:
                  Bertie.Tls13formats.t_ContentType)
                (Bertie.Tls13utils.impl__AppData__as_raw payload <: Bertie.Tls13utils.t_Bytes)
                pad
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist559:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist559)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result_Ok
        (v_rec, (ClientCipherState0 ae kiv (n +! 1uL) exp <: t_ClientCipherState0)
          <:
          (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8)
        (Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8))

let server_cipher_state0
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (counter: u64)
      (early_exporter_ms: Bertie.Tls13utils.t_Bytes)
    : t_ServerCipherState0 =
  { f_key_iv = key_iv; f_counter = counter; f_early_exporter_ms = early_exporter_ms }
  <:
  t_ServerCipherState0
