module Bertie.Tls13record
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13formats in
  let open Bertie.Tls13formats.Handshake_data in
  let open Bertie.Tls13utils in
  ()

let client_cipher_state0
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (c: u64)
      (k: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
     = ClientCipherState0 ae kiv c k <: t_ClientCipherState0

let server_cipher_state0
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (counter: u64)
      (early_exporter_ms: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
     =
  { f_key_iv = key_iv; f_counter = counter; f_early_exporter_ms = early_exporter_ms }
  <:
  t_ServerCipherState0

let impl_DuplexCipherStateH__new
      (sender_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (sender_counter: u64)
      (receiver_key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (receiver_counter: u64)
     =
  {
    f_sender_key_iv = sender_key_iv;
    f_sender_counter = sender_counter;
    f_receiver_key_iv = receiver_key_iv;
    f_receiver_counter = receiver_counter
  }
  <:
  t_DuplexCipherStateH

let duplex_cipher_state1
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv1: Bertie.Tls13crypto.t_AeadKeyIV)
      (c1: u64)
      (kiv2: Bertie.Tls13crypto.t_AeadKeyIV)
      (c2: u64)
      (k: Bertie.Tls13keyscheduler.Key_schedule.t_TagKey)
     = DuplexCipherState1 ae kiv1 c1 kiv2 c2 k <: t_DuplexCipherState1

let derive_iv_ctr (iv: Bertie.Tls13utils.t_Bytes) (n: u64) =
  let (counter: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
    Core.Convert.f_into #(t_Array u8 (mk_usize 8))
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Core.Num.impl_u64__to_be_bytes n <: t_Array u8 (mk_usize 8))
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl_Bytes__zeroes (Bertie.Tls13utils.impl_Bytes__len iv <: usize)
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      ((Bertie.Tls13utils.impl_Bytes__len iv <: usize) -! mk_usize 8 <: usize)
      (fun iv_ctr temp_1_ ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let _:usize = temp_1_ in
          true)
      iv_ctr
      (fun iv_ctr i ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let i:usize = i in
          Rust_primitives.Hax.update_at iv_ctr i (iv.[ i ] <: u8) <: Bertie.Tls13utils.t_Bytes)
  in
  let iv_ctr:Bertie.Tls13utils.t_Bytes =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 8)
      (fun iv_ctr temp_1_ ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let _:usize = temp_1_ in
          true)
      iv_ctr
      (fun iv_ctr i ->
          let iv_ctr:Bertie.Tls13utils.t_Bytes = iv_ctr in
          let i:usize = i in
          Rust_primitives.Hax.update_at iv_ctr
            ((i +! (Bertie.Tls13utils.impl_Bytes__len iv <: usize) <: usize) -! mk_usize 8 <: usize)
            ((iv.[ (i +! (Bertie.Tls13utils.impl_Bytes__len iv <: usize) <: usize) -! mk_usize 8
                  <:
                  usize ]
                <:
                u8) ^.
              (counter.[ i ] <: u8)
              <:
              u8)
          <:
          Bertie.Tls13utils.t_Bytes)
  in
  iv_ctr

let encrypt_record_payload
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ct: Bertie.Tls13formats.t_ContentType)
      (payload: Bertie.Tls13utils.t_Bytes)
      (pad: usize)
     =
  let iv_ctr:Bertie.Tls13utils.t_Bytes = derive_iv_ctr key_iv.Bertie.Tls13crypto.f_iv n in
  let inner_plaintext:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__concat payload
          (Bertie.Tls13utils.bytes1 (Bertie.Tls13formats.t_ContentType_cast_to_repr ct <: u8)
            <:
            Bertie.Tls13utils.t_Bytes)
        <:
        Bertie.Tls13utils.t_Bytes)
      (Bertie.Tls13utils.impl_Bytes__zeroes pad <: Bertie.Tls13utils.t_Bytes)
  in
  let clen:usize = (Bertie.Tls13utils.impl_Bytes__len inner_plaintext <: usize) +! mk_usize 16 in
  if clen <=. mk_usize 65536
  then
    let clenb:t_Array u8 (mk_usize 2) =
      Core.Num.impl_u16__to_be_bytes (cast (clen <: usize) <: u16)
    in
    let ad:Bertie.Tls13utils.t_Bytes =
      Core.Convert.f_into #(t_Array u8 (mk_usize 5))
        #Bertie.Tls13utils.t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (let list =
            [mk_u8 23; mk_u8 3; mk_u8 3; clenb.[ mk_usize 0 ] <: u8; clenb.[ mk_usize 1 ] <: u8]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
          Rust_primitives.Hax.array_of_list 5 list)
    in
    match
      Bertie.Tls13crypto.aead_encrypt key_iv.Bertie.Tls13crypto.f_key iv_ctr inner_plaintext ad
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    with
    | Core.Result.Result_Ok cip ->
      let v_rec:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl_Bytes__concat ad cip in
      Core.Result.Result_Ok v_rec <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let encrypt_zerortt (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_ClientCipherState0) =
  let ClientCipherState0 ae kiv n exp:t_ClientCipherState0 = st in
  match
    encrypt_record_payload kiv
      n
      (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
      (Bertie.Tls13utils.impl_AppData__into_raw payload <: Bertie.Tls13utils.t_Bytes)
      pad
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok v_rec ->
    Core.Result.Result_Ok
    (v_rec, (ClientCipherState0 ae kiv (n +! mk_u64 1) exp <: t_ClientCipherState0)
      <:
      (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8

let encrypt_handshake
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (pad: usize)
      (state: t_DuplexCipherStateH)
     =
  let payload:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13formats.Handshake_data.impl_HandshakeData__to_bytes payload
  in
  match
    encrypt_record_payload state.f_sender_key_iv
      state.f_sender_counter
      (Bertie.Tls13formats.ContentType_Handshake <: Bertie.Tls13formats.t_ContentType)
      payload
      pad
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok v_rec ->
    let state:t_DuplexCipherStateH =
      { state with f_sender_counter = state.f_sender_counter +! mk_u64 1 } <: t_DuplexCipherStateH
    in
    Core.Result.Result_Ok (v_rec, state <: (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8

let encrypt_data (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae kiv n x y exp:t_DuplexCipherState1 = st in
  match
    encrypt_record_payload kiv
      n
      (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
      (Bertie.Tls13utils.impl_AppData__into_raw payload <: Bertie.Tls13utils.t_Bytes)
      pad
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok v_rec ->
    Core.Result.Result_Ok
    (v_rec, (DuplexCipherState1 ae kiv (n +! mk_u64 1) x y exp <: t_DuplexCipherState1)
      <:
      (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8

let rec padlen (b: Bertie.Tls13utils.t_Bytes) (n: usize) =
  if
    n >. mk_usize 0 &&
    (Bertie.Tls13utils.f_declassify #u8
        #u8
        #FStar.Tactics.Typeclasses.solve
        (b.[ n -! mk_usize 1 <: usize ] <: u8)
      <:
      u8) =.
    mk_u8 0
  then mk_usize 1 +! (padlen b (n -! mk_usize 1 <: usize) <: usize)
  else mk_usize 0

let decrypt_record_payload
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ciphertext: Bertie.Tls13utils.t_Bytes)
     =
  let iv_ctr:Bertie.Tls13utils.t_Bytes = derive_iv_ctr kiv.Bertie.Tls13crypto.f_iv n in
  let clen:usize = (Bertie.Tls13utils.impl_Bytes__len ciphertext <: usize) -! mk_usize 5 in
  if clen <=. mk_usize 65536 && clen >. mk_usize 16
  then
    let clen_bytes:t_Array u8 (mk_usize 2) =
      Core.Num.impl_u16__to_be_bytes (cast (clen <: usize) <: u16)
    in
    let ad:Bertie.Tls13utils.t_Bytes =
      Core.Convert.f_into #(t_Array u8 (mk_usize 5))
        #Bertie.Tls13utils.t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (let list =
            [
              mk_u8 23;
              mk_u8 3;
              mk_u8 3;
              clen_bytes.[ mk_usize 0 ] <: u8;
              clen_bytes.[ mk_usize 1 ] <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
          Rust_primitives.Hax.array_of_list 5 list)
    in
    match
      Bertie.Tls13utils.check_eq ad
        (Bertie.Tls13utils.impl_Bytes__slice_range ciphertext
            ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = mk_usize 5 }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      let cip:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl_Bytes__slice_range ciphertext
          ({
              Core.Ops.Range.f_start = mk_usize 5;
              Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len ciphertext <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      (match
          Bertie.Tls13crypto.aead_decrypt kiv.Bertie.Tls13crypto.f_key iv_ctr cip ad
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok plain ->
          let payload_len:usize =
            ((Bertie.Tls13utils.impl_Bytes__len plain <: usize) -!
              (padlen plain (Bertie.Tls13utils.impl_Bytes__len plain <: usize) <: usize)
              <:
              usize) -!
            mk_usize 1
          in
          (match
              Bertie.Tls13formats.impl_ContentType__try_from_u8 (Bertie.Tls13utils.f_declassify #u8
                    #u8
                    #FStar.Tactics.Typeclasses.solve
                    (plain.[ payload_len ] <: u8)
                  <:
                  u8)
              <:
              Core.Result.t_Result Bertie.Tls13formats.t_ContentType u8
            with
            | Core.Result.Result_Ok ct ->
              let payload:Bertie.Tls13utils.t_Bytes =
                Bertie.Tls13utils.impl_Bytes__slice_range plain
                  ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = payload_len }
                    <:
                    Core.Ops.Range.t_Range usize)
              in
              Core.Result.Result_Ok
              (ct, payload <: (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes)
                u8)
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8

let decrypt_zerortt (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_ServerCipherState0) =
  match
    decrypt_record_payload state.f_key_iv state.f_counter ciphertext
    <:
    Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (ct, payload) ->
    (match
        Bertie.Tls13utils.check (ct =.
            (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
            <:
            bool)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl_AppData__new payload,
          ({
              f_key_iv = state.f_key_iv;
              f_counter = state.f_counter +! mk_u64 1;
              f_early_exporter_ms = state.f_early_exporter_ms
            }
            <:
            t_ServerCipherState0)
          <:
          (Bertie.Tls13utils.t_AppData & t_ServerCipherState0))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8

let decrypt_handshake (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_DuplexCipherStateH) =
  match
    decrypt_record_payload state.f_receiver_key_iv state.f_receiver_counter ciphertext
    <:
    Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (ct, payload) ->
    if ct =. (Bertie.Tls13formats.ContentType_Alert <: Bertie.Tls13formats.t_ContentType)
    then
      Core.Result.Result_Err Bertie.Tls13utils.v_GOT_HANDSHAKE_FAILURE_ALERT
      <:
      Core.Result.t_Result
        (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH) u8
    else
      (match
          Bertie.Tls13utils.check (ct =.
              (Bertie.Tls13formats.ContentType_Handshake <: Bertie.Tls13formats.t_ContentType)
              <:
              bool)
          <:
          Core.Result.t_Result Prims.unit u8
        with
        | Core.Result.Result_Ok _ ->
          let state:t_DuplexCipherStateH =
            { state with f_receiver_counter = state.f_receiver_counter +! mk_u64 1 }
            <:
            t_DuplexCipherStateH
          in
          Core.Result.Result_Ok
          (Core.Convert.f_from #Bertie.Tls13formats.Handshake_data.t_HandshakeData
              #Bertie.Tls13utils.t_Bytes
              #FStar.Tactics.Typeclasses.solve
              payload,
            state
            <:
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH))
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH) u8
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result
            (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & t_DuplexCipherStateH)
      u8

let decrypt_data_or_hs (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1 = st in
  match
    decrypt_record_payload kiv n ciphertext
    <:
    Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (ct, payload) ->
    Core.Result.Result_Ok
    (ct, payload, (DuplexCipherState1 ae x y kiv (n +! mk_u64 1) exp <: t_DuplexCipherState1)
      <:
      (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1))
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8

let decrypt_data (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1 = st in
  match
    decrypt_record_payload kiv n ciphertext
    <:
    Core.Result.t_Result (Bertie.Tls13formats.t_ContentType & Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok (ct, payload) ->
    (match
        Bertie.Tls13utils.check (ct =.
            (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
            <:
            bool)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl_AppData__new payload,
          (DuplexCipherState1 ae x y kiv (n +! mk_u64 1) exp <: t_DuplexCipherState1)
          <:
          (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1))
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_DuplexCipherState1) u8
