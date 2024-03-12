module Bertie.Tls13record
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let derive_iv_ctr (iv: Bertie.Tls13utils.t_Bytes) (n: u64) =
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
          magic ()
          // Rust_primitives.Hax.Monomorphized_update_at.update_at_usize iv_ctr i (iv.[ i ] <: u8)
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
          magic ())
          // Rust_primitives.Hax.Monomorphized_update_at.update_at_usize iv_ctr
          //   ((i +! (Bertie.Tls13utils.impl__Bytes__len iv <: usize) <: usize) -! sz 8 <: usize)
          //   ((iv.[ (i +! (Bertie.Tls13utils.impl__Bytes__len iv <: usize) <: usize) -! sz 8 <: usize
          //       ]
          //       <:
          //       u8) ^.
          //     (counter.[ i ] <: u8)
          //     <:
          //     u8)
          // <:
          // Bertie.Tls13utils.t_Bytes)
  in
  iv_ctr

let rec padlen (b: Bertie.Tls13utils.t_Bytes) (n: usize) =
  if n >. sz 0 && (Bertie.Tls13utils.f_declassify (b.[ n -! sz 1 <: usize ] <: u8) <: u8) =. 0uy
  then sz 1 +! (padlen b (n -! sz 1 <: usize) <: usize)
  else sz 0

let decrypt_record_payload
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ciphertext: Bertie.Tls13utils.t_Bytes)
     =
  let iv_ctr:Bertie.Tls13utils.t_Bytes = derive_iv_ctr kiv.Bertie.Tls13crypto.f_iv n in
  let clen:usize = (Bertie.Tls13utils.impl__Bytes__len ciphertext <: usize) -! sz 5 in
  if clen <=. sz 65536 && clen >. sz 16
  then
    let clen_bytes:t_Array u8 (sz 2) =
      magic ()
      // Core.Num.impl__u16__to_be_bytes (cast (clen <: usize) <: u16)
    in
    let ad:Bertie.Tls13utils.t_Bytes =
      Core.Convert.f_into (let list =
            [23uy; 3uy; 3uy; clen_bytes.[ sz 0 ] <: u8; clen_bytes.[ sz 1 ] <: u8]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
          Rust_primitives.Hax.array_of_list 5 list)
    in
    match
      Bertie.Tls13utils.check_eq ad
        (Bertie.Tls13utils.impl__Bytes__slice_range ciphertext
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 5 }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
    with
    | Core.Result.Result_Ok _ ->
      let cip:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl__Bytes__slice_range ciphertext
          ({
              Core.Ops.Range.f_start = sz 5;
              Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ciphertext <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      (match Bertie.Tls13crypto.aead_decrypt kiv.Bertie.Tls13crypto.f_key iv_ctr cip ad with
        | Core.Result.Result_Ok plain ->
          let payload_len:usize =
            ((Bertie.Tls13utils.impl__Bytes__len plain <: usize) -!
              (padlen plain (Bertie.Tls13utils.impl__Bytes__len plain <: usize) <: usize)
              <:
              usize) -!
            sz 1
          in
          (match
              Bertie.Tls13formats.impl__ContentType__try_from_u8 (Bertie.Tls13utils.f_declassify (plain.[
                        payload_len ]
                      <:
                      u8)
                  <:
                  u8)
            with
            | Core.Result.Result_Ok ct ->
              let payload:Bertie.Tls13utils.t_Bytes =
                Bertie.Tls13utils.impl__Bytes__slice_range plain
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = payload_len }
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

let encrypt_record_payload
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (n: u64)
      (ct: Bertie.Tls13formats.t_ContentType)
      (payload: Bertie.Tls13utils.t_Bytes)
      (pad: usize)
     =
  let iv_ctr:Bertie.Tls13utils.t_Bytes = derive_iv_ctr key_iv.Bertie.Tls13crypto.f_iv n in
  let inner_plaintext:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat payload
          (Bertie.Tls13utils.bytes1 (magic () <: u8)
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
      magic ()
      // Core.Num.impl__u16__to_be_bytes (cast (clen <: usize) <: u16) 
    in
    let ad:Bertie.Tls13utils.t_Bytes =
      Core.Convert.f_into (let list =
            [23uy; 3uy; 3uy; clenb.[ sz 0 ] <: u8; clenb.[ sz 1 ] <: u8]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
          Rust_primitives.Hax.array_of_list 5 list)
    in
    match
      Bertie.Tls13crypto.aead_encrypt key_iv.Bertie.Tls13crypto.f_key iv_ctr inner_plaintext ad
    with
    | Core.Result.Result_Ok cip ->
      let v_rec:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ad cip in
      Core.Result.Result_Ok v_rec <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let impl__DuplexCipherStateH__new
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

let client_cipher_state0
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv: Bertie.Tls13crypto.t_AeadKeyIV)
      (c: u64)
      (k: Bertie.Tls13utils.t_Bytes)
     = ClientCipherState0 ae kiv c k <: t_ClientCipherState0

let decrypt_data (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1 = st in
  match decrypt_record_payload kiv n ciphertext with
  | Core.Result.Result_Ok (ct, payload) ->
    (match
        Bertie.Tls13utils.check (ct =.
            (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
            <:
            bool)
      with
      | Core.Result.Result_Ok _ ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__AppData__new payload,
          (DuplexCipherState1 ae x y kiv (n +! 1uL) exp <: t_DuplexCipherState1)
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

let decrypt_data_or_hs (ciphertext: Bertie.Tls13utils.t_Bytes) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae x y kiv n exp:t_DuplexCipherState1 = st in
  match decrypt_record_payload kiv n ciphertext with
  | Core.Result.Result_Ok (ct, payload) ->
    Core.Result.Result_Ok
    (ct, payload, (DuplexCipherState1 ae x y kiv (n +! 1uL) exp <: t_DuplexCipherState1)
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

let decrypt_handshake (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_DuplexCipherStateH) =
  match decrypt_record_payload state.f_receiver_key_iv state.f_receiver_counter ciphertext with
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
        with
        | Core.Result.Result_Ok _ ->
          let state:t_DuplexCipherStateH =
            { state with f_receiver_counter = state.f_receiver_counter +! 1uL }
            <:
            t_DuplexCipherStateH
          in
          Core.Result.Result_Ok
          (Core.Convert.f_from payload, state
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

let decrypt_zerortt (ciphertext: Bertie.Tls13utils.t_Bytes) (state: t_ServerCipherState0) =
  match decrypt_record_payload state.f_key_iv state.f_counter ciphertext with
  | Core.Result.Result_Ok (ct, payload) ->
    (match
        Bertie.Tls13utils.check (ct =.
            (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
            <:
            bool)
      with
      | Core.Result.Result_Ok _ ->
        Core.Result.Result_Ok
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
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_AppData & t_ServerCipherState0) u8

let duplex_cipher_state1
      (ae: Bertie.Tls13crypto.t_AeadAlgorithm)
      (kiv1: Bertie.Tls13crypto.t_AeadKeyIV)
      (c1: u64)
      (kiv2: Bertie.Tls13crypto.t_AeadKeyIV)
      (c2: u64)
      (k: Bertie.Tls13utils.t_Bytes)
     = DuplexCipherState1 ae kiv1 c1 kiv2 c2 k <: t_DuplexCipherState1

let encrypt_data (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_DuplexCipherState1) =
  let DuplexCipherState1 ae kiv n x y exp:t_DuplexCipherState1 = st in
  match
    encrypt_record_payload kiv
      n
      (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
      (Bertie.Tls13utils.impl__AppData__into_raw payload <: Bertie.Tls13utils.t_Bytes)
      pad
  with
  | Core.Result.Result_Ok v_rec ->
    Core.Result.Result_Ok
    (v_rec, (DuplexCipherState1 ae kiv (n +! 1uL) x y exp <: t_DuplexCipherState1)
      <:
      (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherState1) u8

let encrypt_handshake
      (payload: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (pad: usize)
      (state: t_DuplexCipherStateH)
     =
  let payload:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__to_bytes payload
  in
  match
    encrypt_record_payload state.f_sender_key_iv
      state.f_sender_counter
      (Bertie.Tls13formats.ContentType_Handshake <: Bertie.Tls13formats.t_ContentType)
      payload
      pad
  with
  | Core.Result.Result_Ok v_rec ->
    let state:t_DuplexCipherStateH =
      { state with f_sender_counter = state.f_sender_counter +! 1uL } <: t_DuplexCipherStateH
    in
    Core.Result.Result_Ok (v_rec, state <: (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_DuplexCipherStateH) u8

let encrypt_zerortt (payload: Bertie.Tls13utils.t_AppData) (pad: usize) (st: t_ClientCipherState0) =
  let ClientCipherState0 ae kiv n exp:t_ClientCipherState0 = st in
  match
    encrypt_record_payload kiv
      n
      (Bertie.Tls13formats.ContentType_ApplicationData <: Bertie.Tls13formats.t_ContentType)
      (Bertie.Tls13utils.impl__AppData__into_raw payload <: Bertie.Tls13utils.t_Bytes)
      pad
  with
  | Core.Result.Result_Ok v_rec ->
    Core.Result.Result_Ok
    (v_rec, (ClientCipherState0 ae kiv (n +! 1uL) exp <: t_ClientCipherState0)
      <:
      (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0))
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & t_ClientCipherState0) u8

let server_cipher_state0
      (key_iv: Bertie.Tls13crypto.t_AeadKeyIV)
      (counter: u64)
      (early_exporter_ms: Bertie.Tls13utils.t_Bytes)
     =
  { f_key_iv = key_iv; f_counter = counter; f_early_exporter_ms = early_exporter_ms }
  <:
  t_ServerCipherState0
