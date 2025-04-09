module Bertie.Tls13formats.Handshake_data
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

let t_HandshakeType_cast_to_repr (x: t_HandshakeType) =
  match x <: t_HandshakeType with
  | HandshakeType_ClientHello  -> anon_const_HandshakeType_ClientHello__anon_const_0
  | HandshakeType_ServerHello  -> anon_const_HandshakeType_ServerHello__anon_const_0
  | HandshakeType_NewSessionTicket  -> anon_const_HandshakeType_NewSessionTicket__anon_const_0
  | HandshakeType_EndOfEarlyData  -> anon_const_HandshakeType_EndOfEarlyData__anon_const_0
  | HandshakeType_EncryptedExtensions  -> anon_const_HandshakeType_EncryptedExtensions__anon_const_0
  | HandshakeType_Certificate  -> anon_const_HandshakeType_Certificate__anon_const_0
  | HandshakeType_CertificateRequest  -> anon_const_HandshakeType_CertificateRequest__anon_const_0
  | HandshakeType_CertificateVerify  -> anon_const_HandshakeType_CertificateVerify__anon_const_0
  | HandshakeType_Finished  -> anon_const_HandshakeType_Finished__anon_const_0
  | HandshakeType_KeyUpdate  -> anon_const_HandshakeType_KeyUpdate__anon_const_0
  | HandshakeType_MessageHash  -> anon_const_HandshakeType_MessageHash__anon_const_0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Clone.t_Clone t_HandshakeType

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Marker.t_Copy t_HandshakeType

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Fmt.t_Debug t_HandshakeType

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Marker.t_StructuralPartialEq t_HandshakeType

let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Cmp.t_PartialEq t_HandshakeType t_HandshakeType

let impl_5 = impl_5'

let get_hs_type (t: u8) =
  match t <: u8 with
  | Rust_primitives.Integers.MkInt 1 ->
    Core.Result.Result_Ok (HandshakeType_ClientHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 2 ->
    Core.Result.Result_Ok (HandshakeType_ServerHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 4 ->
    Core.Result.Result_Ok (HandshakeType_NewSessionTicket <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 5 ->
    Core.Result.Result_Ok (HandshakeType_EndOfEarlyData <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 8 ->
    Core.Result.Result_Ok (HandshakeType_EncryptedExtensions <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 11 ->
    Core.Result.Result_Ok (HandshakeType_Certificate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 13 ->
    Core.Result.Result_Ok (HandshakeType_CertificateRequest <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 15 ->
    Core.Result.Result_Ok (HandshakeType_CertificateVerify <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 20 ->
    Core.Result.Result_Ok (HandshakeType_Finished <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 24 ->
    Core.Result.Result_Ok (HandshakeType_KeyUpdate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | Rust_primitives.Integers.MkInt 254 ->
    Core.Result.Result_Ok (HandshakeType_MessageHash <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | _ -> Bertie.Tls13utils.tlserr #t_HandshakeType (Bertie.Tls13utils.parse_failed () <: u8)

let impl_HandshakeData__to_bytes (self: t_HandshakeData) =
  Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve self._0

let impl_HandshakeData__len (self: t_HandshakeData) = Bertie.Tls13utils.impl_Bytes__len self._0

let impl_HandshakeData__next_handshake_message (self: t_HandshakeData) =
  if (impl_HandshakeData__len self <: usize) <. mk_usize 4
  then
    Bertie.Tls13utils.tlserr #(t_HandshakeData & t_HandshakeData)
      (Bertie.Tls13utils.parse_failed () <: u8)
  else
    match
      Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl_Bytes__raw_slice self._0
            ({
                Core.Ops.Range.f_start = mk_usize 1;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result usize u8
    with
    | Core.Result.Result_Ok len ->
      let message:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl_Bytes__slice_range self._0
          ({
              Core.Ops.Range.f_start = mk_usize 0;
              Core.Ops.Range.f_end = mk_usize 4 +! len <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let rest:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.impl_Bytes__slice_range self._0
          ({
              Core.Ops.Range.f_start = mk_usize 4 +! len <: usize;
              Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len self._0 <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
      in
      Core.Result.Result_Ok
      ((HandshakeData message <: t_HandshakeData), (HandshakeData rest <: t_HandshakeData)
        <:
        (t_HandshakeData & t_HandshakeData))
      <:
      Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8

let impl_HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
     =
  match
    impl_HandshakeData__next_handshake_message self
    <:
    Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
  with
  | Core.Result.Result_Ok (message, payload_rest) ->
    if (impl_HandshakeData__len payload_rest <: usize) <>. mk_usize 0
    then Bertie.Tls13utils.tlserr #t_HandshakeData (Bertie.Tls13utils.parse_failed () <: u8)
    else
      let HandshakeData tagged_message_bytes:t_HandshakeData = message in
      (match
          Bertie.Tls13utils.check_eq1 (Bertie.Tls13utils.v_U8 (t_HandshakeType_cast_to_repr expected_type

                  <:
                  u8)
              <:
              u8)
            (tagged_message_bytes.[ mk_usize 0 ] <: u8)
          <:
          Core.Result.t_Result Prims.unit u8
        with
        | Core.Result.Result_Ok _ ->
          Core.Result.Result_Ok
          (HandshakeData
            (Bertie.Tls13utils.impl_Bytes__slice_range tagged_message_bytes
                ({
                    Core.Ops.Range.f_start = mk_usize 4;
                    Core.Ops.Range.f_end
                    =
                    Bertie.Tls13utils.impl_Bytes__len tagged_message_bytes <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize))
            <:
            t_HandshakeData)
          <:
          Core.Result.t_Result t_HandshakeData u8
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8

let impl_HandshakeData__to_two (self: t_HandshakeData) =
  match
    impl_HandshakeData__next_handshake_message self
    <:
    Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
  with
  | Core.Result.Result_Ok (message1, payload_rest) ->
    (match
        impl_HandshakeData__next_handshake_message payload_rest
        <:
        Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
      with
      | Core.Result.Result_Ok (message2, payload_rest) ->
        if (impl_HandshakeData__len payload_rest <: usize) <>. mk_usize 0
        then
          Bertie.Tls13utils.tlserr #(t_HandshakeData & t_HandshakeData)
            (Bertie.Tls13utils.parse_failed () <: u8)
        else
          Core.Result.Result_Ok (message1, message2 <: (t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8

let impl_HandshakeData__to_four (self: t_HandshakeData) =
  match
    impl_HandshakeData__next_handshake_message self
    <:
    Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
  with
  | Core.Result.Result_Ok (message1, payload_rest) ->
    (match
        impl_HandshakeData__next_handshake_message payload_rest
        <:
        Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
      with
      | Core.Result.Result_Ok (message2, payload_rest) ->
        (match
            impl_HandshakeData__next_handshake_message payload_rest
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
          with
          | Core.Result.Result_Ok (message3, payload_rest) ->
            (match
                impl_HandshakeData__next_handshake_message payload_rest
                <:
                Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
              with
              | Core.Result.Result_Ok (message4, payload_rest) ->
                if (impl_HandshakeData__len payload_rest <: usize) <>. mk_usize 0
                then
                  Bertie.Tls13utils.tlserr #(t_HandshakeData & t_HandshakeData & t_HandshakeData &
                      t_HandshakeData)
                    (Bertie.Tls13utils.parse_failed () <: u8)
                else
                  Core.Result.Result_Ok
                  (message1, message2, message3, message4
                    <:
                    (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData))
                  <:
                  Core.Result.t_Result
                    (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result
                  (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result
              (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
          u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_HandshakeData Bertie.Tls13utils.t_Bytes =
  {
    f_from_pre = (fun (value: Bertie.Tls13utils.t_Bytes) -> true);
    f_from_post = (fun (value: Bertie.Tls13utils.t_Bytes) (out: t_HandshakeData) -> true);
    f_from = fun (value: Bertie.Tls13utils.t_Bytes) -> HandshakeData value <: t_HandshakeData
  }

let impl_HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: Bertie.Tls13utils.t_Bytes)
     =
  match
    Bertie.Tls13utils.encode_length_u24 handshake_bytes
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist1 ->
    Core.Result.Result_Ok
    (Core.Convert.f_from #t_HandshakeData
        #Bertie.Tls13utils.t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (Bertie.Tls13utils.impl_Bytes__prefix hoist1
            ((let list =
                  [Bertie.Tls13utils.v_U8 (t_HandshakeType_cast_to_repr handshake_type <: u8)]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              <:
              t_Slice u8)
          <:
          Bertie.Tls13utils.t_Bytes))
    <:
    Core.Result.t_Result t_HandshakeData u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8

let impl_HandshakeData__concat (self other: t_HandshakeData) =
  let message1:Bertie.Tls13utils.t_Bytes = impl_HandshakeData__to_bytes self in
  let message2:Bertie.Tls13utils.t_Bytes = impl_HandshakeData__to_bytes other in
  let message1:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl_Bytes__extend_from_slice message1 message2
  in
  Core.Convert.f_from #t_HandshakeData
    #Bertie.Tls13utils.t_Bytes
    #FStar.Tactics.Typeclasses.solve
    message1

let rec impl_HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
     =
  if ((impl_HandshakeData__len self <: usize) -! start <: usize) <. mk_usize 4
  then false
  else
    match
      Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl_Bytes__raw_slice self._0
            ({
                Core.Ops.Range.f_start = start +! mk_usize 1 <: usize;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl_Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result usize u8
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        Bertie.Tls13utils.eq1 (self._0.[ start ] <: u8)
          (Bertie.Tls13utils.v_U8 (t_HandshakeType_cast_to_repr handshake_type <: u8) <: u8)
      then true
      else
        impl_HandshakeData__find_handshake_message self
          handshake_type
          ((start +! mk_usize 4 <: usize) +! len <: usize)
