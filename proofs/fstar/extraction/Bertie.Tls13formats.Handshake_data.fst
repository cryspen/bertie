module Bertie.Tls13formats.Handshake_data
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

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

let get_hs_type (t: u8) : Core.Result.t_Result t_HandshakeType u8 =
  match t with
  | 1uy ->
    Core.Result.Result_Ok (HandshakeType_ClientHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 2uy ->
    Core.Result.Result_Ok (HandshakeType_ServerHello <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 4uy ->
    Core.Result.Result_Ok (HandshakeType_NewSessionTicket <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 5uy ->
    Core.Result.Result_Ok (HandshakeType_EndOfEarlyData <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 8uy ->
    Core.Result.Result_Ok (HandshakeType_EncryptedExtensions <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 11uy ->
    Core.Result.Result_Ok (HandshakeType_Certificate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 13uy ->
    Core.Result.Result_Ok (HandshakeType_CertificateRequest <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 15uy ->
    Core.Result.Result_Ok (HandshakeType_CertificateVerify <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 20uy ->
    Core.Result.Result_Ok (HandshakeType_Finished <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 24uy ->
    Core.Result.Result_Ok (HandshakeType_KeyUpdate <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | 254uy ->
    Core.Result.Result_Ok (HandshakeType_MessageHash <: t_HandshakeType)
    <:
    Core.Result.t_Result t_HandshakeType u8
  | _ -> Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)

type t_HandshakeData = | HandshakeData : Bertie.Tls13utils.t_Bytes -> t_HandshakeData

let impl__HandshakeData__len (self: t_HandshakeData) : usize =
  Bertie.Tls13utils.impl__Bytes__len self._0

let impl__HandshakeData__next_handshake_message (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        (impl__HandshakeData__len self <: usize) <. sz 4 <: bool
      then
        Core.Result.Result_Ok
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8) u8
      else
        let| len:usize =
          Core.Result.impl__map_err (Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__raw_slice
                    self._0
                    ({
                        Core.Ops.Range.f_start = sz 1;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len self._0 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (let message:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range self._0
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                <:
                Core.Ops.Range.t_Range usize)
          in
          let rest:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl__Bytes__slice_range self._0
              ({
                  Core.Ops.Range.f_start = sz 4 +! len <: usize;
                  Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len self._0 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize)
          in
          Core.Result.Result_Ok
          ((HandshakeData message <: t_HandshakeData), (HandshakeData rest <: t_HandshakeData)
            <:
            (t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8) u8)

let impl__HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
    : Core.Result.t_Result t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| message, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message self
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| HandshakeData tagged_message_bytes:t_HandshakeData =
        Core.Result.impl__map_err (if
              (impl__HandshakeData__len payload_rest <: usize) <>. sz 0 <: bool
            then
              Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
              <:
              Core.Result.t_Result t_HandshakeData u8
            else Core.Result.Result_Ok message <: Core.Result.t_Result t_HandshakeData u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let expected_bytes:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (expected_type <: t_HandshakeType) <: u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (Bertie.Tls13utils.check_eq expected_bytes
              (Bertie.Tls13utils.impl__Bytes__slice_range tagged_message_bytes
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (HandshakeData
          (Bertie.Tls13utils.impl__Bytes__slice_range tagged_message_bytes
              ({
                  Core.Ops.Range.f_start = sz 4;
                  Core.Ops.Range.f_end
                  =
                  Bertie.Tls13utils.impl__Bytes__len tagged_message_bytes <: usize
                }
                <:
                Core.Ops.Range.t_Range usize))
          <:
          t_HandshakeData)
        <:
        Core.Result.t_Result t_HandshakeData u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result t_HandshakeData u8) u8)

let impl__HandshakeData__to_bytes (self: t_HandshakeData) : Bertie.Tls13utils.t_Bytes =
  Core.Clone.f_clone self._0

let impl__HandshakeData__to_four (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| message1, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message self
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| message2, payload_rest:(t_HandshakeData & t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message payload_rest
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| message3, payload_rest:(t_HandshakeData & t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message payload_rest
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| message4, payload_rest:(t_HandshakeData & t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message payload_rest
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
        else
          Core.Result.Result_Ok
          (message1, message2, message3, message4
            <:
            (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result
            (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result
            (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8) u8)

let impl__HandshakeData__to_two (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| message1, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message self
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| message2, payload_rest:(t_HandshakeData & t_HandshakeData) =
        Core.Result.impl__map_err (impl__HandshakeData__next_handshake_message payload_rest
            <:
            Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
        else
          Core.Result.Result_Ok (message1, message2 <: (t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8) u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_HandshakeData Bertie.Tls13utils.t_Bytes =
  { f_from = fun (value: Bertie.Tls13utils.t_Bytes) -> HandshakeData value <: t_HandshakeData }

let impl__HandshakeData__concat (self other: t_HandshakeData) : t_HandshakeData =
  let message1:Bertie.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes self in
  let message2:Bertie.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes other in
  let message1:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl__Bytes__extend_from_slice message1 message2
  in
  Core.Convert.f_from message1

let impl__HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist158:Bertie.Tls13utils.t_Bytes =
        Core.Result.impl__map_err (Bertie.Tls13utils.encode_length_u24 handshake_bytes
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist159:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__prefix hoist158
            (Rust_primitives.unsize (let list =
                    [Bertie.Tls13utils.v_U8 (cast (handshake_type <: t_HandshakeType) <: u8) <: u8]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list list)
              <:
              t_Slice u8)
        in
        let hoist160:t_HandshakeData = Core.Convert.f_from hoist159 in
        Core.Result.Result_Ok hoist160 <: Core.Result.t_Result t_HandshakeData u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result t_HandshakeData u8) u8)

let impl__HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
    : bool =
  if (impl__HandshakeData__len self <: usize) <. (start +! sz 4 <: usize)
  then false
  else
    match
      Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__raw_slice self._0
            ({
                Core.Ops.Range.f_start = start +! sz 1 <: usize;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          t_Slice u8)
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        Bertie.Tls13utils.eq1 (self._0.[ start ] <: u8)
          (Bertie.Tls13utils.v_U8 (cast (handshake_type <: t_HandshakeType) <: u8) <: u8)
      then true
      else
        impl__HandshakeData__find_handshake_message self
          handshake_type
          ((start +! sz 4 <: usize) +! len <: usize)
