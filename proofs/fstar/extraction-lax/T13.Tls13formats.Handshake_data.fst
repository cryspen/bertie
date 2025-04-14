module t13.Tls13formats.Handshake_data
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let t_HandshakeType_cast_to_repr (x: t_HandshakeType) =
  match x with
  | HandshakeType_ClientHello  -> discriminant_HandshakeType_ClientHello
  | HandshakeType_ServerHello  -> discriminant_HandshakeType_ServerHello
  | HandshakeType_NewSessionTicket  -> discriminant_HandshakeType_NewSessionTicket
  | HandshakeType_EndOfEarlyData  -> discriminant_HandshakeType_EndOfEarlyData
  | HandshakeType_EncryptedExtensions  -> discriminant_HandshakeType_EncryptedExtensions
  | HandshakeType_Certificate  -> discriminant_HandshakeType_Certificate
  | HandshakeType_CertificateRequest  -> discriminant_HandshakeType_CertificateRequest
  | HandshakeType_CertificateVerify  -> discriminant_HandshakeType_CertificateVerify
  | HandshakeType_Finished  -> discriminant_HandshakeType_Finished
  | HandshakeType_KeyUpdate  -> discriminant_HandshakeType_KeyUpdate
  | HandshakeType_MessageHash  -> discriminant_HandshakeType_MessageHash

let get_hs_type (t: u8) =
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
  | _ -> t13.Tls13utils.tlserr (t13.Tls13utils.parse_failed () <: u8)

let impl__HandshakeData__len (self: t_HandshakeData) = t13.Tls13utils.impl__Bytes__len self._0

let impl__HandshakeData__next_handshake_message (self: t_HandshakeData) =
  if (impl__HandshakeData__len self <: usize) <. sz 4
  then t13.Tls13utils.tlserr (t13.Tls13utils.parse_failed () <: u8)
  else
    match
      t13.Tls13utils.length_u24_encoded (t13.Tls13utils.impl__Bytes__raw_slice self._0
            ({
                Core.Ops.Range.f_start = sz 1;
                Core.Ops.Range.f_end = t13.Tls13utils.impl__Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          t_Slice u8)
    with
    | Core.Result.Result_Ok len ->
      let message:t13.Tls13utils.t_Bytes =
        t13.Tls13utils.impl__Bytes__slice_range self._0
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 4 +! len <: usize }
            <:
            Core.Ops.Range.t_Range usize)
      in
      let rest:t13.Tls13utils.t_Bytes =
        t13.Tls13utils.impl__Bytes__slice_range self._0
          ({
              Core.Ops.Range.f_start = sz 4 +! len <: usize;
              Core.Ops.Range.f_end = t13.Tls13utils.impl__Bytes__len self._0 <: usize
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

let impl__HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
     =
  match impl__HandshakeData__next_handshake_message self with
  | Core.Result.Result_Ok (message, payload_rest) ->
    (match
        if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
        then t13.Tls13utils.tlserr (t13.Tls13utils.parse_failed () <: u8)
        else Core.Result.Result_Ok message <: Core.Result.t_Result t_HandshakeData u8
      with
      | Core.Result.Result_Ok (HandshakeData tagged_message_bytes) ->
        let expected_bytes:t13.Tls13utils.t_Bytes =
          t13.Tls13utils.bytes1 (t_HandshakeType_cast_to_repr expected_type <: u8)
        in
        (match
            t13.Tls13utils.check_eq expected_bytes
              (t13.Tls13utils.impl__Bytes__slice_range tagged_message_bytes
                  ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t13.Tls13utils.t_Bytes)
          with
          | Core.Result.Result_Ok _ ->
            Core.Result.Result_Ok
            (HandshakeData
              (t13.Tls13utils.impl__Bytes__slice_range tagged_message_bytes
                  ({
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end
                      =
                      t13.Tls13utils.impl__Bytes__len tagged_message_bytes <: usize
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
        Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8

let impl__HandshakeData__to_bytes (self: t_HandshakeData) = Core.Clone.f_clone self._0

let impl__HandshakeData__to_four (self: t_HandshakeData) =
  match impl__HandshakeData__next_handshake_message self with
  | Core.Result.Result_Ok (message1, payload_rest) ->
    (match impl__HandshakeData__next_handshake_message payload_rest with
      | Core.Result.Result_Ok (message2, payload_rest) ->
        (match impl__HandshakeData__next_handshake_message payload_rest with
          | Core.Result.Result_Ok (message3, payload_rest) ->
            (match impl__HandshakeData__next_handshake_message payload_rest with
              | Core.Result.Result_Ok (message4, payload_rest) ->
                if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
                then t13.Tls13utils.tlserr (t13.Tls13utils.parse_failed () <: u8)
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

let impl__HandshakeData__to_two (self: t_HandshakeData) =
  match impl__HandshakeData__next_handshake_message self with
  | Core.Result.Result_Ok (message1, payload_rest) ->
    (match impl__HandshakeData__next_handshake_message payload_rest with
      | Core.Result.Result_Ok (message2, payload_rest) ->
        if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
        then t13.Tls13utils.tlserr (t13.Tls13utils.parse_failed () <: u8)
        else
          Core.Result.Result_Ok (message1, message2 <: (t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8

let impl__HandshakeData__concat (self other: t_HandshakeData) =
  let message1:t13.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes self in
  let message2:t13.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes other in
  let message1:t13.Tls13utils.t_Bytes =
    t13.Tls13utils.impl__Bytes__extend_from_slice message1 message2
  in
  Core.Convert.f_from message1

let impl__HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: t13.Tls13utils.t_Bytes)
     =
  match t13.Tls13utils.encode_length_u24 handshake_bytes with
  | Core.Result.Result_Ok hoist138 ->
    Core.Result.Result_Ok
    (Core.Convert.f_from (t13.Tls13utils.impl__Bytes__prefix hoist138
            (Rust_primitives.unsize (let list =
                    [
                      t13.Tls13utils.v_U8 (t_HandshakeType_cast_to_repr handshake_type <: u8)
                      <:
                      u8
                    ]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              t_Slice u8)
          <:
          t13.Tls13utils.t_Bytes))
    <:
    Core.Result.t_Result t_HandshakeData u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_HandshakeData u8

let rec impl__HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
     =
  if (impl__HandshakeData__len self <: usize) <. (start +! sz 4 <: usize)
  then false
  else
    match
      t13.Tls13utils.length_u24_encoded (t13.Tls13utils.impl__Bytes__raw_slice self._0
            ({
                Core.Ops.Range.f_start = start +! sz 1 <: usize;
                Core.Ops.Range.f_end = t13.Tls13utils.impl__Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          t_Slice u8)
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        t13.Tls13utils.eq1 (self._0.[ start ] <: u8)
          (t13.Tls13utils.v_U8 (t_HandshakeType_cast_to_repr handshake_type <: u8) <: u8)
      then true
      else
        impl__HandshakeData__find_handshake_message self
          handshake_type
          ((start +! sz 4 <: usize) +! len <: usize)
