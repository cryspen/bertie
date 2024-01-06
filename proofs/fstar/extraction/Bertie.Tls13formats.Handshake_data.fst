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

let impl__HandshakeData__from_bytes
      (handshake_type: t_HandshakeType)
      (handshake_bytes: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* hoist306:Bertie.Tls13utils.t_Bytes =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.encode_length_u24 handshake_bytes
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist305:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist305)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            Bertie.Tls13utils.t_Bytes
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let hoist307:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes1 (cast (handshake_type
                      <:
                      t_HandshakeType)
                  <:
                  u8)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist306
        in
        let hoist308:t_HandshakeData = Core.Convert.f_from hoist307 in
        Core.Result.Result_Ok hoist308 <: Core.Result.t_Result t_HandshakeData u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
        (Core.Result.t_Result t_HandshakeData u8))

let impl__HandshakeData__len (self: t_HandshakeData) : usize =
  Bertie.Tls13utils.impl__Bytes__len self._0

let impl__HandshakeData__next_handshake_message (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        (impl__HandshakeData__len self <: usize) <. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      else
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__slice_range
                      self._0
                      ({
                          Core.Ops.Range.f_start = sz 1;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len self._0 <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist309:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist309)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8) usize
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8) usize
        in
        Core.Ops.Control_flow.ControlFlow_Continue
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
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8))

let impl__HandshakeData__as_handshake_message
      (self: t_HandshakeData)
      (expected_type: t_HandshakeType)
    : Core.Result.t_Result t_HandshakeData u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* message, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message self
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist310:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist310)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            (t_HandshakeData & t_HandshakeData)
      in
      let* HandshakeData tagged_message_bytes:t_HandshakeData =
        match
          Core.Ops.Try_trait.f_branch (if
                (impl__HandshakeData__len payload_rest <: usize) <>. sz 0 <: bool
              then
                Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
                <:
                Core.Result.t_Result t_HandshakeData u8
              else Core.Result.Result_Ok message <: Core.Result.t_Result t_HandshakeData u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist311:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist311)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            t_HandshakeData
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
            t_HandshakeData
      in
      let expected_bytes:Bertie.Tls13utils.t_Bytes =
        Bertie.Tls13utils.bytes1 (cast (expected_type <: t_HandshakeType) <: u8)
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.check_eq expected_bytes
                (Bertie.Tls13utils.impl__Bytes__slice_range tagged_message_bytes
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Bertie.Tls13utils.t_Bytes)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist312:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result t_HandshakeData u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist312)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8) Prims.unit
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8) Prims.unit
      in
      Core.Ops.Control_flow.ControlFlow_Continue
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
      Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result t_HandshakeData u8)
        (Core.Result.t_Result t_HandshakeData u8))

let impl__HandshakeData__to_bytes (self: t_HandshakeData) : Bertie.Tls13utils.t_Bytes =
  Core.Clone.f_clone self._0

let impl__HandshakeData__concat (self other: t_HandshakeData) : t_HandshakeData =
  let message1:Bertie.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes self in
  let message2:Bertie.Tls13utils.t_Bytes = impl__HandshakeData__to_bytes other in
  let message1:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.impl__Bytes__extend_from_slice message1 message2
  in
  Core.Convert.f_from message1

let impl__HandshakeData__to_four (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData)
      u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* message1, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message self
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist313:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist313)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      let* message2, payload_rest:(t_HandshakeData & t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message payload_rest
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist314:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist314)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      let* message3, payload_rest:(t_HandshakeData & t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message payload_rest
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist315:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist315)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      let* message4, payload_rest:(t_HandshakeData & t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message payload_rest
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist316:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result
                  (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist316)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result
                (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
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
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result
            (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8)
        (Core.Result.t_Result
            (t_HandshakeData & t_HandshakeData & t_HandshakeData & t_HandshakeData) u8))

let impl__HandshakeData__to_two (self: t_HandshakeData)
    : Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* message1, payload_rest:(t_HandshakeData &
        t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message self
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist317:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist317)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      let* message2, payload_rest:(t_HandshakeData & t_HandshakeData) =
        match
          Core.Ops.Try_trait.f_branch (impl__HandshakeData__next_handshake_message payload_rest
              <:
              Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist318:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist318)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
            (t_HandshakeData & t_HandshakeData)
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (if (impl__HandshakeData__len payload_rest <: usize) <>. sz 0
        then Bertie.Tls13utils.tlserr (Bertie.Tls13utils.parse_failed () <: u8)
        else
          Core.Result.Result_Ok (message1, message2 <: (t_HandshakeData & t_HandshakeData))
          <:
          Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
      <:
      Core.Ops.Control_flow.t_ControlFlow
        (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8)
        (Core.Result.t_Result (t_HandshakeData & t_HandshakeData) u8))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From t_HandshakeData Bertie.Tls13utils.t_Bytes =
  { f_from = fun (value: Bertie.Tls13utils.t_Bytes) -> HandshakeData value <: t_HandshakeData }

let impl__HandshakeData__find_handshake_message
      (self: t_HandshakeData)
      (handshake_type: t_HandshakeType)
      (start: usize)
    : bool =
  if (impl__HandshakeData__len self <: usize) <. (start +! sz 4 <: usize)
  then false
  else
    match
      Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__slice_range self._0
            ({
                Core.Ops.Range.f_start = start +! sz 1 <: usize;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len self._0 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
    with
    | Core.Result.Result_Err _ -> false
    | Core.Result.Result_Ok len ->
      if
        Bertie.Tls13utils.eq1 (self._0.[ start ] <: Bertie.Tls13utils.t_U8)
          (Core.Convert.f_from (cast (handshake_type <: t_HandshakeType) <: u8)
            <:
            Bertie.Tls13utils.t_U8)
      then true
      else
        impl__HandshakeData__find_handshake_message self
          handshake_type
          ((start +! sz 4 <: usize) +! len <: usize)
