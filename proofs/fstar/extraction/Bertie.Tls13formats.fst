module Bertie.Tls13formats
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

let t_AlertDescription_cast_to_repr (x: t_AlertDescription) =
  match x <: t_AlertDescription with
  | AlertDescription_CloseNotify  -> discriminant_AlertDescription_CloseNotify
  | AlertDescription_UnexpectedMessage  -> discriminant_AlertDescription_UnexpectedMessage
  | AlertDescription_BadRecordMac  -> discriminant_AlertDescription_BadRecordMac
  | AlertDescription_RecordOverflow  -> discriminant_AlertDescription_RecordOverflow
  | AlertDescription_HandshakeFailure  -> discriminant_AlertDescription_HandshakeFailure
  | AlertDescription_BadCertificate  -> discriminant_AlertDescription_BadCertificate
  | AlertDescription_UnsupportedCertificate  -> discriminant_AlertDescription_UnsupportedCertificate
  | AlertDescription_CertificateRevoked  -> discriminant_AlertDescription_CertificateRevoked
  | AlertDescription_CertificateExpired  -> discriminant_AlertDescription_CertificateExpired
  | AlertDescription_CertificateUnknown  -> discriminant_AlertDescription_CertificateUnknown
  | AlertDescription_IllegalParameter  -> discriminant_AlertDescription_IllegalParameter
  | AlertDescription_UnknownCa  -> discriminant_AlertDescription_UnknownCa
  | AlertDescription_AccessDenied  -> discriminant_AlertDescription_AccessDenied
  | AlertDescription_DecodeError  -> discriminant_AlertDescription_DecodeError
  | AlertDescription_DecryptError  -> discriminant_AlertDescription_DecryptError
  | AlertDescription_ProtocolVersion  -> discriminant_AlertDescription_ProtocolVersion
  | AlertDescription_InsufficientSecurity  -> discriminant_AlertDescription_InsufficientSecurity
  | AlertDescription_InternalError  -> discriminant_AlertDescription_InternalError
  | AlertDescription_InappropriateFallback  -> discriminant_AlertDescription_InappropriateFallback
  | AlertDescription_UserCanceled  -> discriminant_AlertDescription_UserCanceled
  | AlertDescription_MissingExtension  -> discriminant_AlertDescription_MissingExtension
  | AlertDescription_UnsupportedExtension  -> discriminant_AlertDescription_UnsupportedExtension
  | AlertDescription_UnrecognizedName  -> discriminant_AlertDescription_UnrecognizedName
  | AlertDescription_BadCertificateStatusResponse  ->
    discriminant_AlertDescription_BadCertificateStatusResponse
  | AlertDescription_UnknownPskIdentity  -> discriminant_AlertDescription_UnknownPskIdentity
  | AlertDescription_CertificateRequired  -> discriminant_AlertDescription_CertificateRequired
  | AlertDescription_NoApplicationProtocol  -> discriminant_AlertDescription_NoApplicationProtocol

let t_AlertLevel_cast_to_repr (x: t_AlertLevel) =
  match x <: t_AlertLevel with
  | AlertLevel_Warning  -> discriminant_AlertLevel_Warning
  | AlertLevel_Fatal  -> discriminant_AlertLevel_Fatal

let t_ContentType_cast_to_repr (x: t_ContentType) =
  match x <: t_ContentType with
  | ContentType_Invalid  -> discriminant_ContentType_Invalid
  | ContentType_ChangeCipherSpec  -> discriminant_ContentType_ChangeCipherSpec
  | ContentType_Alert  -> discriminant_ContentType_Alert
  | ContentType_Handshake  -> discriminant_ContentType_Handshake
  | ContentType_ApplicationData  -> discriminant_ContentType_ApplicationData

let impl__Transcript__new (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm) =
  {
    f_hash_algorithm = hash_algorithm;
    f_transcript
    =
    Bertie.Tls13formats.Handshake_data.HandshakeData (Bertie.Tls13utils.impl__Bytes__new ())
    <:
    Bertie.Tls13formats.Handshake_data.t_HandshakeData
  }
  <:
  t_Transcript

let application_data_instead_of_handshake (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE
  <:
  Core.Result.t_Result Prims.unit u8

let invalid_compression_list (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_COMPRESSION_LIST
  <:
  Core.Result.t_Result Prims.unit u8

let invalid_compression_method_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_DECODE_ERROR <: Core.Result.t_Result Prims.unit u8

let protocol_version_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_PROTOCOL_VERSION_ALERT
  <:
  Core.Result.t_Result Prims.unit u8

let unsupported_cipher_alert (_: Prims.unit) =
  Core.Result.Result_Err Bertie.Tls13utils.v_UNSUPPORTED_ALGORITHM
  <:
  Core.Result.t_Result Prims.unit u8

let impl__ContentType__try_from_u8 (t: u8) =
  match t <: u8 with
  | 20uy ->
    Core.Result.Result_Ok (ContentType_ChangeCipherSpec <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 21uy ->
    Core.Result.Result_Ok (ContentType_Alert <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 22uy ->
    Core.Result.Result_Ok (ContentType_Handshake <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | 23uy ->
    Core.Result.Result_Ok (ContentType_ApplicationData <: t_ContentType)
    <:
    Core.Result.t_Result t_ContentType u8
  | _ ->
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result t_ContentType u8

let check_r_len (rlen: usize) =
  if rlen <. sz 32 || rlen >. sz 33
  then
    Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
    <:
    Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8

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

let impl__Transcript__add
      (self: t_Transcript)
      (msg: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  let self:t_Transcript =
    {
      self with
      f_transcript
      =
      Bertie.Tls13formats.Handshake_data.impl__HandshakeData__concat self.f_transcript msg
    }
    <:
    t_Transcript
  in
  self

let impl__Extensions__merge (self e2: t_Extensions) =
  match
    merge_opts #Bertie.Tls13utils.t_Bytes self.f_sni e2.f_sni
    <:
    Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
  with
  | Core.Result.Result_Ok hoist37 ->
    (match
        merge_opts #Bertie.Tls13utils.t_Bytes self.f_key_share e2.f_key_share
        <:
        Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
      with
      | Core.Result.Result_Ok hoist36 ->
        (match
            merge_opts #Bertie.Tls13utils.t_Bytes self.f_ticket e2.f_ticket
            <:
            Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
          with
          | Core.Result.Result_Ok hoist35 ->
            (match
                merge_opts #Bertie.Tls13utils.t_Bytes self.f_binder e2.f_binder
                <:
                Core.Result.t_Result (Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
              with
              | Core.Result.Result_Ok hoist34 ->
                Core.Result.Result_Ok
                ({ f_sni = hoist37; f_key_share = hoist36; f_ticket = hoist35; f_binder = hoist34 }
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

let impl__Transcript__transcript_hash (self: t_Transcript) =
  match
    Bertie.Tls13crypto.impl__HashAlgorithm__hash self.f_hash_algorithm
      self.f_transcript.Bertie.Tls13formats.Handshake_data._0
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok th ->
    Core.Result.Result_Ok th <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let impl__Transcript__transcript_hash_without_client_hello
      (self: t_Transcript)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
      (trunc_len: usize)
     =
  let Bertie.Tls13formats.Handshake_data.HandshakeData ch:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    client_hello
  in
  Bertie.Tls13crypto.impl__HashAlgorithm__hash self.f_hash_algorithm
    (Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
            #FStar.Tactics.Typeclasses.solve
            self.f_transcript.Bertie.Tls13formats.Handshake_data._0
          <:
          Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl__Bytes__slice_range client_hello
              .Bertie.Tls13formats.Handshake_data._0
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = trunc_len }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Bertie.Tls13utils.t_Bytes)

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
  let chlen:usize = Bertie.Tls13utils.impl__Bytes__len ch in
  let hlen:usize =
    Bertie.Tls13crypto.impl__HashAlgorithm__hash_len (Bertie.Tls13crypto.impl__Algorithms__hash ciphersuite

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
        (Bertie.Tls13utils.impl__Bytes__update_slice ch trunc_len m (sz 0) hlen)
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

let check_psk_shared_key (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match Bertie.Tls13utils.length_u16_encoded ch <: Core.Result.t_Result usize u8 with
  | Core.Result.Result_Ok len_id ->
    (match
        Bertie.Tls13utils.length_u16_encoded (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = sz 2 +! len_id <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok len_tkt ->
        if len_id =. (len_tkt +! sz 6 <: usize)
        then
          match
            Bertie.Tls13utils.check_length_encoding_u16_slice (ch.[ {
                    Core.Ops.Range.f_start = sz 2 +! len_id <: usize;
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
                        Core.Ops.Range.f_start = sz 4 +! len_id <: usize;
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
                  (((Core.Slice.impl__len #u8 ch <: usize) -! sz 5 <: usize) -! len_id <: usize) <>.
                  (Bertie.Tls13crypto.impl__HashAlgorithm__hash_len (Bertie.Tls13crypto.impl__Algorithms__hash
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
  | Core.Result.Result_Ok hoist62 ->
    (match
        Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__prefix hoist62
              (build_server_name__PREFIX2 <: t_Slice u8)
            <:
            Bertie.Tls13utils.t_Bytes)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist65 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist65
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist67 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__prefix hoist67
                (build_server_name__PREFIX1 <: t_Slice u8))
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
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
    Bertie.Tls13utils.check_eq_with_slice ((let list = [Bertie.Tls13utils.v_U8 1uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
      client_hello
      (sz 1)
      (sz 2)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let check_server_name (extension: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice extension
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13utils.check_eq_with_slice ((let list = [Bertie.Tls13utils.v_U8 0uy] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            <:
            t_Slice u8)
          extension
          (sz 2)
          (sz 3)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        (match
            Bertie.Tls13utils.check_length_encoding_u16_slice (extension.[ {
                    Core.Ops.Range.f_start = sz 3;
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
                      Core.Ops.Range.f_start = sz 5;
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

let check_server_psk_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  Bertie.Tls13utils.check_eq_slice ((let list =
          [Bertie.Tls13utils.v_U8 0uy; Bertie.Tls13utils.v_U8 0uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    b

let check_server_supported_version (v__algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  Bertie.Tls13utils.check_eq_slice ((let list =
          [Bertie.Tls13utils.v_U8 3uy; Bertie.Tls13utils.v_U8 4uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    b

let check_supported_versions (client_hello: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u8_slice client_hello
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    Bertie.Tls13utils.check_mem ((let list =
            [Bertie.Tls13utils.v_U8 3uy; Bertie.Tls13utils.v_U8 4uy]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
      (client_hello.[ {
            Core.Ops.Range.f_start = sz 1;
            Core.Ops.Range.f_end = Core.Slice.impl__len #u8 client_hello <: usize
          }
          <:
          Core.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let finished (vd: Bertie.Tls13utils.t_Bytes) =
  Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Finished
      <:
      Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    vd

let psk_key_exchange_modes (_: Prims.unit) =
  match
    Bertie.Tls13utils.encode_length_u8 ((let list = [Bertie.Tls13utils.v_U8 1uy] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist69 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist69
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist71 ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__Bytes__prefix hoist71
            (psk_key_exchange_modes__PSK_MODE_PREFIX <: t_Slice u8))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let server_certificate (v__algs: Bertie.Tls13crypto.t_Algorithms) (cert: Bertie.Tls13utils.t_Bytes) =
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
            Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new ()
                <:
                Bertie.Tls13utils.t_Bytes)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok ext ->
            (match
                Bertie.Tls13utils.encode_length_u24 (Bertie.Tls13utils.impl__Bytes__concat crt ext
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok crts ->
                Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeType)
                  (Bertie.Tls13utils.impl__Bytes__concat creq crts <: Bertie.Tls13utils.t_Bytes)
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

let check_server_key_share (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  match
    Bertie.Tls13crypto.impl__Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist87 ->
    (match
        Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw hoist87
            <:
            t_Slice u8)
          b
          (sz 0)
          (sz 2)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        (match
            Bertie.Tls13utils.check_length_encoding_u16_slice (b.[ {
                    Core.Ops.Range.f_start = sz 2;
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
                      Core.Ops.Range.f_start = sz 4;
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

let check_server_extension (algs: Bertie.Tls13crypto.t_Algorithms) (b: t_Slice u8) =
  if (Core.Slice.impl__len #u8 b <: usize) <. sz 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
  else
    let l0:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (b.[ sz 0 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    let l1:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (b.[ sz 1 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    match
      Bertie.Tls13utils.length_u16_encoded (b.[ {
              Core.Ops.Range.f_start = sz 2;
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
        | 0uy, 43uy ->
          (match
              check_server_supported_version algs
                (b.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok ok ->
              Core.Result.Result_Ok
              (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | 0uy, 51uy ->
          (match
              check_server_key_share algs
                (b.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
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
              (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | 0uy, 41uy ->
          (match
              check_server_psk_shared_key algs
                (b.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok ok ->
              Core.Result.Result_Ok
              (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err
              <:
              Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
        | _ ->
          Core.Result.Result_Ok
          (sz 4 +! len, out <: (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes))
          <:
          Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result (usize & Core.Option.t_Option Bertie.Tls13utils.t_Bytes) u8

let check_signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist90 ->
        Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl__Bytes__as_raw hoist90 <: t_Slice u8)
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let check_supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl__Algorithms__supported_group algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist92 ->
        Bertie.Tls13utils.check_mem (Bertie.Tls13utils.impl__Bytes__as_raw hoist92 <: t_Slice u8)
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13crypto.impl__Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist95 ->
    (match
        Bertie.Tls13utils.encode_length_u16 gx <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist94 ->
        let ks:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat hoist95 hoist94 in
        (match
            Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist96 ->
            (match
                Bertie.Tls13utils.encode_length_u16 hoist96
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok hoist98 ->
                Core.Result.Result_Ok
                (Bertie.Tls13utils.impl__Bytes__prefix hoist98 (key_shares__PREFIX <: t_Slice u8))
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

let supported_groups (algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13crypto.impl__Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist100 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist100
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist102 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist102
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist104 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__prefix hoist104
                (supported_groups__SUPPORTED_GROUPS_PREFIX <: t_Slice u8))
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
            [Bertie.Tls13utils.v_U8 3uy; Bertie.Tls13utils.v_U8 4uy]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist106 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist106
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist108 ->
        Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__Bytes__concat (Core.Convert.f_from #Bertie.Tls13utils.t_Bytes
                #(t_Array u8 (sz 2))
                #FStar.Tactics.Typeclasses.solve
                (let list = [0uy; 43uy] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                  Rust_primitives.Hax.array_of_list 2 list)
              <:
              Bertie.Tls13utils.t_Bytes)
            hoist108)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let ecdsa_signature (sv: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl__Bytes__len sv <: usize) <>. sz 64
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
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
      if
        (Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (r.[ sz 0 ] <: u8)
          <:
          u8) >=.
        128uy
      then
        let r:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
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
        (Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (s.[ sz 0 ] <: u8)
          <:
          u8) >=.
        128uy
      then
        let s:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat b0 s in
        s
      else s
    in
    match
      Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw r <: t_Slice u8)
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    with
    | Core.Result.Result_Ok hoist112 ->
      (match
          Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw s <: t_Slice u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok hoist114 ->
          (match
              Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw (Bertie.Tls13utils.impl__Bytes__concat
                        (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat
                                (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
                                    #FStar.Tactics.Typeclasses.solve
                                    b2
                                  <:
                                  Bertie.Tls13utils.t_Bytes)
                                hoist112
                              <:
                              Bertie.Tls13utils.t_Bytes)
                            b2
                          <:
                          Bertie.Tls13utils.t_Bytes)
                        hoist114
                      <:
                      Bertie.Tls13utils.t_Bytes)
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok hoist119 ->
              Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat b1 hoist119)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
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
        if (Bertie.Tls13utils.impl__Bytes__len cv <: usize) <>. sz 64
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
        Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist122 ->
        (match
            Bertie.Tls13utils.encode_length_u16 sv
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist121 ->
            let sig:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__concat hoist122 hoist121
            in
            Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
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

let encrypted_extensions (v__algs: Bertie.Tls13crypto.t_Algorithms) =
  let handshake_type:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.discriminant_HandshakeType_EncryptedExtensions +!
            0uy
            <:
            u8)
        <:
        u8)
  in
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__new ()
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist123 ->
    (match
        Bertie.Tls13utils.encode_length_u24 hoist123
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist125 ->
        Core.Result.Result_Ok
        (Bertie.Tls13formats.Handshake_data.HandshakeData
          (Bertie.Tls13utils.impl__Bytes__concat handshake_type hoist125)
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

let parse_ecdsa_signature (sig: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <. sz 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    match
      Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 48uy <: Bertie.Tls13utils.t_Bytes)
        (Bertie.Tls13utils.impl__Bytes__slice_range sig
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Bertie.Tls13utils.t_Bytes)
      <:
      Core.Result.t_Result Prims.unit u8
    with
    | Core.Result.Result_Ok _ ->
      (match
          Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range sig
                ({
                    Core.Ops.Range.f_start = sz 1;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
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
              Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy <: Bertie.Tls13utils.t_Bytes)
                (Bertie.Tls13utils.impl__Bytes__slice_range sig
                    ({ Core.Ops.Range.f_start = sz 2; Core.Ops.Range.f_end = sz 3 }
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
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sig <: usize
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
                        Bertie.Tls13utils.impl__Bytes__slice sig
                          ((sz 4 +! rlen <: usize) -! sz 32 <: usize)
                          (sz 32)
                      in
                      if
                        (Bertie.Tls13utils.impl__Bytes__len sig <: usize) <.
                        ((sz 6 +! rlen <: usize) +! sz 32 <: usize)
                      then
                        Core.Result.Result_Err Bertie.Tls13utils.v_INVALID_SIGNATURE
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      else
                        (match
                            Bertie.Tls13utils.check_eq (Bertie.Tls13utils.bytes1 2uy
                                <:
                                Bertie.Tls13utils.t_Bytes)
                              (Bertie.Tls13utils.impl__Bytes__slice_range sig
                                  ({
                                      Core.Ops.Range.f_start = sz 4 +! rlen <: usize;
                                      Core.Ops.Range.f_end = sz 5 +! rlen <: usize
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
                                Bertie.Tls13utils.check_length_encoding_u8 (Bertie.Tls13utils.impl__Bytes__slice_range
                                      sig
                                      ({
                                          Core.Ops.Range.f_start = sz 5 +! rlen <: usize;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl__Bytes__len sig <: usize
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
                                  Bertie.Tls13utils.impl__Bytes__slice sig
                                    ((Bertie.Tls13utils.impl__Bytes__len sig <: usize) -! sz 32
                                      <:
                                      usize)
                                    (sz 32)
                                in
                                Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__concat r s)
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

let parse_certificate_verify
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (certificate_verify: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message certificate_verify
      (Bertie.Tls13formats.Handshake_data.HandshakeType_CertificateVerify
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData cv) ->
    let sa:Bertie.Tls13crypto.t_SignatureScheme =
      Bertie.Tls13crypto.impl__Algorithms__signature algs
    in
    (match
        Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist128 ->
        (match
            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw hoist128
                <:
                t_Slice u8)
              (Bertie.Tls13utils.impl__Bytes__as_raw cv <: t_Slice u8)
              (sz 0)
              (sz 2)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            (match
                Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                      cv
                      ({
                          Core.Ops.Range.f_start = sz 2;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
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
                    parse_ecdsa_signature (Bertie.Tls13utils.impl__Bytes__slice_range cv
                          ({
                              Core.Ops.Range.f_start = sz 4;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        Bertie.Tls13utils.t_Bytes)
                  | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
                    Core.Result.Result_Ok
                    (Bertie.Tls13utils.impl__Bytes__slice_range cv
                        ({
                            Core.Ops.Range.f_start = sz 4;
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
                    if ((Bertie.Tls13utils.impl__Bytes__len cv <: usize) -! sz 4 <: usize) =. sz 64
                    then
                      Core.Result.Result_Ok
                      (Bertie.Tls13utils.impl__Bytes__slice_range cv
                          ({
                              Core.Ops.Range.f_start = sz 4;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len cv <: usize
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

let parse_encrypted_extensions
      (v__algs: Bertie.Tls13crypto.t_Algorithms)
      (encrypted_extensions: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  let Bertie.Tls13formats.Handshake_data.HandshakeData encrypted_extension_bytes:Bertie.Tls13formats.Handshake_data.t_HandshakeData
  =
    encrypted_extensions
  in
  let expected_handshake_type:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (Bertie.Tls13formats.Handshake_data.discriminant_HandshakeType_EncryptedExtensions +!
            0uy
            <:
            u8)
        <:
        u8)
  in
  match
    Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw expected_handshake_type

        <:
        t_Slice u8)
      (Bertie.Tls13utils.impl__Bytes__as_raw encrypted_extension_bytes <: t_Slice u8)
      (sz 0)
      (sz 1)
    <:
    Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl__Bytes__raw_slice encrypted_extension_bytes
          ({
              Core.Ops.Range.f_start = sz 1;
              Core.Ops.Range.f_end
              =
              Bertie.Tls13utils.impl__Bytes__len encrypted_extension_bytes <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        t_Slice u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let parse_finished (finished: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  match
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message finished
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

let parse_server_certificate (certificate: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  match
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message certificate
      (Bertie.Tls13formats.Handshake_data.HandshakeType_Certificate
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData sc) ->
    let next:usize = sz 0 in
    (match
        Bertie.Tls13utils.length_u8_encoded (sc.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
        <:
        Core.Result.t_Result usize u8
      with
      | Core.Result.Result_Ok creqlen ->
        let next:usize = (next +! sz 1 <: usize) +! creqlen in
        (match
            Bertie.Tls13utils.check_length_encoding_u24 (Bertie.Tls13utils.impl__Bytes__raw_slice sc
                  ({
                      Core.Ops.Range.f_start = next;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let next:usize = next +! sz 3 in
            (match
                Bertie.Tls13utils.length_u24_encoded (Bertie.Tls13utils.impl__Bytes__raw_slice sc
                      ({
                          Core.Ops.Range.f_start = next;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize)
                    <:
                    t_Slice u8)
                <:
                Core.Result.t_Result usize u8
              with
              | Core.Result.Result_Ok crtlen ->
                let next:usize = next +! sz 3 in
                let crt:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl__Bytes__slice_range sc
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
                            Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len sc <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result usize u8
                  with
                  | Core.Result.Result_Ok v__extlen ->
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

let check_handshake_record (p: Bertie.Tls13utils.t_Bytes) =
  if (Bertie.Tls13utils.impl__Bytes__len p <: usize) <. sz 5
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (Bertie.Tls13formats.Handshake_data.t_HandshakeData & usize) u8
  else
    let ty:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.bytes1 (cast (discriminant_ContentType_Handshake +! 0uy <: u8) <: u8)
    in
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
    match
      Bertie.Tls13utils.check_eq ty
        (Bertie.Tls13utils.impl__Bytes__slice_range p
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 1 }
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
            (Bertie.Tls13utils.impl__Bytes__slice_range p
                ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 3 }
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
                      Core.Ops.Range.f_start = sz 3;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
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
                  (Bertie.Tls13utils.impl__Bytes__slice_range p
                      ({
                          Core.Ops.Range.f_start = sz 5;
                          Core.Ops.Range.f_end = sz 5 +! len <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize))
                  <:
                  Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                sz 5 +! len
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
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
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
                    (Bertie.Tls13utils.impl__Bytes__slice_range p
                        ({
                            Core.Ops.Range.f_start = sz 5;
                            Core.Ops.Range.f_end = sz 5 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                  sz 5 +! len
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
              (Bertie.Tls13utils.impl__Bytes__slice_range p
                  ({ Core.Ops.Range.f_start = sz 1; Core.Ops.Range.f_end = sz 3 }
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
                        Core.Ops.Range.f_start = sz 3;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
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
                    (Bertie.Tls13utils.impl__Bytes__slice_range p
                        ({
                            Core.Ops.Range.f_start = sz 5;
                            Core.Ops.Range.f_end = sz 5 +! len <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize))
                    <:
                    Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                  sz 5 +! len
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
                          Core.Ops.Range.f_start = sz 3;
                          Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len p <: usize
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
                      (Bertie.Tls13utils.impl__Bytes__slice_range p
                          ({
                              Core.Ops.Range.f_start = sz 5;
                              Core.Ops.Range.f_end = sz 5 +! len <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize))
                      <:
                      Bertie.Tls13formats.Handshake_data.t_HandshakeData),
                    sz 5 +! len
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
    if len =. (Bertie.Tls13utils.impl__Bytes__len p <: usize)
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

let handshake_record (p: Bertie.Tls13formats.Handshake_data.t_HandshakeData) =
  let ty:Bertie.Tls13utils.t_Bytes =
    Bertie.Tls13utils.bytes1 (cast (discriminant_ContentType_Handshake +! 0uy <: u8) <: u8)
  in
  let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
  match
    Bertie.Tls13utils.encode_length_u16 p.Bertie.Tls13formats.Handshake_data._0
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist132 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat ty ver
          <:
          Bertie.Tls13utils.t_Bytes)
        hoist132)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
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
  | Core.Result.Result_Ok hoist134 ->
    (match
        Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__concat_array (sz 4)
              hoist134
              (Bertie.Tls13utils.u32_as_be_bytes (Bertie.Tls13utils.v_U32 4294967295ul <: u32)
                <:
                t_Array u8 (sz 4))
            <:
            Bertie.Tls13utils.t_Bytes)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok identities ->
        (match
            Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw (Bertie.Tls13crypto.zero_key
                      (Bertie.Tls13crypto.impl__Algorithms__hash algs
                        <:
                        Bertie.Tls13crypto.t_HashAlgorithm)
                    <:
                    Bertie.Tls13utils.t_Bytes)
                <:
                t_Slice u8)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist137 ->
            (match
                Bertie.Tls13utils.encode_length_u16 hoist137
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
              with
              | Core.Result.Result_Ok binders ->
                let binders_len:usize = Bertie.Tls13utils.impl__Bytes__len binders in
                (match
                    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.impl__Bytes__concat identities
                          binders
                        <:
                        Bertie.Tls13utils.t_Bytes)
                    <:
                    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok hoist139 ->
                    let ext:Bertie.Tls13utils.t_Bytes =
                      Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
                          <:
                          Bertie.Tls13utils.t_Bytes)
                        hoist139
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
          Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.impl__Bytes__concat extensions
                pskm
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

let server_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (gx: Bertie.Tls13utils.t_Bytes) =
  match
    Bertie.Tls13crypto.impl__Algorithms__supported_group algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist141 ->
    (match
        Bertie.Tls13utils.encode_length_u16 gx <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist140 ->
        let ks:Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__concat hoist141 hoist140
        in
        (match
            Bertie.Tls13utils.encode_length_u16 ks
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist142 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 51uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
                hoist142)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let server_pre_shared_key (v__algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 0uy 0uy
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist144 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 41uy
          <:
          Bertie.Tls13utils.t_Bytes)
        hoist144)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let server_supported_version (v__algorithms: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13utils.encode_length_u16 (Bertie.Tls13utils.bytes2 3uy 4uy
        <:
        Bertie.Tls13utils.t_Bytes)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist146 ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl__Bytes__prefix hoist146
        (server_supported_version__SUPPORTED_VERSION_PREFIX <: t_Slice u8))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let server_hello (algs: Bertie.Tls13crypto.t_Algorithms) (sr sid gy: Bertie.Tls13utils.t_Bytes) =
  let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
  match
    Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl__Bytes__as_raw sid <: t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok sid ->
    (match
        Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok cip ->
        let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
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
                let exts:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__concat ks sv in
                if Bertie.Tls13crypto.impl__Algorithms__psk_mode algs
                then
                  match
                    server_pre_shared_key algs <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                  with
                  | Core.Result.Result_Ok hoist148 ->
                    let exts:Bertie.Tls13utils.t_Bytes =
                      Bertie.Tls13utils.impl__Bytes__concat exts hoist148
                    in
                    (match
                        Bertie.Tls13utils.encode_length_u16 exts
                        <:
                        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
                      with
                      | Core.Result.Result_Ok encoded_extensions ->
                        let len:usize =
                          (Bertie.Tls13utils.impl__Bytes__len ver <: usize) +!
                          (Bertie.Tls13utils.impl__Bytes__len sr <: usize)
                        in
                        let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len sid <: usize) in
                        let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len cip <: usize) in
                        let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len comp <: usize) in
                        let len:usize =
                          len +! (Bertie.Tls13utils.impl__Bytes__len encoded_extensions <: usize)
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__new_alloc len
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out ver
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out sr
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out sid
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out cip
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out comp
                        in
                        let out:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl__Bytes__append out encoded_extensions
                        in
                        (match
                            Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
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
                        (Bertie.Tls13utils.impl__Bytes__len ver <: usize) +!
                        (Bertie.Tls13utils.impl__Bytes__len sr <: usize)
                      in
                      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len sid <: usize) in
                      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len cip <: usize) in
                      let len:usize = len +! (Bertie.Tls13utils.impl__Bytes__len comp <: usize) in
                      let len:usize =
                        len +! (Bertie.Tls13utils.impl__Bytes__len encoded_extensions <: usize)
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__new_alloc len
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out ver
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out sr
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out sid
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out cip
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out comp
                      in
                      let out:Bertie.Tls13utils.t_Bytes =
                        Bertie.Tls13utils.impl__Bytes__append out encoded_extensions
                      in
                      (match
                          Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
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

let signature_algorithms (algs: Bertie.Tls13crypto.t_Algorithms) =
  match
    Bertie.Tls13crypto.impl__Algorithms__signature_algorithm algs
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist152 ->
    (match
        Bertie.Tls13utils.encode_length_u16 hoist152
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist154 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist154
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok hoist156 ->
            Core.Result.Result_Ok
            (Bertie.Tls13utils.impl__Bytes__concat (Bertie.Tls13utils.bytes2 0uy 13uy
                  <:
                  Bertie.Tls13utils.t_Bytes)
                hoist156)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let client_hello
      (algorithms: Bertie.Tls13crypto.t_Algorithms)
      (client_random kem_pk server_name: Bertie.Tls13utils.t_Bytes)
      (session_ticket: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
     =
  let version:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
  let compression_methods:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
  match
    Bertie.Tls13utils.encode_length_u8 (Rust_primitives.Hax.repeat (Bertie.Tls13utils.v_U8 0uy <: u8
          )
          (sz 32)
        <:
        t_Slice u8)
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok legacy_session_id ->
    (match
        Bertie.Tls13crypto.impl__Algorithms__ciphersuite algorithms
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist158 ->
        (match
            Bertie.Tls13utils.encode_length_u16 hoist158
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
                                  (Bertie.Tls13utils.impl__Bytes__len server_name <: usize) +!
                                  (Bertie.Tls13utils.impl__Bytes__len supported_versions <: usize)
                                in
                                let len:usize =
                                  len +!
                                  (Bertie.Tls13utils.impl__Bytes__len supported_groups <: usize)
                                in
                                let len:usize =
                                  len +!
                                  (Bertie.Tls13utils.impl__Bytes__len signature_algorithms <: usize)
                                in
                                let len:usize =
                                  len +! (Bertie.Tls13utils.impl__Bytes__len key_shares <: usize)
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__new_alloc len
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__append out server_name
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__append out supported_versions
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__append out supported_groups
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__append out signature_algorithms
                                in
                                let out:Bertie.Tls13utils.t_Bytes =
                                  Bertie.Tls13utils.impl__Bytes__append out key_shares
                                in
                                let extensions:Bertie.Tls13utils.t_Bytes = out in
                                (match
                                    (match
                                        Bertie.Tls13crypto.impl__Algorithms__psk_mode algorithms,
                                        session_ticket
                                        <:
                                        (bool & Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
                                      with
                                      | true, Core.Option.Option_Some session_ticket ->
                                        get_psk_extensions algorithms session_ticket extensions
                                      | false, Core.Option.Option_None  ->
                                        Core.Result.Result_Ok
                                        (sz 0, extensions <: (usize & Bertie.Tls13utils.t_Bytes))
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
                                          (Bertie.Tls13utils.impl__Bytes__len version <: usize) +!
                                          (Bertie.Tls13utils.impl__Bytes__len client_random <: usize
                                          )
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl__Bytes__len legacy_session_id
                                            <:
                                            usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl__Bytes__len cipher_suites <: usize
                                          )
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl__Bytes__len compression_methods
                                            <:
                                            usize)
                                        in
                                        let len:usize =
                                          len +!
                                          (Bertie.Tls13utils.impl__Bytes__len encoded_extensions
                                            <:
                                            usize)
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__new_alloc len
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out version
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out client_random
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out
                                            legacy_session_id
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out cipher_suites
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out
                                            compression_methods
                                        in
                                        let out:Bertie.Tls13utils.t_Bytes =
                                          Bertie.Tls13utils.impl__Bytes__append out
                                            encoded_extensions
                                        in
                                        let handshake_bytes:Bertie.Tls13utils.t_Bytes = out in
                                        (match
                                            Bertie.Tls13formats.Handshake_data.impl__HandshakeData__from_bytes
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

let rec find_key_share (g: Bertie.Tls13utils.t_Bytes) (ch: t_Slice u8) =
  if (Core.Slice.impl__len #u8 ch <: usize) <. sz 4
  then Bertie.Tls13utils.tlserr #Bertie.Tls13utils.t_Bytes (Bertie.Tls13utils.parse_failed () <: u8)
  else
    if
      Bertie.Tls13utils.eq_slice (Bertie.Tls13utils.impl__Bytes__as_raw g <: t_Slice u8)
        (ch.[ { Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 2 }
            <:
            Core.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
    then
      match
        Bertie.Tls13utils.length_u16_encoded_slice (ch.[ {
                Core.Ops.Range.f_start = sz 2;
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
            (ch.[ { Core.Ops.Range.f_start = sz 4; Core.Ops.Range.f_end = sz 4 +! len <: usize }
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
                Core.Ops.Range.f_start = sz 2;
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
                Core.Ops.Range.f_start = sz 4 +! len <: usize;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 ch <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let check_key_shares (algs: Bertie.Tls13crypto.t_Algorithms) (ch: t_Slice u8) =
  match
    Bertie.Tls13utils.check_length_encoding_u16_slice ch <: Core.Result.t_Result Prims.unit u8
  with
  | Core.Result.Result_Ok _ ->
    (match
        Bertie.Tls13crypto.impl__Algorithms__supported_group algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok hoist163 ->
        find_key_share hoist163
          (ch.[ {
                Core.Ops.Range.f_start = sz 2;
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
  if (Core.Slice.impl__len #u8 bytes <: usize) <. sz 4
  then
    Core.Result.Result_Err (Bertie.Tls13utils.parse_failed ())
    <:
    Core.Result.t_Result (usize & t_Extensions) u8
  else
    let l0:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ sz 0 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    let l1:usize =
      cast (Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (bytes.[ sz 1 ] <: u8)
          <:
          u8)
      <:
      usize
    in
    match
      Bertie.Tls13utils.length_u16_encoded_slice (bytes.[ {
              Core.Ops.Range.f_start = sz 2;
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
        | 0uy, 0uy ->
          (match
              check_server_name (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
            with
            | Core.Result.Result_Ok hoist164 ->
              Core.Result.Result_Ok
              (sz 4 +! len,
                ({
                    f_sni
                    =
                    Core.Option.Option_Some hoist164
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
        | 0uy, 45uy ->
          (match
              check_psk_key_exchange_modes (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | 0uy, 43uy ->
          (match
              check_supported_versions (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | 0uy, 10uy ->
          (match
              check_supported_groups algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | 0uy, 13uy ->
          (match
              check_signature_algorithms algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | 0uy, 51uy ->
          (match
              check_key_shares algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
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
              (sz 4 +! len,
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
        | 0uy, 41uy ->
          (match
              check_psk_shared_key algs
                (bytes.[ {
                      Core.Ops.Range.f_start = sz 4;
                      Core.Ops.Range.f_end = sz 4 +! len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              Core.Result.t_Result Prims.unit u8
            with
            | Core.Result.Result_Ok _ ->
              Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
              <:
              Core.Result.t_Result (usize & t_Extensions) u8
            | Core.Result.Result_Err err ->
              Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8)
        | _ ->
          Core.Result.Result_Ok (sz 4 +! len, out <: (usize & t_Extensions))
          <:
          Core.Result.t_Result (usize & t_Extensions) u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & t_Extensions) u8

let parse_server_hello
      (algs: Bertie.Tls13crypto.t_Algorithms)
      (server_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message server_hello
      (Bertie.Tls13formats.Handshake_data.HandshakeType_ServerHello
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData server_hello) ->
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
    (match
        Bertie.Tls13crypto.impl__Algorithms__ciphersuite algs
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok cip ->
        let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes1 0uy in
        let next:usize = sz 0 in
        (match
            (match
                Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw ver
                    <:
                    t_Slice u8)
                  (Bertie.Tls13utils.impl__Bytes__as_raw server_hello <: t_Slice u8)
                  next
                  (next +! sz 2 <: usize)
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
            let next:usize = next +! sz 2 in
            (match
                Bertie.Tls13utils.check ((Bertie.Tls13utils.impl__Bytes__len server_hello <: usize) >=.
                    (next +! sz 32 <: usize)
                    <:
                    bool)
                <:
                Core.Result.t_Result Prims.unit u8
              with
              | Core.Result.Result_Ok _ ->
                let srand:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl__Bytes__slice_range server_hello
                    ({
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = next +! sz 32 <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                in
                let next:usize = next +! sz 32 in
                (match
                    Bertie.Tls13utils.length_u8_encoded (server_hello.[ {
                            Core.Ops.Range.f_start = next;
                            Core.Ops.Range.f_end
                            =
                            Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result usize u8
                  with
                  | Core.Result.Result_Ok sidlen ->
                    let next:usize = (next +! sz 1 <: usize) +! sidlen in
                    (match
                        (match
                            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw
                                  cip
                                <:
                                t_Slice u8)
                              (Bertie.Tls13utils.impl__Bytes__as_raw server_hello <: t_Slice u8)
                              next
                              (next +! sz 2 <: usize)
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
                        let next:usize = next +! sz 2 in
                        (match
                            (match
                                Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw
                                      comp
                                    <:
                                    t_Slice u8)
                                  (Bertie.Tls13utils.impl__Bytes__as_raw server_hello <: t_Slice u8)
                                  next
                                  (next +! sz 1 <: usize)
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
                            let next:usize = next +! sz 1 in
                            (match
                                Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                                      server_hello
                                      ({
                                          Core.Ops.Range.f_start = next;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
                                        }
                                        <:
                                        Core.Ops.Range.t_Range usize)
                                    <:
                                    Bertie.Tls13utils.t_Bytes)
                                <:
                                Core.Result.t_Result Prims.unit u8
                              with
                              | Core.Result.Result_Ok _ ->
                                let next:usize = next +! sz 2 in
                                (match
                                    check_server_extensions algs
                                      (server_hello.[ {
                                            Core.Ops.Range.f_start = next;
                                            Core.Ops.Range.f_end
                                            =
                                            Bertie.Tls13utils.impl__Bytes__len server_hello <: usize
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
        | Core.Result.Result_Ok out_rest -> impl__Extensions__merge out out_rest
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8

let check_extensions (algs: Bertie.Tls13crypto.t_Algorithms) (b: Bertie.Tls13utils.t_Bytes) =
  match
    check_extension algs (Bertie.Tls13utils.impl__Bytes__as_raw b <: t_Slice u8)
    <:
    Core.Result.t_Result (usize & t_Extensions) u8
  with
  | Core.Result.Result_Ok (len, out) ->
    if len =. (Bertie.Tls13utils.impl__Bytes__len b <: usize)
    then Core.Result.Result_Ok out <: Core.Result.t_Result t_Extensions u8
    else
      (match
          check_extensions_slice algs
            (Bertie.Tls13utils.impl__Bytes__raw_slice b
                ({
                    Core.Ops.Range.f_start = len;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len b <: usize
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result t_Extensions u8
        with
        | Core.Result.Result_Ok out_rest -> impl__Extensions__merge out out_rest
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_Extensions u8

let parse_client_hello
      (ciphersuite: Bertie.Tls13crypto.t_Algorithms)
      (client_hello: Bertie.Tls13formats.Handshake_data.t_HandshakeData)
     =
  match
    Bertie.Tls13formats.Handshake_data.impl__HandshakeData__as_handshake_message client_hello
      (Bertie.Tls13formats.Handshake_data.HandshakeType_ClientHello
        <:
        Bertie.Tls13formats.Handshake_data.t_HandshakeType)
    <:
    Core.Result.t_Result Bertie.Tls13formats.Handshake_data.t_HandshakeData u8
  with
  | Core.Result.Result_Ok (Bertie.Tls13formats.Handshake_data.HandshakeData ch) ->
    let ver:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 3uy 3uy in
    let comp:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.bytes2 1uy 0uy in
    let next:usize = sz 0 in
    (match
        Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw ver
            <:
            t_Slice u8)
          (Bertie.Tls13utils.impl__Bytes__as_raw ch <: t_Slice u8)
          next
          (next +! sz 2 <: usize)
        <:
        Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        let next:usize = next +! sz 2 in
        (match
            Bertie.Tls13utils.check ((Bertie.Tls13utils.impl__Bytes__len ch <: usize) >=.
                (next +! sz 32 <: usize)
                <:
                bool)
            <:
            Core.Result.t_Result Prims.unit u8
          with
          | Core.Result.Result_Ok _ ->
            let crand:Bertie.Tls13utils.t_Bytes =
              Bertie.Tls13utils.impl__Bytes__slice_range ch
                ({ Core.Ops.Range.f_start = next; Core.Ops.Range.f_end = next +! sz 32 <: usize }
                  <:
                  Core.Ops.Range.t_Range usize)
            in
            let next:usize = next +! sz 32 in
            (match
                Bertie.Tls13utils.length_u8_encoded (ch.[ {
                        Core.Ops.Range.f_start = next;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
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
                  Bertie.Tls13utils.impl__Bytes__slice_range ch
                    ({
                        Core.Ops.Range.f_start = next +! sz 1 <: usize;
                        Core.Ops.Range.f_end = (next +! sz 1 <: usize) +! sidlen <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                in
                let next:usize = (next +! sz 1 <: usize) +! sidlen in
                (match
                    Bertie.Tls13crypto.impl__Algorithms__check ciphersuite
                      (Bertie.Tls13utils.impl__Bytes__raw_slice ch
                          ({
                              Core.Ops.Range.f_start = next;
                              Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ch <: usize
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
                            Bertie.Tls13utils.check_eq_with_slice (Bertie.Tls13utils.impl__Bytes__as_raw
                                  comp
                                <:
                                t_Slice u8)
                              (Bertie.Tls13utils.impl__Bytes__as_raw ch <: t_Slice u8)
                              next
                              (next +! sz 2 <: usize)
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
                        let next:usize = next +! sz 2 in
                        (match
                            Bertie.Tls13utils.check_length_encoding_u16 (Bertie.Tls13utils.impl__Bytes__slice_range
                                  ch
                                  ({
                                      Core.Ops.Range.f_start = next;
                                      Core.Ops.Range.f_end
                                      =
                                      Bertie.Tls13utils.impl__Bytes__len ch <: usize
                                    }
                                    <:
                                    Core.Ops.Range.t_Range usize)
                                <:
                                Bertie.Tls13utils.t_Bytes)
                            <:
                            Core.Result.t_Result Prims.unit u8
                          with
                          | Core.Result.Result_Ok _ ->
                            let next:usize = next +! sz 2 in
                            (match
                                check_extensions ciphersuite
                                  (Bertie.Tls13utils.impl__Bytes__slice_range ch
                                      ({
                                          Core.Ops.Range.f_start = next;
                                          Core.Ops.Range.f_end
                                          =
                                          Bertie.Tls13utils.impl__Bytes__len ch <: usize
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
                                  ((Bertie.Tls13utils.impl__Bytes__len ch <: usize) -!
                                    (Bertie.Tls13crypto.impl__HashAlgorithm__hash_len (Bertie.Tls13crypto.impl__Algorithms__hash
                                            ciphersuite
                                          <:
                                          Bertie.Tls13crypto.t_HashAlgorithm)
                                      <:
                                      usize)
                                    <:
                                    usize) -!
                                  sz 3
                                in
                                (match
                                    Bertie.Tls13crypto.impl__Algorithms__psk_mode ciphersuite, exts
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
                                      Bertie.Tls13utils.impl__Bytes__new (),
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
                                      sz 0
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
                                      Bertie.Tls13utils.impl__Bytes__new (),
                                      gx,
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      (Core.Option.Option_None
                                        <:
                                        Core.Option.t_Option Bertie.Tls13utils.t_Bytes),
                                      sz 0
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
