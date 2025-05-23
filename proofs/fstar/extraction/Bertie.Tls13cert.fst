module Bertie.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13utils in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Clone.t_Clone t_CertificateKey

let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_CertificateKey

let impl_1 = impl_1'

let asn1_error (#v_T: Type0) (err: u8) = Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

let long_length (b: Bertie.Tls13utils.t_Bytes) (offset len: usize) =
  if len >. mk_usize 4
  then asn1_error #usize v_ASN1_SEQUENCE_TOO_LONG
  else
    let u32word:t_Array u8 (mk_usize 4) =
      Rust_primitives.Hax.repeat (Bertie.Tls13utils.v_U8 (mk_u8 0) <: u8) (mk_usize 4)
    in
    let u32word:t_Array u8 (mk_usize 4) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range u32word
        ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = len }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice #u8
            (u32word.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = len }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
            (b.[ { Core.Ops.Range.f_start = offset; Core.Ops.Range.f_end = offset +! len <: usize }
                <:
                Core.Ops.Range.t_Range usize ]
              <:
              t_Slice u8)
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    ((cast (Bertie.Tls13utils.f_declassify #u32
              #u32
              #FStar.Tactics.Typeclasses.solve
              (Bertie.Tls13utils.u32_from_be_bytes u32word <: u32)
            <:
            u32)
        <:
        usize) >>!
      ((mk_usize 4 -! len <: usize) *! mk_usize 8 <: usize))
    <:
    Core.Result.t_Result usize u8

let length_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  if
    ((Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (b.[ offset ] <: u8)
        <:
        u8) >>!
      mk_i32 7
      <:
      u8) =.
    mk_u8 1
  then
    cast ((Bertie.Tls13utils.f_declassify #u8
            #u8
            #FStar.Tactics.Typeclasses.solve
            (b.[ offset ] <: u8)
          <:
          u8) &.
        mk_u8 127
        <:
        u8)
    <:
    usize
  else mk_usize 0

let short_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  if
    ((Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (b.[ offset ] <: u8)
        <:
        u8) &.
      mk_u8 128
      <:
      u8) =.
    mk_u8 0
  then
    Core.Result.Result_Ok
    (cast ((Bertie.Tls13utils.f_declassify #u8
              #u8
              #FStar.Tactics.Typeclasses.solve
              (b.[ offset ] <: u8)
            <:
            u8) &.
          mk_u8 127
          <:
          u8)
      <:
      usize)
    <:
    Core.Result.t_Result usize u8
  else asn1_error #usize v_ASN1_ERROR

let length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  if
    ((Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (b.[ offset ] <: u8)
        <:
        u8) &.
      mk_u8 128
      <:
      u8) =.
    mk_u8 0
  then
    match short_length b offset <: Core.Result.t_Result usize u8 with
    | Core.Result.Result_Ok len ->
      Core.Result.Result_Ok (offset +! mk_usize 1, len <: (usize & usize))
      <:
      Core.Result.t_Result (usize & usize) u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & usize) u8
  else
    let len:usize = length_length b offset in
    let offset:usize = offset +! mk_usize 1 in
    match long_length b offset len <: Core.Result.t_Result usize u8 with
    | Core.Result.Result_Ok v_end ->
      Core.Result.Result_Ok (offset +! len, v_end <: (usize & usize))
      <:
      Core.Result.t_Result (usize & usize) u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & usize) u8

let check_tag (b: Bertie.Tls13utils.t_Bytes) (offset: usize) (value: u8) =
  if
    (Bertie.Tls13utils.f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (b.[ offset ] <: u8)
      <:
      u8) =.
    value
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error #Prims.unit v_ASN1_INVALID_TAG

let read_sequence_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 48) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    let length_length:usize = length_length b offset in
    let offset:usize = (offset +! length_length <: usize) +! mk_usize 1 in
    Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let read_octet_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 4) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    let length_length:usize = length_length b offset in
    let offset:usize = (offset +! length_length <: usize) +! mk_usize 1 in
    Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let skip_sequence (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 48) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match length b offset <: Core.Result.t_Result (usize & usize) u8 with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let read_version_number (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 160) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match short_length b offset <: Core.Result.t_Result usize u8 with
      | Core.Result.Result_Ok length ->
        Core.Result.Result_Ok ((offset +! mk_usize 1 <: usize) +! length)
        <:
        Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err _ -> Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8

let skip_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 2) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match length b offset <: Core.Result.t_Result (usize & usize) u8 with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let read_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset (mk_u8 2) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match length b offset <: Core.Result.t_Result (usize & usize) u8 with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (Bertie.Tls13utils.impl_Bytes__slice b offset length)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let x962_ec_public_key_oid (_: Prims.unit) =
  Core.Convert.f_into #(t_Array u8 (mk_usize 7))
    #Bertie.Tls13utils.t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (let list = [mk_u8 42; mk_u8 134; mk_u8 72; mk_u8 206; mk_u8 61; mk_u8 2; mk_u8 1] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
      Rust_primitives.Hax.array_of_list 7 list)

let ecdsa_secp256r1_sha256_oid (_: Prims.unit) =
  Core.Convert.f_into #(t_Array u8 (mk_usize 8))
    #Bertie.Tls13utils.t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (let list = [mk_u8 42; mk_u8 134; mk_u8 72; mk_u8 206; mk_u8 61; mk_u8 3; mk_u8 1; mk_u8 7] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list 8 list)

let rsa_pkcs1_encryption_oid (_: Prims.unit) =
  Core.Convert.f_into #(t_Array u8 (mk_usize 9))
    #Bertie.Tls13utils.t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (let list =
        [mk_u8 42; mk_u8 134; mk_u8 72; mk_u8 134; mk_u8 247; mk_u8 13; mk_u8 1; mk_u8 1; mk_u8 1]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
      Rust_primitives.Hax.array_of_list 9 list)

let check_success (v_val: bool) =
  if v_val
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error #Prims.unit v_ASN1_ERROR

let read_spki (cert: Bertie.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag cert offset (mk_u8 48) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match length cert offset <: Core.Result.t_Result (usize & usize) u8 with
      | Core.Result.Result_Ok (offset, e_seq_len) ->
        (match check_tag cert offset (mk_u8 48) <: Core.Result.t_Result Prims.unit u8 with
          | Core.Result.Result_Ok _ ->
            let offset:usize = offset +! mk_usize 1 in
            (match length cert offset <: Core.Result.t_Result (usize & usize) u8 with
              | Core.Result.Result_Ok (offset, seq_len) ->
                (match check_tag cert offset (mk_u8 6) <: Core.Result.t_Result Prims.unit u8 with
                  | Core.Result.Result_Ok _ ->
                    (match
                        length cert (offset +! mk_usize 1 <: usize)
                        <:
                        Core.Result.t_Result (usize & usize) u8
                      with
                      | Core.Result.Result_Ok (oid_offset, oid_len) ->
                        let ec_pk_oid, ecdsa_p256, rsa_pk_oid:(bool & bool & bool) =
                          false, false, false <: (bool & bool & bool)
                        in
                        let ec_oid:Bertie.Tls13utils.t_Bytes = x962_ec_public_key_oid () in
                        let rsa_oid:Bertie.Tls13utils.t_Bytes = rsa_pkcs1_encryption_oid () in
                        if (Bertie.Tls13utils.impl_Bytes__len ec_oid <: usize) =. oid_len
                        then
                          let ec_pk_oid:bool = true in
                          let ec_pk_oid:bool =
                            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                              (Bertie.Tls13utils.impl_Bytes__len ec_oid <: usize)
                              (fun ec_pk_oid temp_1_ ->
                                  let ec_pk_oid:bool = ec_pk_oid in
                                  let _:usize = temp_1_ in
                                  true)
                              ec_pk_oid
                              (fun ec_pk_oid i ->
                                  let ec_pk_oid:bool = ec_pk_oid in
                                  let i:usize = i in
                                  let oid_byte_equal:bool =
                                    (Bertie.Tls13utils.f_declassify #u8
                                        #u8
                                        #FStar.Tactics.Typeclasses.solve
                                        (cert.[ oid_offset +! i <: usize ] <: u8)
                                      <:
                                      u8) =.
                                    (Bertie.Tls13utils.f_declassify #u8
                                        #u8
                                        #FStar.Tactics.Typeclasses.solve
                                        (ec_oid.[ i ] <: u8)
                                      <:
                                      u8)
                                  in
                                  let ec_pk_oid:bool = ec_pk_oid && oid_byte_equal in
                                  ec_pk_oid)
                          in
                          if ec_pk_oid
                          then
                            let oid_offset:usize = oid_offset +! oid_len in
                            match
                              check_tag cert oid_offset (mk_u8 6)
                              <:
                              Core.Result.t_Result Prims.unit u8
                            with
                            | Core.Result.Result_Ok _ ->
                              let oid_offset:usize = oid_offset +! mk_usize 1 in
                              (match
                                  length cert oid_offset <: Core.Result.t_Result (usize & usize) u8
                                with
                                | Core.Result.Result_Ok (oid_offset, e_oid_len) ->
                                  let ecdsa_p256:bool = true in
                                  let ec_oid:Bertie.Tls13utils.t_Bytes =
                                    ecdsa_secp256r1_sha256_oid ()
                                  in
                                  let ecdsa_p256:bool =
                                    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                                      (Bertie.Tls13utils.impl_Bytes__len ec_oid <: usize)
                                      (fun ecdsa_p256 temp_1_ ->
                                          let ecdsa_p256:bool = ecdsa_p256 in
                                          let _:usize = temp_1_ in
                                          true)
                                      ecdsa_p256
                                      (fun ecdsa_p256 i ->
                                          let ecdsa_p256:bool = ecdsa_p256 in
                                          let i:usize = i in
                                          let oid_byte_equal:bool =
                                            (Bertie.Tls13utils.f_declassify #u8
                                                #u8
                                                #FStar.Tactics.Typeclasses.solve
                                                (cert.[ oid_offset +! i <: usize ] <: u8)
                                              <:
                                              u8) =.
                                            (Bertie.Tls13utils.f_declassify #u8
                                                #u8
                                                #FStar.Tactics.Typeclasses.solve
                                                (ec_oid.[ i ] <: u8)
                                              <:
                                              u8)
                                          in
                                          let ecdsa_p256:bool = ecdsa_p256 && oid_byte_equal in
                                          ecdsa_p256)
                                  in
                                  (match
                                      check_success ecdsa_p256 <: Core.Result.t_Result Prims.unit u8
                                    with
                                    | Core.Result.Result_Ok _ ->
                                      let ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
                                        ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize)
                                      in
                                      let rsa_pk_oid:bool =
                                        if
                                          (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize) =.
                                          oid_len
                                        then
                                          let rsa_pk_oid:bool = true in
                                          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                                            (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize)
                                            (fun rsa_pk_oid temp_1_ ->
                                                let rsa_pk_oid:bool = rsa_pk_oid in
                                                let _:usize = temp_1_ in
                                                true)
                                            rsa_pk_oid
                                            (fun rsa_pk_oid i ->
                                                let rsa_pk_oid:bool = rsa_pk_oid in
                                                let i:usize = i in
                                                let oid_byte_equal:bool =
                                                  (Bertie.Tls13utils.f_declassify #u8
                                                      #u8
                                                      #FStar.Tactics.Typeclasses.solve
                                                      (cert.[ oid_offset +! i <: usize ] <: u8)
                                                    <:
                                                    u8) =.
                                                  (Bertie.Tls13utils.f_declassify #u8
                                                      #u8
                                                      #FStar.Tactics.Typeclasses.solve
                                                      (rsa_oid.[ i ] <: u8)
                                                    <:
                                                    u8)
                                                in
                                                let rsa_pk_oid:bool =
                                                  rsa_pk_oid && oid_byte_equal
                                                in
                                                rsa_pk_oid)
                                        else rsa_pk_oid
                                      in
                                      (match
                                          check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid)
                                          <:
                                          Core.Result.t_Result Prims.unit u8
                                        with
                                        | Core.Result.Result_Ok _ ->
                                          let offset:usize = offset +! seq_len in
                                          (match
                                              check_tag cert offset (mk_u8 3)
                                              <:
                                              Core.Result.t_Result Prims.unit u8
                                            with
                                            | Core.Result.Result_Ok _ ->
                                              let offset:usize = offset +! mk_usize 1 in
                                              (match
                                                  length cert offset
                                                  <:
                                                  Core.Result.t_Result (usize & usize) u8
                                                with
                                                | Core.Result.Result_Ok (offset, bit_string_len) ->
                                                  let offset:usize =
                                                    if
                                                      (Bertie.Tls13utils.f_declassify #u8
                                                          #u8
                                                          #FStar.Tactics.Typeclasses.solve
                                                          (cert.[ offset ] <: u8)
                                                        <:
                                                        u8) =.
                                                      mk_u8 0
                                                    then
                                                      let offset:usize = offset +! mk_usize 1 in
                                                      offset
                                                    else offset
                                                  in
                                                  if ec_pk_oid && ecdsa_p256
                                                  then
                                                    Core.Result.Result_Ok
                                                    ((Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256
                                                        <:
                                                        Bertie.Tls13crypto.t_SignatureScheme),
                                                      (CertificateKey offset
                                                          (bit_string_len -! mk_usize 1)
                                                        <:
                                                        t_CertificateKey)
                                                      <:
                                                      (Bertie.Tls13crypto.t_SignatureScheme &
                                                        t_CertificateKey))
                                                    <:
                                                    Core.Result.t_Result
                                                      (Bertie.Tls13crypto.t_SignatureScheme &
                                                        t_CertificateKey) u8
                                                  else
                                                    if rsa_pk_oid
                                                    then
                                                      Core.Result.Result_Ok
                                                      ((Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256
                                                          <:
                                                          Bertie.Tls13crypto.t_SignatureScheme),
                                                        (CertificateKey offset
                                                            (bit_string_len -! mk_usize 1)
                                                          <:
                                                          t_CertificateKey)
                                                        <:
                                                        (Bertie.Tls13crypto.t_SignatureScheme &
                                                          t_CertificateKey))
                                                      <:
                                                      Core.Result.t_Result
                                                        (Bertie.Tls13crypto.t_SignatureScheme &
                                                          t_CertificateKey) u8
                                                    else
                                                      asn1_error #(Bertie.Tls13crypto.t_SignatureScheme &
                                                          t_CertificateKey)
                                                        v_ASN1_INVALID_CERTIFICATE
                                                | Core.Result.Result_Err err ->
                                                  Core.Result.Result_Err err
                                                  <:
                                                  Core.Result.t_Result
                                                    (Bertie.Tls13crypto.t_SignatureScheme &
                                                      t_CertificateKey) u8)
                                            | Core.Result.Result_Err err ->
                                              Core.Result.Result_Err err
                                              <:
                                              Core.Result.t_Result
                                                (Bertie.Tls13crypto.t_SignatureScheme &
                                                  t_CertificateKey) u8)
                                        | Core.Result.Result_Err err ->
                                          Core.Result.Result_Err err
                                          <:
                                          Core.Result.t_Result
                                            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ) u8)
                                    | Core.Result.Result_Err err ->
                                      Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result
                                        (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                                  )
                                | Core.Result.Result_Err err ->
                                  Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                            | Core.Result.Result_Err err ->
                              Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                          else
                            let ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
                              ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize)
                            in
                            let rsa_pk_oid:bool =
                              if (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize) =. oid_len
                              then
                                let rsa_pk_oid:bool = true in
                                Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                                  (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize)
                                  (fun rsa_pk_oid temp_1_ ->
                                      let rsa_pk_oid:bool = rsa_pk_oid in
                                      let _:usize = temp_1_ in
                                      true)
                                  rsa_pk_oid
                                  (fun rsa_pk_oid i ->
                                      let rsa_pk_oid:bool = rsa_pk_oid in
                                      let i:usize = i in
                                      let oid_byte_equal:bool =
                                        (Bertie.Tls13utils.f_declassify #u8
                                            #u8
                                            #FStar.Tactics.Typeclasses.solve
                                            (cert.[ oid_offset +! i <: usize ] <: u8)
                                          <:
                                          u8) =.
                                        (Bertie.Tls13utils.f_declassify #u8
                                            #u8
                                            #FStar.Tactics.Typeclasses.solve
                                            (rsa_oid.[ i ] <: u8)
                                          <:
                                          u8)
                                      in
                                      let rsa_pk_oid:bool = rsa_pk_oid && oid_byte_equal in
                                      rsa_pk_oid)
                              else rsa_pk_oid
                            in
                            match
                              check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid)
                              <:
                              Core.Result.t_Result Prims.unit u8
                            with
                            | Core.Result.Result_Ok _ ->
                              let offset:usize = offset +! seq_len in
                              (match
                                  check_tag cert offset (mk_u8 3)
                                  <:
                                  Core.Result.t_Result Prims.unit u8
                                with
                                | Core.Result.Result_Ok _ ->
                                  let offset:usize = offset +! mk_usize 1 in
                                  (match
                                      length cert offset <: Core.Result.t_Result (usize & usize) u8
                                    with
                                    | Core.Result.Result_Ok (offset, bit_string_len) ->
                                      let offset:usize =
                                        if
                                          (Bertie.Tls13utils.f_declassify #u8
                                              #u8
                                              #FStar.Tactics.Typeclasses.solve
                                              (cert.[ offset ] <: u8)
                                            <:
                                            u8) =.
                                          mk_u8 0
                                        then
                                          let offset:usize = offset +! mk_usize 1 in
                                          offset
                                        else offset
                                      in
                                      if ec_pk_oid && ecdsa_p256
                                      then
                                        Core.Result.Result_Ok
                                        ((Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256
                                            <:
                                            Bertie.Tls13crypto.t_SignatureScheme),
                                          (CertificateKey offset (bit_string_len -! mk_usize 1)
                                            <:
                                            t_CertificateKey)
                                          <:
                                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                                          u8
                                      else
                                        if rsa_pk_oid
                                        then
                                          Core.Result.Result_Ok
                                          ((Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256
                                              <:
                                              Bertie.Tls13crypto.t_SignatureScheme),
                                            (CertificateKey offset (bit_string_len -! mk_usize 1)
                                              <:
                                              t_CertificateKey)
                                            <:
                                            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ))
                                          <:
                                          Core.Result.t_Result
                                            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ) u8
                                        else
                                          asn1_error #(Bertie.Tls13crypto.t_SignatureScheme &
                                              t_CertificateKey)
                                            v_ASN1_INVALID_CERTIFICATE
                                    | Core.Result.Result_Err err ->
                                      Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result
                                        (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                                  )
                                | Core.Result.Result_Err err ->
                                  Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                            | Core.Result.Result_Err err ->
                              Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                        else
                          let ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
                            ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize)
                          in
                          let rsa_pk_oid:bool =
                            if (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize) =. oid_len
                            then
                              let rsa_pk_oid:bool = true in
                              Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                                (Bertie.Tls13utils.impl_Bytes__len rsa_oid <: usize)
                                (fun rsa_pk_oid temp_1_ ->
                                    let rsa_pk_oid:bool = rsa_pk_oid in
                                    let _:usize = temp_1_ in
                                    true)
                                rsa_pk_oid
                                (fun rsa_pk_oid i ->
                                    let rsa_pk_oid:bool = rsa_pk_oid in
                                    let i:usize = i in
                                    let oid_byte_equal:bool =
                                      (Bertie.Tls13utils.f_declassify #u8
                                          #u8
                                          #FStar.Tactics.Typeclasses.solve
                                          (cert.[ oid_offset +! i <: usize ] <: u8)
                                        <:
                                        u8) =.
                                      (Bertie.Tls13utils.f_declassify #u8
                                          #u8
                                          #FStar.Tactics.Typeclasses.solve
                                          (rsa_oid.[ i ] <: u8)
                                        <:
                                        u8)
                                    in
                                    let rsa_pk_oid:bool = rsa_pk_oid && oid_byte_equal in
                                    rsa_pk_oid)
                            else rsa_pk_oid
                          in
                          (match
                              check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid)
                              <:
                              Core.Result.t_Result Prims.unit u8
                            with
                            | Core.Result.Result_Ok _ ->
                              let offset:usize = offset +! seq_len in
                              (match
                                  check_tag cert offset (mk_u8 3)
                                  <:
                                  Core.Result.t_Result Prims.unit u8
                                with
                                | Core.Result.Result_Ok _ ->
                                  let offset:usize = offset +! mk_usize 1 in
                                  (match
                                      length cert offset <: Core.Result.t_Result (usize & usize) u8
                                    with
                                    | Core.Result.Result_Ok (offset, bit_string_len) ->
                                      let offset:usize =
                                        if
                                          (Bertie.Tls13utils.f_declassify #u8
                                              #u8
                                              #FStar.Tactics.Typeclasses.solve
                                              (cert.[ offset ] <: u8)
                                            <:
                                            u8) =.
                                          mk_u8 0
                                        then
                                          let offset:usize = offset +! mk_usize 1 in
                                          offset
                                        else offset
                                      in
                                      if ec_pk_oid && ecdsa_p256
                                      then
                                        Core.Result.Result_Ok
                                        ((Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256
                                            <:
                                            Bertie.Tls13crypto.t_SignatureScheme),
                                          (CertificateKey offset (bit_string_len -! mk_usize 1)
                                            <:
                                            t_CertificateKey)
                                          <:
                                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
                                        <:
                                        Core.Result.t_Result
                                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                                          u8
                                      else
                                        if rsa_pk_oid
                                        then
                                          Core.Result.Result_Ok
                                          ((Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256
                                              <:
                                              Bertie.Tls13crypto.t_SignatureScheme),
                                            (CertificateKey offset (bit_string_len -! mk_usize 1)
                                              <:
                                              t_CertificateKey)
                                            <:
                                            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ))
                                          <:
                                          Core.Result.t_Result
                                            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ) u8
                                        else
                                          asn1_error #(Bertie.Tls13crypto.t_SignatureScheme &
                                              t_CertificateKey)
                                            v_ASN1_INVALID_CERTIFICATE
                                    | Core.Result.Result_Err err ->
                                      Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result
                                        (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                                  )
                                | Core.Result.Result_Err err ->
                                  Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result
                                    (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                            | Core.Result.Result_Err err ->
                              Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                      u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8

let verification_key_from_cert (cert: Bertie.Tls13utils.t_Bytes) =
  match read_sequence_header cert (mk_usize 0) <: Core.Result.t_Result usize u8 with
  | Core.Result.Result_Ok offset ->
    (match read_sequence_header cert offset <: Core.Result.t_Result usize u8 with
      | Core.Result.Result_Ok hoist107 ->
        let offset:usize = hoist107 in
        (match read_version_number cert offset <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok hoist108 ->
            let offset:usize = hoist108 in
            (match skip_integer cert offset <: Core.Result.t_Result usize u8 with
              | Core.Result.Result_Ok hoist109 ->
                let offset:usize = hoist109 in
                (match skip_sequence cert offset <: Core.Result.t_Result usize u8 with
                  | Core.Result.Result_Ok hoist110 ->
                    let offset:usize = hoist110 in
                    (match skip_sequence cert offset <: Core.Result.t_Result usize u8 with
                      | Core.Result.Result_Ok hoist111 ->
                        let offset:usize = hoist111 in
                        (match skip_sequence cert offset <: Core.Result.t_Result usize u8 with
                          | Core.Result.Result_Ok hoist112 ->
                            let offset:usize = hoist112 in
                            (match skip_sequence cert offset <: Core.Result.t_Result usize u8 with
                              | Core.Result.Result_Ok hoist113 ->
                                let offset:usize = hoist113 in
                                read_spki cert offset
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                      u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8

let ecdsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey) =
  let CertificateKey offset len:t_CertificateKey = indices in
  match check_tag cert offset (mk_u8 4) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    Core.Result.Result_Ok
    (Bertie.Tls13utils.impl_Bytes__slice cert
        (offset +! mk_usize 1 <: usize)
        (len -! mk_usize 1 <: usize))
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let rsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey) =
  let CertificateKey offset e_len:t_CertificateKey = indices in
  match check_tag cert offset (mk_u8 48) <: Core.Result.t_Result Prims.unit u8 with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! mk_usize 1 in
    (match length cert offset <: Core.Result.t_Result (usize & usize) u8 with
      | Core.Result.Result_Ok (offset, e_seq_len) ->
        (match check_tag cert offset (mk_u8 2) <: Core.Result.t_Result Prims.unit u8 with
          | Core.Result.Result_Ok _ ->
            let offset:usize = offset +! mk_usize 1 in
            (match length cert offset <: Core.Result.t_Result (usize & usize) u8 with
              | Core.Result.Result_Ok (offset, int_len) ->
                let n:Bertie.Tls13utils.t_Bytes =
                  Bertie.Tls13utils.impl_Bytes__slice cert offset int_len
                in
                let offset:usize = offset +! int_len in
                (match check_tag cert offset (mk_u8 2) <: Core.Result.t_Result Prims.unit u8 with
                  | Core.Result.Result_Ok _ ->
                    let offset:usize = offset +! mk_usize 1 in
                    (match length cert offset <: Core.Result.t_Result (usize & usize) u8 with
                      | Core.Result.Result_Ok (offset, int_len) ->
                        let e:Bertie.Tls13utils.t_Bytes =
                          Bertie.Tls13utils.impl_Bytes__slice cert offset int_len
                        in
                        Core.Result.Result_Ok
                        ({ Bertie.Tls13crypto.f_modulus = n; Bertie.Tls13crypto.f_exponent = e }
                          <:
                          Bertie.Tls13crypto.t_RsaVerificationKey)
                        <:
                        Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8

let rsa_private_key (key: Bertie.Tls13utils.t_Bytes) =
  match read_sequence_header key (mk_usize 0) <: Core.Result.t_Result usize u8 with
  | Core.Result.Result_Ok offset ->
    (match skip_integer key offset <: Core.Result.t_Result usize u8 with
      | Core.Result.Result_Ok hoist114 ->
        let offset:usize = hoist114 in
        (match skip_sequence key offset <: Core.Result.t_Result usize u8 with
          | Core.Result.Result_Ok hoist115 ->
            let offset:usize = hoist115 in
            (match read_octet_header key offset <: Core.Result.t_Result usize u8 with
              | Core.Result.Result_Ok hoist116 ->
                let offset:usize = hoist116 in
                (match read_sequence_header key offset <: Core.Result.t_Result usize u8 with
                  | Core.Result.Result_Ok hoist117 ->
                    let offset:usize = hoist117 in
                    (match skip_integer key offset <: Core.Result.t_Result usize u8 with
                      | Core.Result.Result_Ok hoist118 ->
                        let offset:usize = hoist118 in
                        (match skip_integer key offset <: Core.Result.t_Result usize u8 with
                          | Core.Result.Result_Ok hoist119 ->
                            let offset:usize = hoist119 in
                            (match skip_integer key offset <: Core.Result.t_Result usize u8 with
                              | Core.Result.Result_Ok hoist120 ->
                                let offset:usize = hoist120 in
                                read_integer key offset
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
        Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let cert_public_key
      (certificate: Bertie.Tls13utils.t_Bytes)
      (spki: (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
     =
  match spki._1 <: Bertie.Tls13crypto.t_SignatureScheme with
  | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
    asn1_error #Bertie.Tls13crypto.t_PublicVerificationKey v_ASN1_UNSUPPORTED_ALGORITHM
  | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
    (match
        ecdsa_public_key certificate spki._2 <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok pk ->
        Core.Result.Result_Ok
        (Bertie.Tls13crypto.PublicVerificationKey_EcDsa pk
          <:
          Bertie.Tls13crypto.t_PublicVerificationKey)
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
  | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
    match
      rsa_public_key certificate spki._2
      <:
      Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8
    with
    | Core.Result.Result_Ok pk ->
      Core.Result.Result_Ok
      (Bertie.Tls13crypto.PublicVerificationKey_Rsa pk <: Bertie.Tls13crypto.t_PublicVerificationKey
      )
      <:
      Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8
