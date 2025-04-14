module t13.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let asn1_error (#v_T: Type) (err: u8) = Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

let check_success (v_val: bool) =
  if v_val
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error v_ASN1_ERROR

let ecdsa_secp256r1_sha256_oid (_: Prims.unit) =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 3uy; 1uy; 7uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list 8 list)

let rsa_pkcs1_encryption_oid (_: Prims.unit) =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 134uy; 247uy; 13uy; 1uy; 1uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
      Rust_primitives.Hax.array_of_list 9 list)

let x962_ec_public_key_oid (_: Prims.unit) =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 2uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
      Rust_primitives.Hax.array_of_list 7 list)

let check_tag (b: t13.Tls13utils.t_Bytes) (offset: usize) (value: u8) =
  if (t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) =. value
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error v_ASN1_INVALID_TAG

let length_length (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  if ((t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) >>! 7l <: u8) =. 1uy
  then cast ((t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 127uy <: u8) <: usize
  else sz 0

let read_octet_header (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 4uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    let length_length:usize = length_length b offset in
    let offset:usize = (offset +! length_length <: usize) +! sz 1 in
    Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let read_sequence_header (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 48uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    let length_length:usize = length_length b offset in
    let offset:usize = (offset +! length_length <: usize) +! sz 1 in
    Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let short_length (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  if ((t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 128uy <: u8) =. 0uy
  then
    Core.Result.Result_Ok
    (cast ((t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 127uy <: u8) <: usize)
    <:
    Core.Result.t_Result usize u8
  else asn1_error v_ASN1_ERROR

let read_version_number (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 160uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    (match short_length b offset with
      | Core.Result.Result_Ok length ->
        Core.Result.Result_Ok ((offset +! sz 1 <: usize) +! length) <: Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err _ -> Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8

let long_length (b: t13.Tls13utils.t_Bytes) (offset len: usize) =
  if len >. sz 4
  then asn1_error v_ASN1_SEQUENCE_TOO_LONG
  else
    let u32word:t_Array u8 (sz 4) =
      Rust_primitives.Hax.repeat (t13.Tls13utils.v_U8 0uy <: u8) (sz 4)
    in
    let u32word:t_Array u8 (sz 4) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range u32word
        ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = len }
          <:
          Core.Ops.Range.t_Range usize)
        (Core.Slice.impl__copy_from_slice (u32word.[ {
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = len
                }
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
    ((cast (t13.Tls13utils.f_declassify (t13.Tls13utils.u32_from_be_bytes u32word <: u32)
            <:
            u32)
        <:
        usize) >>!
      ((sz 4 -! len <: usize) *! sz 8 <: usize))
    <:
    Core.Result.t_Result usize u8

let length (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  if ((t13.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 128uy <: u8) =. 0uy
  then
    match short_length b offset with
    | Core.Result.Result_Ok len ->
      Core.Result.Result_Ok (offset +! sz 1, len <: (usize & usize))
      <:
      Core.Result.t_Result (usize & usize) u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & usize) u8
  else
    let len:usize = length_length b offset in
    let offset:usize = offset +! sz 1 in
    match long_length b offset len with
    | Core.Result.Result_Ok v_end ->
      Core.Result.Result_Ok (offset +! len, v_end <: (usize & usize))
      <:
      Core.Result.t_Result (usize & usize) u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result (usize & usize) u8

let skip_integer (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 2uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    (match length b offset with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let skip_sequence (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 48uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    (match length b offset with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8
      | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8)
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result usize u8

let read_spki (cert: t13.Tls13utils.t_Bytes) (offset: usize) =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        check_tag cert offset 48uy <: Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        let offset:usize = offset +! sz 1 in
        (match length cert offset with
          | Core.Result.Result_Ok (offset, v__seq_len) ->
            (match check_tag cert offset 48uy with
              | Core.Result.Result_Ok _ ->
                let offset:usize = offset +! sz 1 in
                (match length cert offset with
                  | Core.Result.Result_Ok (offset, seq_len) ->
                    (match check_tag cert offset 6uy with
                      | Core.Result.Result_Ok _ ->
                        (match length cert (offset +! sz 1 <: usize) with
                          | Core.Result.Result_Ok (oid_offset, oid_len) ->
                            let ec_pk_oid, ecdsa_p256, rsa_pk_oid:(bool & bool & bool) =
                              false, false, false <: (bool & bool & bool)
                            in
                            let ec_oid:t13.Tls13utils.t_Bytes = x962_ec_public_key_oid () in
                            let rsa_oid:t13.Tls13utils.t_Bytes = rsa_pkcs1_encryption_oid () in
                            let! ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
                              if (t13.Tls13utils.impl__Bytes__len ec_oid <: usize) =. oid_len
                              then
                                let ec_pk_oid:bool = true in
                                let ec_pk_oid:bool =
                                  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter
                                        ({
                                            Core.Ops.Range.f_start = sz 0;
                                            Core.Ops.Range.f_end
                                            =
                                            t13.Tls13utils.impl__Bytes__len ec_oid <: usize
                                          }
                                          <:
                                          Core.Ops.Range.t_Range usize)
                                      <:
                                      Core.Ops.Range.t_Range usize)
                                    ec_pk_oid
                                    (fun ec_pk_oid i ->
                                        let ec_pk_oid:bool = ec_pk_oid in
                                        let i:usize = i in
                                        let oid_byte_equal:bool =
                                          (t13.Tls13utils.f_declassify (cert.[ oid_offset +! i
                                                  <:
                                                  usize ]
                                                <:
                                                u8)
                                            <:
                                            u8) =.
                                          (t13.Tls13utils.f_declassify (ec_oid.[ i ] <: u8) <: u8
                                          )
                                        in
                                        let ec_pk_oid:bool = ec_pk_oid && oid_byte_equal in
                                        ec_pk_oid)
                                in
                                if ec_pk_oid
                                then
                                  let oid_offset:usize = oid_offset +! oid_len in
                                  match check_tag cert oid_offset 6uy with
                                  | Core.Result.Result_Ok _ ->
                                    let oid_offset:usize = oid_offset +! sz 1 in
                                    (match length cert oid_offset with
                                      | Core.Result.Result_Ok (oid_offset, v__oid_len) ->
                                        let ecdsa_p256:bool = true in
                                        let ec_oid:t13.Tls13utils.t_Bytes =
                                          ecdsa_secp256r1_sha256_oid ()
                                        in
                                        let ecdsa_p256:bool =
                                          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter
                                                ({
                                                    Core.Ops.Range.f_start = sz 0;
                                                    Core.Ops.Range.f_end
                                                    =
                                                    t13.Tls13utils.impl__Bytes__len ec_oid
                                                    <:
                                                    usize
                                                  }
                                                  <:
                                                  Core.Ops.Range.t_Range usize)
                                              <:
                                              Core.Ops.Range.t_Range usize)
                                            ecdsa_p256
                                            (fun ecdsa_p256 i ->
                                                let ecdsa_p256:bool = ecdsa_p256 in
                                                let i:usize = i in
                                                let oid_byte_equal:bool =
                                                  (t13.Tls13utils.f_declassify (cert.[ oid_offset +!
                                                          i
                                                          <:
                                                          usize ]
                                                        <:
                                                        u8)
                                                    <:
                                                    u8) =.
                                                  (t13.Tls13utils.f_declassify (ec_oid.[ i ]
                                                        <:
                                                        u8)
                                                    <:
                                                    u8)
                                                in
                                                let ecdsa_p256:bool =
                                                  ecdsa_p256 && oid_byte_equal
                                                in
                                                ecdsa_p256)
                                        in
                                        (match check_success ecdsa_p256 with
                                          | Core.Result.Result_Ok _ ->
                                            Core.Ops.Control_flow.ControlFlow_Continue
                                            (ec_pk_oid, ecdsa_p256, oid_offset
                                              <:
                                              (bool & bool & usize))
                                            <:
                                            Core.Ops.Control_flow.t_ControlFlow
                                              (Core.Result.t_Result
                                                  (t13.Tls13crypto.t_SignatureScheme &
                                                    t_CertificateKey) u8) (bool & bool & usize)
                                          | Core.Result.Result_Err err ->
                                            let! _:Prims.unit =
                                              Core.Ops.Control_flow.ControlFlow_Break
                                              (Core.Result.Result_Err err
                                                <:
                                                Core.Result.t_Result
                                                  (t13.Tls13crypto.t_SignatureScheme &
                                                    t_CertificateKey) u8)
                                              <:
                                              Core.Ops.Control_flow.t_ControlFlow
                                                (Core.Result.t_Result
                                                    (t13.Tls13crypto.t_SignatureScheme &
                                                      t_CertificateKey) u8) Prims.unit
                                            in
                                            Core.Ops.Control_flow.ControlFlow_Continue
                                            (ec_pk_oid, ecdsa_p256, oid_offset
                                              <:
                                              (bool & bool & usize))
                                            <:
                                            Core.Ops.Control_flow.t_ControlFlow
                                              (Core.Result.t_Result
                                                  (t13.Tls13crypto.t_SignatureScheme &
                                                    t_CertificateKey) u8) (bool & bool & usize))
                                      | Core.Result.Result_Err err ->
                                        let! _:Prims.unit =
                                          Core.Ops.Control_flow.ControlFlow_Break
                                          (Core.Result.Result_Err err
                                            <:
                                            Core.Result.t_Result
                                              (t13.Tls13crypto.t_SignatureScheme &
                                                t_CertificateKey) u8)
                                          <:
                                          Core.Ops.Control_flow.t_ControlFlow
                                            (Core.Result.t_Result
                                                (t13.Tls13crypto.t_SignatureScheme &
                                                  t_CertificateKey) u8) Prims.unit
                                        in
                                        Core.Ops.Control_flow.ControlFlow_Continue
                                        (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
                                        <:
                                        Core.Ops.Control_flow.t_ControlFlow
                                          (Core.Result.t_Result
                                              (t13.Tls13crypto.t_SignatureScheme &
                                                t_CertificateKey) u8) (bool & bool & usize))
                                  | Core.Result.Result_Err err ->
                                    let! _:Prims.unit =
                                      Core.Ops.Control_flow.ControlFlow_Break
                                      (Core.Result.Result_Err err
                                        <:
                                        Core.Result.t_Result
                                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                                          u8)
                                      <:
                                      Core.Ops.Control_flow.t_ControlFlow
                                        (Core.Result.t_Result
                                            (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ) u8) Prims.unit
                                    in
                                    Core.Ops.Control_flow.ControlFlow_Continue
                                    (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
                                    <:
                                    Core.Ops.Control_flow.t_ControlFlow
                                      (Core.Result.t_Result
                                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                                          u8) (bool & bool & usize)
                                else
                                  Core.Ops.Control_flow.ControlFlow_Continue
                                  (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
                                  <:
                                  Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Result.t_Result
                                        (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                                    ) (bool & bool & usize)
                              else
                                Core.Ops.Control_flow.ControlFlow_Continue
                                (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
                                <:
                                Core.Ops.Control_flow.t_ControlFlow
                                  (Core.Result.t_Result
                                      (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                                  (bool & bool & usize)
                            in
                            Core.Ops.Control_flow.ControlFlow_Continue
                            (let rsa_pk_oid:bool =
                                if (t13.Tls13utils.impl__Bytes__len rsa_oid <: usize) =. oid_len
                                then
                                  let rsa_pk_oid:bool = true in
                                  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter
                                        ({
                                            Core.Ops.Range.f_start = sz 0;
                                            Core.Ops.Range.f_end
                                            =
                                            t13.Tls13utils.impl__Bytes__len rsa_oid <: usize
                                          }
                                          <:
                                          Core.Ops.Range.t_Range usize)
                                      <:
                                      Core.Ops.Range.t_Range usize)
                                    rsa_pk_oid
                                    (fun rsa_pk_oid i ->
                                        let rsa_pk_oid:bool = rsa_pk_oid in
                                        let i:usize = i in
                                        let oid_byte_equal:bool =
                                          (t13.Tls13utils.f_declassify (cert.[ oid_offset +! i
                                                  <:
                                                  usize ]
                                                <:
                                                u8)
                                            <:
                                            u8) =.
                                          (t13.Tls13utils.f_declassify (rsa_oid.[ i ] <: u8)
                                            <:
                                            u8)
                                        in
                                        let rsa_pk_oid:bool = rsa_pk_oid && oid_byte_equal in
                                        rsa_pk_oid)
                                else rsa_pk_oid
                              in
                              match check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid) with
                              | Core.Result.Result_Ok _ ->
                                let offset:usize = offset +! seq_len in
                                (match check_tag cert offset 3uy with
                                  | Core.Result.Result_Ok _ ->
                                    let offset:usize = offset +! sz 1 in
                                    (match length cert offset with
                                      | Core.Result.Result_Ok (offset, bit_string_len) ->
                                        let offset:usize =
                                          if
                                            (t13.Tls13utils.f_declassify (cert.[ offset ] <: u8)
                                              <:
                                              u8) =.
                                            0uy
                                          then
                                            let offset:usize = offset +! sz 1 in
                                            offset
                                          else offset
                                        in
                                        if ec_pk_oid && ecdsa_p256
                                        then
                                          Core.Result.Result_Ok
                                          ((t13.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256
                                              <:
                                              t13.Tls13crypto.t_SignatureScheme),
                                            (CertificateKey offset (bit_string_len -! sz 1)
                                              <:
                                              t_CertificateKey)
                                            <:
                                            (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ))
                                          <:
                                          Core.Result.t_Result
                                            (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey
                                            ) u8
                                        else
                                          if rsa_pk_oid
                                          then
                                            Core.Result.Result_Ok
                                            ((t13.Tls13crypto.SignatureScheme_RsaPssRsaSha256
                                                <:
                                                t13.Tls13crypto.t_SignatureScheme),
                                              (CertificateKey offset (bit_string_len -! sz 1)
                                                <:
                                                t_CertificateKey)
                                              <:
                                              (t13.Tls13crypto.t_SignatureScheme &
                                                t_CertificateKey))
                                            <:
                                            Core.Result.t_Result
                                              (t13.Tls13crypto.t_SignatureScheme &
                                                t_CertificateKey) u8
                                          else asn1_error v_ASN1_INVALID_CERTIFICATE
                                      | Core.Result.Result_Err err ->
                                        Core.Result.Result_Err err
                                        <:
                                        Core.Result.t_Result
                                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                                          u8)
                                  | Core.Result.Result_Err err ->
                                    Core.Result.Result_Err err
                                    <:
                                    Core.Result.t_Result
                                      (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                            <:
                            Core.Ops.Control_flow.t_ControlFlow
                              (Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                              (Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                          | Core.Result.Result_Err err ->
                            Core.Ops.Control_flow.ControlFlow_Continue
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result
                                (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                            <:
                            Core.Ops.Control_flow.t_ControlFlow
                              (Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                              (Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8))
                      | Core.Result.Result_Err err ->
                        Core.Ops.Control_flow.ControlFlow_Continue
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result
                            (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Result.t_Result
                              (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                          (Core.Result.t_Result
                              (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8))
                  | Core.Result.Result_Err err ->
                    Core.Ops.Control_flow.ControlFlow_Continue
                    (Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                        u8)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Result.t_Result
                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                      (Core.Result.t_Result
                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8))
              | Core.Result.Result_Err err ->
                Core.Ops.Control_flow.ControlFlow_Continue
                (Core.Result.Result_Err err
                  <:
                  Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                  )
                  (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
                  ))
          | Core.Result.Result_Err err ->
            Core.Ops.Control_flow.ControlFlow_Continue
            (Core.Result.Result_Err err
              <:
              Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
              (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8))
      | Core.Result.Result_Err err ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
        <:
        Core.Ops.Control_flow.t_ControlFlow
          (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          (Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8))

let verification_key_from_cert (cert: t13.Tls13utils.t_Bytes) =
  match read_sequence_header cert (sz 0) with
  | Core.Result.Result_Ok offset ->
    (match read_sequence_header cert offset with
      | Core.Result.Result_Ok hoist30 ->
        let offset:usize = hoist30 in
        (match read_version_number cert offset with
          | Core.Result.Result_Ok hoist31 ->
            let offset:usize = hoist31 in
            (match skip_integer cert offset with
              | Core.Result.Result_Ok hoist32 ->
                let offset:usize = hoist32 in
                (match skip_sequence cert offset with
                  | Core.Result.Result_Ok hoist33 ->
                    let offset:usize = hoist33 in
                    (match skip_sequence cert offset with
                      | Core.Result.Result_Ok hoist34 ->
                        let offset:usize = hoist34 in
                        (match skip_sequence cert offset with
                          | Core.Result.Result_Ok hoist35 ->
                            let offset:usize = hoist35 in
                            (match skip_sequence cert offset with
                              | Core.Result.Result_Ok hoist36 ->
                                let offset:usize = hoist36 in
                                read_spki cert offset
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result
                                  (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result
                              (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result
                          (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                      u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8

let ecdsa_public_key (cert: t13.Tls13utils.t_Bytes) (indices: t_CertificateKey) =
  let CertificateKey offset len:t_CertificateKey = indices in
  match check_tag cert offset 4uy with
  | Core.Result.Result_Ok _ ->
    Core.Result.Result_Ok
    (t13.Tls13utils.impl__Bytes__slice cert (offset +! sz 1 <: usize) (len -! sz 1 <: usize))
    <:
    Core.Result.t_Result t13.Tls13utils.t_Bytes u8
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8

let read_integer (b: t13.Tls13utils.t_Bytes) (offset: usize) =
  match check_tag b offset 2uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    (match length b offset with
      | Core.Result.Result_Ok (offset, length) ->
        Core.Result.Result_Ok (t13.Tls13utils.impl__Bytes__slice b offset length)
        <:
        Core.Result.t_Result t13.Tls13utils.t_Bytes u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8

let rsa_private_key (key: t13.Tls13utils.t_Bytes) =
  match read_sequence_header key (sz 0) with
  | Core.Result.Result_Ok offset ->
    (match skip_integer key offset with
      | Core.Result.Result_Ok hoist41 ->
        let offset:usize = hoist41 in
        (match skip_sequence key offset with
          | Core.Result.Result_Ok hoist42 ->
            let offset:usize = hoist42 in
            (match read_octet_header key offset with
              | Core.Result.Result_Ok hoist43 ->
                let offset:usize = hoist43 in
                (match read_sequence_header key offset with
                  | Core.Result.Result_Ok hoist44 ->
                    let offset:usize = hoist44 in
                    (match skip_integer key offset with
                      | Core.Result.Result_Ok hoist45 ->
                        let offset:usize = hoist45 in
                        (match skip_integer key offset with
                          | Core.Result.Result_Ok hoist46 ->
                            let offset:usize = hoist46 in
                            (match skip_integer key offset with
                              | Core.Result.Result_Ok hoist47 ->
                                let offset:usize = hoist47 in
                                read_integer key offset
                              | Core.Result.Result_Err err ->
                                Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                          | Core.Result.Result_Err err ->
                            Core.Result.Result_Err err
                            <:
                            Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13utils.t_Bytes u8

let rsa_public_key (cert: t13.Tls13utils.t_Bytes) (indices: t_CertificateKey) =
  let CertificateKey offset v__len:t_CertificateKey = indices in
  match check_tag cert offset 48uy with
  | Core.Result.Result_Ok _ ->
    let offset:usize = offset +! sz 1 in
    (match length cert offset with
      | Core.Result.Result_Ok (offset, v__seq_len) ->
        (match check_tag cert offset 2uy with
          | Core.Result.Result_Ok _ ->
            let offset:usize = offset +! sz 1 in
            (match length cert offset with
              | Core.Result.Result_Ok (offset, int_len) ->
                let n:t13.Tls13utils.t_Bytes =
                  t13.Tls13utils.impl__Bytes__slice cert offset int_len
                in
                let offset:usize = offset +! int_len in
                (match check_tag cert offset 2uy with
                  | Core.Result.Result_Ok _ ->
                    let offset:usize = offset +! sz 1 in
                    (match length cert offset with
                      | Core.Result.Result_Ok (offset, int_len) ->
                        let e:t13.Tls13utils.t_Bytes =
                          t13.Tls13utils.impl__Bytes__slice cert offset int_len
                        in
                        Core.Result.Result_Ok
                        ({ t13.Tls13crypto.f_modulus = n; t13.Tls13crypto.f_exponent = e }
                          <:
                          t13.Tls13crypto.t_RsaVerificationKey)
                        <:
                        Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8
                      | Core.Result.Result_Err err ->
                        Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
              | Core.Result.Result_Err err ->
                Core.Result.Result_Err err
                <:
                Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t13.Tls13crypto.t_RsaVerificationKey u8

let cert_public_key
      (certificate: t13.Tls13utils.t_Bytes)
      (spki: (t13.Tls13crypto.t_SignatureScheme & t_CertificateKey))
     =
  match spki._1 with
  | t13.Tls13crypto.SignatureScheme_ED25519  -> asn1_error v_ASN1_UNSUPPORTED_ALGORITHM
  | t13.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
    (match ecdsa_public_key certificate spki._2 with
      | Core.Result.Result_Ok pk ->
        Core.Result.Result_Ok
        (t13.Tls13crypto.PublicVerificationKey_EcDsa pk
          <:
          t13.Tls13crypto.t_PublicVerificationKey)
        <:
        Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err
        <:
        Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8)
  | t13.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
    match rsa_public_key certificate spki._2 with
    | Core.Result.Result_Ok pk ->
      Core.Result.Result_Ok
      (t13.Tls13crypto.PublicVerificationKey_Rsa pk <: t13.Tls13crypto.t_PublicVerificationKey
      )
      <:
      Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err
      <:
      Core.Result.t_Result t13.Tls13crypto.t_PublicVerificationKey u8
