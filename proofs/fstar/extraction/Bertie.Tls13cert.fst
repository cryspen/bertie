module Bertie.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Asn1Error = u8

let v_ASN1_ERROR: u8 = 25uy

let v_ASN1_INVALID_CERTIFICATE: u8 = 23uy

let v_ASN1_INVALID_TAG: u8 = 22uy

let v_ASN1_SEQUENCE_TOO_LONG: u8 = 21uy

let v_ASN1_UNSUPPORTED_ALGORITHM: u8 = 24uy

let asn1_error
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized v_T)
      (err: u8)
    : Core.Result.t_Result v_T u8 = Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

let check_success (v_val: bool) : Core.Result.t_Result Prims.unit u8 =
  if v_val
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error v_ASN1_ERROR

type t_CertificateKey = | CertificateKey : usize -> usize -> t_CertificateKey

unfold
let t_Spki = (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)

let ecdsa_secp256r1_sha256_oid (_: Prims.unit) : Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 3uy; 1uy; 7uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list list)

let rsa_pkcs1_encryption_oid (_: Prims.unit) : Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 134uy; 247uy; 13uy; 1uy; 1uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
      Rust_primitives.Hax.array_of_list list)

let x962_ec_public_key_oid (_: Prims.unit) : Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 2uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
      Rust_primitives.Hax.array_of_list list)

let check_tag (b: Bertie.Tls13utils.t_Bytes) (offset: usize) (value: u8)
    : Core.Result.t_Result Prims.unit u8 =
  if (Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) =. value
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else asn1_error v_ASN1_INVALID_TAG

let length_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : usize =
  if ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) >>! 7l <: u8) =. 1uy
  then cast ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 127uy <: u8) <: usize
  else sz 0

let read_octet_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag b offset 4uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let offset:usize = offset +! sz 1 in
        let length_length:usize = length_length b offset in
        let offset:usize = (offset +! length_length <: usize) +! sz 1 in
        Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result usize u8) u8)

let read_sequence_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag b offset 48uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let offset:usize = offset +! sz 1 in
        let length_length:usize = length_length b offset in
        let offset:usize = (offset +! length_length <: usize) +! sz 1 in
        Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result usize u8) u8)

let short_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  if ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 128uy <: u8) =. 0uy
  then
    Core.Result.Result_Ok
    (cast ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 127uy <: u8) <: usize)
    <:
    Core.Result.t_Result usize u8
  else asn1_error v_ASN1_ERROR

let read_version_number (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (match
        check_tag b offset 160uy <: Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        let offset:usize = offset +! sz 1 in
        let| length:usize =
          Core.Result.impl__map_err (short_length b offset <: Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok ((offset +! sz 1 <: usize) +! length)
          <:
          Core.Result.t_Result usize u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result usize u8) u8
      | Core.Result.Result_Err _ ->
        Core.Result.Result_Ok (Core.Result.Result_Ok offset <: Core.Result.t_Result usize u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result usize u8) u8)

let long_length (b: Bertie.Tls13utils.t_Bytes) (offset len: usize) : Core.Result.t_Result usize u8 =
  if len >. sz 4
  then asn1_error v_ASN1_SEQUENCE_TOO_LONG
  else
    let u32word:t_Array u8 (sz 4) =
      Rust_primitives.Hax.repeat (Bertie.Tls13utils.v_U8 0uy <: u8) (sz 4)
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
    ((cast (Bertie.Tls13utils.f_declassify (Bertie.Tls13utils.u32_from_be_bytes u32word <: u32)
            <:
            u32)
        <:
        usize) >>!
      ((sz 4 -! len <: usize) *! sz 8 <: usize))
    <:
    Core.Result.t_Result usize u8

let length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result (usize & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (if
        ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: u8) <: u8) &. 128uy <: u8) =. 0uy <: bool
      then
        let| len:usize =
          Core.Result.impl__map_err (short_length b offset <: Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (offset +! sz 1, len <: (usize & usize))
          <:
          Core.Result.t_Result (usize & usize) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & usize) u8) u8
      else
        let len:usize = length_length b offset in
        let offset:usize = offset +! sz 1 in
        let| v_end:usize =
          Core.Result.impl__map_err (long_length b offset len <: Core.Result.t_Result usize u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok (offset +! len, v_end <: (usize & usize))
          <:
          Core.Result.t_Result (usize & usize) u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result (usize & usize) u8) u8)

let skip_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag b offset 2uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, length:(usize & usize) =
        Core.Result.impl__map_err (length b offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result usize u8) u8)

let skip_sequence (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag b offset 48uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, length:(usize & usize) =
        Core.Result.impl__map_err (length b offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok (offset +! length) <: Core.Result.t_Result usize u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result usize u8) u8)

let read_spki (cert: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 48uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, v__seq_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 48uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, seq_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 6uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| oid_offset, oid_len:(usize & usize) =
        Core.Result.impl__map_err (length cert (offset +! sz 1 <: usize)
            <:
            Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let ec_pk_oid, ecdsa_p256, rsa_pk_oid:(bool & bool & bool) =
        false, false, false <: (bool & bool & bool)
      in
      let ec_oid:Bertie.Tls13utils.t_Bytes = x962_ec_public_key_oid () in
      let rsa_oid:Bertie.Tls13utils.t_Bytes = rsa_pkcs1_encryption_oid () in
      let| ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
        if (Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize) =. oid_len
        then
          let ec_pk_oid:bool = true in
          let ec_pk_oid:bool =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize
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
                    (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ] <: u8) <: u8) =.
                    (Bertie.Tls13utils.f_declassify (ec_oid.[ i ] <: u8) <: u8)
                  in
                  let ec_pk_oid:bool = ec_pk_oid && oid_byte_equal in
                  ec_pk_oid)
          in
          if ec_pk_oid
          then
            let oid_offset:usize = oid_offset +! oid_len in
            let| _:Prims.unit =
              Core.Result.impl__map_err (check_tag cert oid_offset 6uy
                  <:
                  Core.Result.t_Result Prims.unit u8)
                (Core.Convert.f_from <: u8 -> u8)
            in
            let oid_offset:usize = oid_offset +! sz 1 in
            let| oid_offset, v__oid_len:(usize & usize) =
              Core.Result.impl__map_err (length cert oid_offset
                  <:
                  Core.Result.t_Result (usize & usize) u8)
                (Core.Convert.f_from <: u8 -> u8)
            in
            let ecdsa_p256:bool = true in
            let ec_oid:Bertie.Tls13utils.t_Bytes = ecdsa_secp256r1_sha256_oid () in
            let ecdsa_p256:bool =
              Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize
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
                      (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ] <: u8)
                        <:
                        u8) =.
                      (Bertie.Tls13utils.f_declassify (ec_oid.[ i ] <: u8) <: u8)
                    in
                    let ecdsa_p256:bool = ecdsa_p256 && oid_byte_equal in
                    ecdsa_p256)
            in
            let| _:Prims.unit =
              Core.Result.impl__map_err (check_success ecdsa_p256
                  <:
                  Core.Result.t_Result Prims.unit u8)
                (Core.Convert.f_from <: u8 -> u8)
            in
            Core.Result.Result_Ok (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
            <:
            Core.Result.t_Result (bool & bool & usize) u8
          else
            Core.Result.Result_Ok (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
            <:
            Core.Result.t_Result (bool & bool & usize) u8
        else
          Core.Result.Result_Ok (ec_pk_oid, ecdsa_p256, oid_offset <: (bool & bool & usize))
          <:
          Core.Result.t_Result (bool & bool & usize) u8
      in
      let rsa_pk_oid:bool =
        if (Bertie.Tls13utils.impl__Bytes__len rsa_oid <: usize) =. oid_len
        then
          let rsa_pk_oid:bool = true in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len rsa_oid <: usize
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
                  (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ] <: u8) <: u8) =.
                  (Bertie.Tls13utils.f_declassify (rsa_oid.[ i ] <: u8) <: u8)
                in
                let rsa_pk_oid:bool = rsa_pk_oid && oid_byte_equal in
                rsa_pk_oid)
        else rsa_pk_oid
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid)
            <:
            Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! seq_len in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 3uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, bit_string_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let offset:usize =
          if (Bertie.Tls13utils.f_declassify (cert.[ offset ] <: u8) <: u8) =. 0uy
          then
            let offset:usize = offset +! sz 1 in
            offset
          else offset
        in
        if ec_pk_oid && ecdsa_p256
        then
          Core.Result.Result_Ok
          ((Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256
              <:
              Bertie.Tls13crypto.t_SignatureScheme),
            (CertificateKey offset (bit_string_len -! sz 1) <: t_CertificateKey)
            <:
            (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
          <:
          Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
        else
          if rsa_pk_oid
          then
            Core.Result.Result_Ok
            ((Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256
                <:
                Bertie.Tls13crypto.t_SignatureScheme),
              (CertificateKey offset (bit_string_len -! sz 1) <: t_CertificateKey)
              <:
              (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
            <:
            Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8
          else asn1_error v_ASN1_INVALID_CERTIFICATE)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8) u8)

let verification_key_from_cert (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| offset:usize =
        Core.Result.impl__map_err (read_sequence_header cert (sz 0) <: Core.Result.t_Result usize u8
          )
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist33:usize =
        Core.Result.impl__map_err (read_sequence_header cert offset <: Core.Result.t_Result usize u8
          )
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist33 in
      let| hoist34:usize =
        Core.Result.impl__map_err (read_version_number cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist34 in
      let| hoist35:usize =
        Core.Result.impl__map_err (skip_integer cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist35 in
      let| hoist36:usize =
        Core.Result.impl__map_err (skip_sequence cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist36 in
      let| hoist37:usize =
        Core.Result.impl__map_err (skip_sequence cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist37 in
      let| hoist38:usize =
        Core.Result.impl__map_err (skip_sequence cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist38 in
      let| hoist39:usize =
        Core.Result.impl__map_err (skip_sequence cert offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let offset:usize = hoist39 in
        read_spki cert offset)
      <:
      Core.Result.t_Result
        (Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8) u8)

let ecdsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let CertificateKey offset len:t_CertificateKey
      =
        indices
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 4uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok
        (Bertie.Tls13utils.impl__Bytes__slice cert (offset +! sz 1 <: usize) (len -! sz 1 <: usize))
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let read_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag b offset 2uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, length:(usize & usize) =
        Core.Result.impl__map_err (length b offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (Core.Result.Result_Ok (Bertie.Tls13utils.impl__Bytes__slice b offset length)
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let rsa_private_key (key: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| offset:usize =
        Core.Result.impl__map_err (read_sequence_header key (sz 0) <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| hoist48:usize =
        Core.Result.impl__map_err (skip_integer key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist48 in
      let| hoist49:usize =
        Core.Result.impl__map_err (skip_sequence key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist49 in
      let| hoist50:usize =
        Core.Result.impl__map_err (read_octet_header key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist50 in
      let| hoist51:usize =
        Core.Result.impl__map_err (read_sequence_header key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist51 in
      let| hoist52:usize =
        Core.Result.impl__map_err (skip_integer key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist52 in
      let| hoist53:usize =
        Core.Result.impl__map_err (skip_integer key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = hoist53 in
      let| hoist54:usize =
        Core.Result.impl__map_err (skip_integer key offset <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let offset:usize = hoist54 in
        read_integer key offset)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) u8)

let rsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let CertificateKey offset v__len:t_CertificateKey
      =
        indices
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 48uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, v__seq_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 2uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, int_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let n:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__slice cert offset int_len in
      let offset:usize = offset +! int_len in
      let| _:Prims.unit =
        Core.Result.impl__map_err (check_tag cert offset 2uy <: Core.Result.t_Result Prims.unit u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      let offset:usize = offset +! sz 1 in
      let| offset, int_len:(usize & usize) =
        Core.Result.impl__map_err (length cert offset <: Core.Result.t_Result (usize & usize) u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let e:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__slice cert offset int_len in
        Core.Result.Result_Ok
        ({ Bertie.Tls13crypto.f_modulus = n; Bertie.Tls13crypto.f_exponent = e }
          <:
          Bertie.Tls13crypto.t_RsaVerificationKey)
        <:
        Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8) u8)

let cert_public_key
      (certificate: Bertie.Tls13utils.t_Bytes)
      (spki: (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
    : Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (match spki._1 with
      | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
        Core.Result.Result_Ok
        (asn1_error v_ASN1_UNSUPPORTED_ALGORITHM
          <:
          Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8) u8
      | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
        let| pk:Bertie.Tls13utils.t_Bytes =
          Core.Result.impl__map_err (ecdsa_public_key certificate spki._2
              <:
              Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok
          (Bertie.Tls13crypto.PublicVerificationKey_EcDsa pk
            <:
            Bertie.Tls13crypto.t_PublicVerificationKey)
          <:
          Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8) u8
      | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
        let| pk:Bertie.Tls13crypto.t_RsaVerificationKey =
          Core.Result.impl__map_err (rsa_public_key certificate spki._2
              <:
              Core.Result.t_Result Bertie.Tls13crypto.t_RsaVerificationKey u8)
            (Core.Convert.f_from <: u8 -> u8)
        in
        Core.Result.Result_Ok
        (Core.Result.Result_Ok
          (Bertie.Tls13crypto.PublicVerificationKey_Rsa pk
            <:
            Bertie.Tls13crypto.t_PublicVerificationKey)
          <:
          Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
        <:
        Core.Result.t_Result (Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8) u8
    )
