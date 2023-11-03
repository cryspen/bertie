module Bertie.Tls13cert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_CertificateKey = | CertificateKey : usize -> usize -> t_CertificateKey

let t_Asn1Error = u8

let v_ASN1_SEQUENCE_TOO_LONG: u8 = 21uy

let v_ASN1_INVALID_TAG: u8 = 22uy

let v_ASN1_INVALID_CERTIFICATE: u8 = 23uy

let v_ASN1_UNSUPPORTED_ALGORITHM: u8 = 24uy

let v_ASN1_ERROR: u8 = 25uy

let t_UsizeResult = Core.Result.t_Result usize u8

let t_DoubleUsizeResult = Core.Result.t_Result (usize & usize) u8

let t_SpkiResult = Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8

let t_PkResult = Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8

let t_VerificationKeyResult = Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let t_RsaVerificationKeyResult =
  Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8

let asn1err
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_T)
      (err: u8)
    : Core.Result.t_Result v_T u8 =
  let bt:Backtrace.Capture.t_Backtrace = Backtrace.Capture.impl__Backtrace__new in
  let _:Prims.unit =
    Std.Io.Stdio.v__print (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice string)
          (Rust_primitives.unsize (let list =
                  [Core.Fmt.Rt.impl_1__new_debug bt <: Core.Fmt.Rt.t_Argument]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list list)
            <:
            t_Slice Core.Fmt.Rt.t_Argument)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  Core.Result.Result_Err err

let long_length (b: Bertie.Tls13utils.t_Bytes) (offset len: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if len >. sz 4 <: bool
      then
        Core.Ops.Control_flow.ControlFlow_Continue
        (asn1err v_ASN1_SEQUENCE_TOO_LONG <: Core.Result.t_Result usize u8)
      else
        let (u32word: Bertie.Tls13utils.t_Bytes):Bertie.Tls13utils.t_Bytes =
          Bertie.Tls13utils.impl__Bytes__zeroes (sz 4)
        in
        let u32word:Bertie.Tls13utils.t_Bytes =
          Rust_primitives.Hax.update_at u32word
            ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = len })
            (Core.Slice.impl__copy_from_slice (Core.Ops.Index.IndexMut.index_mut u32word
                    ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = len })
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
                (b.[ {
                      Core.Ops.Range.f_start = offset;
                      Core.Ops.Range.f_end = offset +! len <: usize
                    } ]
                  <:
                  t_Slice Bertie.Tls13utils.t_U8)
              <:
              t_Slice Bertie.Tls13utils.t_U8)
        in
        let* hoist474:Bertie.Tls13utils.t_U32 =
          match
            Core.Ops.Try_trait.f_branch (Bertie.Tls13utils.impl__U32__from_be_bytes u32word
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_U32 u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist473:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result usize u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist473)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (let hoist475:u32 = Bertie.Tls13utils.impl__U32__declassify hoist474 in
          let hoist476:usize = cast hoist475 <: usize in
          let hoist477:usize = hoist476 >>! ((sz 4 -! len <: usize) *! sz 8 <: usize) in
          Core.Result.Result.v_Ok hoist477))

let length_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : usize =
  if
    ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) >>! 7l <: u8) =.
    1uy
  then
    cast ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) &. 127uy)
    <:
    usize
  else sz 0

let short_length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  if
    ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) &. 128uy <: u8) =.
    0uy
  then
    Core.Result.Result.v_Ok (cast ((Bertie.Tls13utils.f_declassify (b.[ offset ]
                  <:
                  Bertie.Tls13utils.t_U8)
              <:
              u8) &.
            127uy
            <:
            u8)
        <:
        usize)
  else asn1err v_ASN1_ERROR

let length (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result (usize & usize) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (if
        ((Bertie.Tls13utils.f_declassify (b.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) &. 128uy
          <:
          u8) =.
        0uy
        <:
        bool
      then
        let* len:usize =
          match
            Core.Ops.Try_trait.f_branch (short_length b offset <: Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist478:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist478)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok ((offset +! sz 1 <: usize), len))
      else
        let len:usize = length_length b offset in
        let offset:usize = offset +! sz 1 in
        let* v_end:usize =
          match
            Core.Ops.Try_trait.f_branch (long_length b offset len <: Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist479:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result (usize & usize) u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist479)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok ((offset +! len <: usize), v_end)))

let read_sequence_header (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag b offset 48uy <: Core.Result.t_Result Prims.unit u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist480:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist480)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let offset:usize = offset +! sz 1 in
        let length_length:usize = length_length b offset in
        let offset:usize = (offset +! length_length <: usize) +! sz 1 in
        Core.Result.Result.v_Ok offset))

let check_tag (b: Bertie.Tls13utils.t_Bytes) (offset: usize) (value: u8)
    : Core.Result.t_Result Prims.unit u8 =
  if (Bertie.Tls13utils.f_declassify (b.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) =. value
  then Core.Result.Result_Ok ()
  else asn1err v_ASN1_INVALID_TAG

let skip_sequence (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag b offset 48uy <: Core.Result.t_Result Prims.unit u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist481:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist481)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, length:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length b offset <: Core.Result.t_Result (usize & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist482:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist482)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result.v_Ok (offset +! length <: usize)))

let read_version_number (b: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match
        check_tag b offset 160uy <: Core.Result.t_Result Prims.unit u8
      with
      | Core.Result.Result_Ok _ ->
        let offset:usize = offset +! sz 1 in
        let* length:usize =
          match
            Core.Ops.Try_trait.f_branch (short_length b offset <: Core.Result.t_Result usize u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist483:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result usize u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist483)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok ((offset +! sz 1 <: usize) +! length <: usize))
      | Core.Result.Result_Err _ ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok offset <: Core.Result.t_Result usize u8))

let read_integer (b: Bertie.Tls13utils.t_Bytes) (offset: usize) : Core.Result.t_Result usize u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag b offset 2uy <: Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist484:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist484)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, length:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length b offset <: Core.Result.t_Result (usize & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist485:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result usize u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist485)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result.v_Ok (offset +! length <: usize)))

let t_Spki = (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)

let x962_ec_public_key_oid: Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 2uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
      Rust_primitives.Hax.array_of_list list)

let ecdsa_secp256r1_sha256_oid: Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 206uy; 61uy; 3uy; 1uy; 7uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
      Rust_primitives.Hax.array_of_list list)

let rsa_pkcs1_encryption_oid: Bertie.Tls13utils.t_Bytes =
  Core.Convert.f_into (let list = [42uy; 134uy; 72uy; 134uy; 247uy; 13uy; 1uy; 1uy; 1uy] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
      Rust_primitives.Hax.array_of_list list)

let check_success (v_val: bool) : Core.Result.t_Result Prims.unit u8 =
  if v_val then Core.Result.Result_Ok () else asn1err v_ASN1_ERROR

let read_spki (cert: Bertie.Tls13utils.t_Bytes) (offset: usize)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 48uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist486:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist486)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, v__seq_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist487:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist487)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 48uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist488:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist488)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, seq_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist489:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist489)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 6uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist490:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist490)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* oid_offset, oid_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert (offset +! sz 1 <: usize)
              <:
              Core.Result.t_Result (usize & usize) u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist491:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist491)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let ec_pk_oid, ecdsa_p256, rsa_pk_oid:(bool & bool & bool) = false, false, false in
      let ec_oid:Bertie.Tls13utils.t_Bytes = x962_ec_public_key_oid in
      let rsa_oid:Bertie.Tls13utils.t_Bytes = rsa_pkcs1_encryption_oid in
      let* ec_pk_oid, ecdsa_p256, oid_offset:(bool & bool & usize) =
        if (Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize) =. oid_len
        then
          let ec_pk_oid:bool = true in
          let ec_pk_oid:bool =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize
                    })
                <:
                Core.Ops.Range.t_Range usize)
              ec_pk_oid
              (fun ec_pk_oid i ->
                  let oid_byte_equal:bool =
                    (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ]
                          <:
                          Bertie.Tls13utils.t_U8)
                      <:
                      u8) =.
                    (Bertie.Tls13utils.f_declassify (ec_oid.[ i ] <: Bertie.Tls13utils.t_U8) <: u8)
                  in
                  let ec_pk_oid:bool = ec_pk_oid && oid_byte_equal in
                  ec_pk_oid)
          in
          if ec_pk_oid
          then
            let oid_offset:usize = oid_offset +! oid_len in
            let* _:Prims.unit =
              match
                Core.Ops.Try_trait.f_branch (check_tag cert oid_offset 6uy
                    <:
                    Core.Result.t_Result Prims.unit u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist492:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                        u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist492)
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
            in
            let oid_offset:usize = oid_offset +! sz 1 in
            let* oid_offset, v__oid_len:(usize & usize) =
              match
                Core.Ops.Try_trait.f_branch (length cert oid_offset
                    <:
                    Core.Result.t_Result (usize & usize) u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist493:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                        u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist493)
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
            in
            let ecdsa_p256:bool = true in
            let ec_oid:Bertie.Tls13utils.t_Bytes = ecdsa_secp256r1_sha256_oid in
            let ecdsa_p256:bool =
              Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len ec_oid <: usize
                      })
                  <:
                  Core.Ops.Range.t_Range usize)
                ecdsa_p256
                (fun ecdsa_p256 i ->
                    let oid_byte_equal:bool =
                      (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ]
                            <:
                            Bertie.Tls13utils.t_U8)
                        <:
                        u8) =.
                      (Bertie.Tls13utils.f_declassify (ec_oid.[ i ] <: Bertie.Tls13utils.t_U8) <: u8
                      )
                    in
                    let ecdsa_p256:bool = ecdsa_p256 && oid_byte_equal in
                    ecdsa_p256)
            in
            let* _:Prims.unit =
              match
                Core.Ops.Try_trait.f_branch (check_success ecdsa_p256
                    <:
                    Core.Result.t_Result Prims.unit u8)
              with
              | Core.Ops.Control_flow.ControlFlow_Break residual ->
                let* hoist494:Rust_primitives.Hax.t_Never =
                  Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual

                      <:
                      Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey)
                        u8)
                in
                Core.Ops.Control_flow.ControlFlow_Continue
                (Rust_primitives.Hax.never_to_any hoist494)
              | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
                Core.Ops.Control_flow.ControlFlow_Continue v_val
            in
            Core.Ops.Control_flow.ControlFlow_Continue (ec_pk_oid, ecdsa_p256, oid_offset)
          else Core.Ops.Control_flow.ControlFlow_Continue (ec_pk_oid, ecdsa_p256, oid_offset)
        else Core.Ops.Control_flow.ControlFlow_Continue (ec_pk_oid, ecdsa_p256, oid_offset)
      in
      let rsa_pk_oid:bool =
        if (Bertie.Tls13utils.impl__Bytes__len rsa_oid <: usize) =. oid_len
        then
          let rsa_pk_oid:bool = true in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = Bertie.Tls13utils.impl__Bytes__len rsa_oid <: usize
                  })
              <:
              Core.Ops.Range.t_Range usize)
            rsa_pk_oid
            (fun rsa_pk_oid i ->
                let oid_byte_equal:bool =
                  (Bertie.Tls13utils.f_declassify (cert.[ oid_offset +! i <: usize ]
                        <:
                        Bertie.Tls13utils.t_U8)
                    <:
                    u8) =.
                  (Bertie.Tls13utils.f_declassify (rsa_oid.[ i ] <: Bertie.Tls13utils.t_U8) <: u8)
                in
                let rsa_pk_oid:bool = rsa_pk_oid && oid_byte_equal in
                rsa_pk_oid)
        else rsa_pk_oid
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_success (ec_pk_oid && ecdsa_p256 || rsa_pk_oid)
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist495:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist495)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! seq_len in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 3uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist496:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist496)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, bit_string_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist497:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist497)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let offset:usize =
          if
            (Bertie.Tls13utils.f_declassify (cert.[ offset ] <: Bertie.Tls13utils.t_U8) <: u8) =.
            0uy
          then
            let offset:usize = offset +! sz 1 in
            offset
          else offset
        in
        if ec_pk_oid && ecdsa_p256
        then
          Core.Result.Result.v_Ok (Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256,
              CertificateKey offset (bit_string_len -! sz 1 <: usize))
        else
          if rsa_pk_oid
          then
            Core.Result.Result.v_Ok (Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256,
                CertificateKey offset (bit_string_len -! sz 1 <: usize))
          else asn1err v_ASN1_INVALID_CERTIFICATE))

let verification_key_from_cert (cert: Bertie.Tls13utils.t_Bytes)
    : Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let* offset:usize =
        match
          Core.Ops.Try_trait.f_branch (read_sequence_header cert (sz 0)
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist498:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist498)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* hoist500:usize =
        match
          Core.Ops.Try_trait.f_branch (read_sequence_header cert offset
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist499:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist499)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist500 in
      let* hoist502:usize =
        match
          Core.Ops.Try_trait.f_branch (read_version_number cert offset
              <:
              Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist501:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist501)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist502 in
      let* hoist504:usize =
        match
          Core.Ops.Try_trait.f_branch (read_integer cert offset <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist503:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist503)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist504 in
      let* hoist506:usize =
        match
          Core.Ops.Try_trait.f_branch (skip_sequence cert offset <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist505:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist505)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist506 in
      let* hoist508:usize =
        match
          Core.Ops.Try_trait.f_branch (skip_sequence cert offset <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist507:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist507)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist508 in
      let* hoist510:usize =
        match
          Core.Ops.Try_trait.f_branch (skip_sequence cert offset <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist509:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist509)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = hoist510 in
      let* hoist512:usize =
        match
          Core.Ops.Try_trait.f_branch (skip_sequence cert offset <: Core.Result.t_Result usize u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist511:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist511)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let offset:usize = hoist512 in
        read_spki cert offset))

let ecdsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let CertificateKey offset len:t_CertificateKey
      =
        indices
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 4uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist513:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist513)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (Core.Result.Result.v_Ok (Bertie.Tls13utils.impl__Bytes__slice cert
              (offset +! sz 1 <: usize)
              (len -! sz 1 <: usize)
            <:
            Bertie.Tls13utils.t_Bytes)))

let rsa_public_key (cert: Bertie.Tls13utils.t_Bytes) (indices: t_CertificateKey)
    : Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let CertificateKey offset v__len:t_CertificateKey
      =
        indices
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 48uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist514:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist514)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, v__seq_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist515:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist515)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 2uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist516:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist516)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, int_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist517:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist517)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let n:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__slice cert offset int_len in
      let offset:usize = offset +! int_len in
      let* _:Prims.unit =
        match
          Core.Ops.Try_trait.f_branch (check_tag cert offset 2uy
              <:
              Core.Result.t_Result Prims.unit u8)
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist518:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist518)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      let offset:usize = offset +! sz 1 in
      let* offset, int_len:(usize & usize) =
        match
          Core.Ops.Try_trait.f_branch (length cert offset <: Core.Result.t_Result (usize & usize) u8
            )
        with
        | Core.Ops.Control_flow.ControlFlow_Break residual ->
          let* hoist519:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist519)
        | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
          Core.Ops.Control_flow.ControlFlow_Continue v_val
      in
      Core.Ops.Control_flow.ControlFlow_Continue
      (let e:Bertie.Tls13utils.t_Bytes = Bertie.Tls13utils.impl__Bytes__slice cert offset int_len in
        Core.Result.Result.v_Ok (n, e)))

let cert_public_key
      (cert: Bertie.Tls13utils.t_Bytes)
      (spki: (Bertie.Tls13crypto.t_SignatureScheme & t_CertificateKey))
    : Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8 =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (match spki._1 with
      | Bertie.Tls13crypto.SignatureScheme_ED25519  ->
        Core.Ops.Control_flow.ControlFlow_Continue
        (asn1err v_ASN1_UNSUPPORTED_ALGORITHM
          <:
          Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
      | Bertie.Tls13crypto.SignatureScheme_EcdsaSecp256r1Sha256  ->
        let* pk:Bertie.Tls13utils.t_Bytes =
          match
            Core.Ops.Try_trait.f_branch (ecdsa_public_key cert spki._2
                <:
                Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist520:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist520)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok (Bertie.Tls13crypto.PublicVerificationKey_EcDsa pk))
      | Bertie.Tls13crypto.SignatureScheme_RsaPssRsaSha256  ->
        let* pk:(Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) =
          match
            Core.Ops.Try_trait.f_branch (rsa_public_key cert spki._2
                <:
                Core.Result.t_Result (Bertie.Tls13utils.t_Bytes & Bertie.Tls13utils.t_Bytes) u8)
          with
          | Core.Ops.Control_flow.ControlFlow_Break residual ->
            let* hoist521:Rust_primitives.Hax.t_Never =
              Core.Ops.Control_flow.ControlFlow.v_Break (Core.Ops.Try_trait.f_from_residual residual
                  <:
                  Core.Result.t_Result Bertie.Tls13crypto.t_PublicVerificationKey u8)
            in
            Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist521)
          | Core.Ops.Control_flow.ControlFlow_Continue v_val ->
            Core.Ops.Control_flow.ControlFlow_Continue v_val
        in
        Core.Ops.Control_flow.ControlFlow_Continue
        (Core.Result.Result.v_Ok (Bertie.Tls13crypto.PublicVerificationKey_Rsa pk)))