module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Error = | Error_UnknownCiphersuite : Alloc.String.t_String -> t_Error

unfold
let t_TLSError = u8

unfold
let t_U16 = u16

unfold
let t_U32 = u32

unfold
let t_U8 = u8

let v_APPLICATION_DATA_INSTEAD_OF_HANDSHAKE: u8 = 138uy

let v_CRYPTO_ERROR: u8 = 2uy

let v_DECODE_ERROR: u8 = 142uy

let v_GOT_HANDSHAKE_FAILURE_ALERT: u8 = 141uy

let v_INCORRECT_ARRAY_LENGTH: u8 = 4uy

let v_INCORRECT_STATE: u8 = 128uy

let v_INSUFFICIENT_DATA: u8 = 134uy

let v_INSUFFICIENT_ENTROPY: u8 = 3uy

let v_INVALID_COMPRESSION_LIST: u8 = 136uy

let v_INVALID_SIGNATURE: u8 = 140uy

let v_MISSING_KEY_SHARE: u8 = 139uy

let v_NEGOTIATION_MISMATCH: u8 = 132uy

let v_PARSE_FAILED: u8 = 133uy

let v_PAYLOAD_TOO_LONG: u8 = 130uy

let v_PROTOCOL_VERSION_ALERT: u8 = 137uy

let v_PSK_MODE_MISMATCH: u8 = 131uy

let v_U16 (x: u16) : u16 = x

let v_U32 (x: u32) : u32 = x

let v_U8 (x: u8) : u8 = x

let v_UNSUPPORTED: u8 = 135uy

let v_UNSUPPORTED_ALGORITHM: u8 = 1uy

let v_ZERO_RTT_DISABLED: u8 = 129uy

let parse_failed (_: Prims.unit) : u8 = v_PARSE_FAILED

class t_Declassify (v_Self: Type) (v_T: Type) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_1031284672:Core.Marker.t_Sized v_T;
  f_declassify:v_Self -> v_T
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Declassify u8 u8 = { f_declassify = fun (self: u8) -> self }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_Declassify u32 u32 = { f_declassify = fun (self: u32) -> self }

let eq1 (b1 b2: u8) : bool = (f_declassify b1 <: u8) =. (f_declassify b2 <: u8)

let u32_from_be_bytes (v_val: t_Array u8 (sz 4)) : u32 =
  let v_val:u32 = Core.Num.impl__u32__from_be_bytes v_val in
  v_U32 v_val

let u16_as_be_bytes (v_val: u16) : t_Array u8 (sz 2) =
  let v_val:t_Array u8 (sz 2) = Core.Num.impl__u16__to_be_bytes v_val in
  let list = [v_U8 (v_val.[ sz 0 ] <: u8); v_U8 (v_val.[ sz 1 ] <: u8)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list list

let u32_as_be_bytes (v_val: u32) : t_Array u8 (sz 4) =
  let v_val:t_Array u8 (sz 4) = Core.Num.impl__u32__to_be_bytes v_val in
  let list =
    [
      v_U8 (v_val.[ sz 0 ] <: u8);
      v_U8 (v_val.[ sz 1 ] <: u8);
      v_U8 (v_val.[ sz 2 ] <: u8);
      v_U8 (v_val.[ sz 3 ] <: u8)
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  Rust_primitives.Hax.array_of_list list

let check (b: bool) : Core.Result.t_Result Prims.unit u8 =
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let check_eq1 (b1 b2: u8) : Core.Result.t_Result Prims.unit u8 =
  if eq1 b1 b2
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let length_u16_encoded_slice (bytes: t_Slice u8) : Core.Result.t_Result usize u8 =
  if (Core.Slice.impl__len bytes <: usize) <. sz 2
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l0:usize = cast (f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize in
    let l1:usize = cast (f_declassify (bytes.[ sz 1 ] <: u8) <: u8) <: usize in
    let l:usize = (l0 *! sz 256 <: usize) +! l1 in
    if ((Core.Slice.impl__len bytes <: usize) -! sz 2 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let length_u16_encoded (bytes: t_Slice u8) : Core.Result.t_Result usize u8 =
  length_u16_encoded_slice bytes

let length_u24_encoded (bytes: t_Slice u8) : Core.Result.t_Result usize u8 =
  if (Core.Slice.impl__len bytes <: usize) <. sz 3
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l0:usize = cast (f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize in
    let l1:usize = cast (f_declassify (bytes.[ sz 1 ] <: u8) <: u8) <: usize in
    let l2:usize = cast (f_declassify (bytes.[ sz 2 ] <: u8) <: u8) <: usize in
    let l:usize = ((l0 *! sz 65536 <: usize) +! (l1 *! sz 256 <: usize) <: usize) +! l2 in
    if ((Core.Slice.impl__len bytes <: usize) -! sz 3 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let length_u8_encoded (bytes: t_Slice u8) : Core.Result.t_Result usize u8 =
  if Core.Slice.impl__is_empty bytes
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l:usize = cast (f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize in
    if ((Core.Slice.impl__len bytes <: usize) -! sz 1 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let check_length_encoding_u16_slice (bytes: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist1:usize =
        Core.Result.impl__map_err (length_u16_encoded bytes <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist2:usize = hoist1 +! sz 2 in
        let hoist3:bool = hoist2 <>. (Core.Slice.impl__len bytes <: usize) in
        if hoist3
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let check_length_encoding_u24 (bytes: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist4:usize =
        Core.Result.impl__map_err (length_u24_encoded bytes <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist5:usize = hoist4 +! sz 3 in
        let hoist6:bool = hoist5 <>. (Core.Slice.impl__len bytes <: usize) in
        if hoist6
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let check_length_encoding_u8_slice (bytes: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let| hoist7:usize =
        Core.Result.impl__map_err (length_u8_encoded bytes <: Core.Result.t_Result usize u8)
          (Core.Convert.f_from <: u8 -> u8)
      in
      Core.Result.Result_Ok
      (let hoist8:usize = hoist7 +! sz 1 in
        let hoist9:bool = hoist8 <>. (Core.Slice.impl__len bytes <: usize) in
        if hoist9
        then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
        else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8)
      <:
      Core.Result.t_Result (Core.Result.t_Result Prims.unit u8) u8)

let eq_slice (b1 b2: t_Slice u8) : bool =
  if (Core.Slice.impl__len b1 <: usize) <>. (Core.Slice.impl__len b2 <: usize)
  then false
  else
    let (b: bool):bool = true in
    let b:bool =
      Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len b1 <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Core.Ops.Range.t_Range usize)
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            if ~.(eq1 (b1.[ i ] <: u8) (b2.[ i ] <: u8) <: bool) <: bool
            then
              let b:bool = false in
              b
            else b)
    in
    b

let check_eq_slice (b1 b2: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  let b:bool = eq_slice b1 b2 in
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let check_mem (b1 b2: t_Slice u8) : Core.Result.t_Result Prims.unit u8 =
  if ((Core.Slice.impl__len b2 <: usize) %! (Core.Slice.impl__len b1 <: usize) <: usize) <>. sz 0
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
  else
    let b:bool = false in
    let b:bool =
      Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end
                =
                (Core.Slice.impl__len b2 <: usize) /! (Core.Slice.impl__len b1 <: usize) <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
          <:
          Core.Ops.Range.t_Range usize)
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            if
              eq_slice b1
                (b2.[ {
                      Core.Ops.Range.f_start = i *! (Core.Slice.impl__len b1 <: usize) <: usize;
                      Core.Ops.Range.f_end
                      =
                      (i +! sz 1 <: usize) *! (Core.Slice.impl__len b1 <: usize) <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              bool
            then
              let b:bool = true in
              b
            else b)
    in
    if b
    then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
    else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let error_string (c: u8) : Alloc.String.t_String =
  Alloc.Fmt.format (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list list)
          <:
          t_Slice string)
        (Rust_primitives.unsize (let list =
                [Core.Fmt.Rt.impl_1__new_display c <: Core.Fmt.Rt.t_Argument]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list list)
          <:
          t_Slice Core.Fmt.Rt.t_Argument)
      <:
      Core.Fmt.t_Arguments)

let tlserr
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Marker.t_Sized v_T)
      (err: u8)
    : Core.Result.t_Result v_T u8 =
  let bt:Backtrace.Capture.t_Backtrace = Backtrace.Capture.impl__Backtrace__new () in
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
  Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

type t_Bytes = | Bytes : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  { f_from = fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> Bytes x <: t_Bytes }

let impl__Bytes__as_raw (self: t_Bytes) : t_Slice u8 = Core.Ops.Deref.f_deref self._0

let impl__Bytes__declassify (self: t_Bytes) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
                self._0
              <:
              t_Slice u8)
          <:
          Core.Slice.Iter.t_Iter u8)
        (fun x ->
            let x:u8 = x in
            f_declassify x <: u8)
      <:
      Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))

let impl__Bytes__into_raw (self: t_Bytes) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = self._0

let impl__Bytes__declassify_array (self: t_Bytes) : Core.Result.t_Result (t_Array u8 v_C) u8 =
  Core.Result.impl__map_err (Core.Convert.f_try_into (impl__Bytes__declassify self
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      Core.Result.t_Result (t_Array u8 v_C) (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    (fun temp_0_ ->
        let _:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = temp_0_ in
        v_INCORRECT_ARRAY_LENGTH)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From t_Bytes (t_Slice u8) =
  {
    f_from
    =
    fun (x: t_Slice u8) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec x <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_C: usize) : Core.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core.Convert.f_into (Alloc.Slice.impl__to_vec (Rust_primitives.unsize x <: t_Slice u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Index.t_Index t_Bytes usize =
  { f_Output = u8; f_index = fun (self: t_Bytes) (x: usize) -> self._0.[ x ] }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Index.t_Index t_Bytes (Core.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice u8;
    f_index = fun (self: t_Bytes) (x: Core.Ops.Range.t_Range usize) -> self._0.[ x ]
  }

let impl__Bytes__append (self x: t_Bytes) : t_Bytes =
  let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  =
    Alloc.Vec.impl_1__append self._0 x._0
  in
  let self:t_Bytes = { self with _0 = tmp0 } <: t_Bytes in
  let x:t_Bytes = { x with _0 = tmp1 } <: t_Bytes in
  let hax_temp_output:Prims.unit = () in
  self

let impl__Bytes__concat (self other: t_Bytes) : t_Bytes =
  let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  =
    Alloc.Vec.impl_1__append self._0 other._0
  in
  let self:t_Bytes = { self with _0 = tmp0 } <: t_Bytes in
  let other:t_Bytes = { other with _0 = tmp1 } <: t_Bytes in
  let _:Prims.unit = () in
  self

let impl__Bytes__concat_array (self: t_Bytes) (other: t_Array u8 v_N) : t_Bytes =
  let self:t_Bytes =
    {
      self with
      _0 = Alloc.Vec.impl_2__extend_from_slice self._0 (Rust_primitives.unsize other <: t_Slice u8)
    }
    <:
    t_Bytes
  in
  self

let impl__Bytes__extend_from_slice (self x: t_Bytes) : t_Bytes =
  let hax_temp_output, self:(Prims.unit & t_Bytes) =
    (),
    ({
        self with
        _0 = Alloc.Vec.impl_2__extend_from_slice self._0 (Core.Ops.Deref.f_deref x._0 <: t_Slice u8)
      }
      <:
      t_Bytes)
    <:
    (Prims.unit & t_Bytes)
  in
  self

let impl__Bytes__from_hex (s: string) : t_Bytes =
  let (s: Alloc.String.t_String):Alloc.String.t_String =
    Core.Iter.Traits.Iterator.f_collect (Core.Str.impl__str__split_whitespace s
        <:
        Core.Str.Iter.t_SplitWhitespace)
  in
  if ((Alloc.String.impl__String__len s <: usize) %! sz 2 <: usize) =. sz 0
  then
    Bytes
    (Core.Option.impl__expect (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (
                  Core.Iter.Traits.Iterator.f_step_by ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Alloc.String.impl__String__len s <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                    (sz 2)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
                (fun i ->
                    let i:usize = i in
                    Core.Option.impl__and_then (Core.Str.impl__str__get (Core.Ops.Deref.f_deref s
                            <:
                            string)
                          ({ Core.Ops.Range.f_start = i; Core.Ops.Range.f_end = i +! sz 2 <: usize }
                            <:
                            Core.Ops.Range.t_Range usize)
                        <:
                        Core.Option.t_Option string)
                      (fun sub ->
                          let sub:string = sub in
                          Core.Option.impl__map (Core.Result.impl__ok (Core.Num.impl__u8__from_str_radix
                                    sub
                                    16ul
                                  <:
                                  Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError)
                              <:
                              Core.Option.t_Option u8)
                            v_U8
                          <:
                          Core.Option.t_Option u8)
                    <:
                    Core.Option.t_Option u8)
              <:
              Core.Iter.Adapters.Map.t_Map
                (Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
                (usize -> Core.Option.t_Option u8))
          <:
          Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
        "Not a hex string1")
    <:
    t_Bytes
  else
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize
                  (let list = ["internal error: entered unreachable code: Not a hex string2"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list list)
                <:
                t_Slice string)
              (Rust_primitives.unsize (Core.Fmt.Rt.impl_1__none ()
                    <:
                    t_Array Core.Fmt.Rt.t_Argument (sz 0))
                <:
                t_Slice Core.Fmt.Rt.t_Argument)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)

let impl__Bytes__from_slice (s: t_Slice u8) : t_Bytes = Core.Convert.f_into s

let impl__Bytes__len (self: t_Bytes) : usize = Alloc.Vec.impl_1__len self._0

let impl__Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8) : t_Bytes =
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity ((Core.Slice.impl__len prefix <: usize) +!
        (impl__Bytes__len self <: usize)
        <:
        usize)
  in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice out prefix
  in
  let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  =
    Alloc.Vec.impl_1__append out self._0
  in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = tmp0 in
  let self:t_Bytes = { self with _0 = tmp1 } <: t_Bytes in
  let _:Prims.unit = () in
  Bytes out <: t_Bytes

let impl__Bytes__new (_: Prims.unit) : t_Bytes = Bytes (Alloc.Vec.impl__new ()) <: t_Bytes

let impl__Bytes__new_alloc (len: usize) : t_Bytes =
  Bytes (Alloc.Vec.impl__with_capacity len) <: t_Bytes

let impl__Bytes__push (self: t_Bytes) (x: u8) : t_Bytes =
  let hax_temp_output, self:(Prims.unit & t_Bytes) =
    (), ({ self with _0 = Alloc.Vec.impl_1__push self._0 x } <: t_Bytes) <: (Prims.unit & t_Bytes)
  in
  self

let impl__Bytes__raw_slice (self: t_Bytes) (range: Core.Ops.Range.t_Range usize) : t_Slice u8 =
  self._0.[ range ]

let impl__Bytes__slice (self: t_Bytes) (start len: usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)

let impl__Bytes__slice_range (self: t_Bytes) (range: Core.Ops.Range.t_Range usize) : t_Bytes =
  Core.Convert.f_into (self._0.[ range ] <: t_Slice u8)

let impl__Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize)
    : t_Bytes =
  let res:t_Bytes = Core.Clone.f_clone self in
  let res:t_Bytes =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = len
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      res
      (fun res i ->
          let res:t_Bytes = res in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
            (start +! i <: usize)
            (other.[ beg +! i <: usize ] <: u8)
          <:
          t_Bytes)
  in
  res

let impl__Bytes__zeroes (len: usize) : t_Bytes =
  Bytes (Alloc.Vec.from_elem (v_U8 0uy <: u8) len) <: t_Bytes

let bytes (x: t_Slice u8) : t_Bytes = Core.Convert.f_into x

let bytes1 (x: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list list)

let bytes2 (x y: u8) : t_Bytes =
  Core.Convert.f_into (let list = [x; y] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list list)

let check_eq (b1 b2: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  check_eq_slice (impl__Bytes__as_raw b1 <: t_Slice u8) (impl__Bytes__as_raw b2 <: t_Slice u8)

let check_length_encoding_u16 (bytes: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  check_length_encoding_u16_slice (impl__Bytes__as_raw bytes <: t_Slice u8)

let check_length_encoding_u8 (bytes: t_Bytes) : Core.Result.t_Result Prims.unit u8 =
  check_length_encoding_u8_slice (impl__Bytes__as_raw bytes <: t_Slice u8)

let encode_length_u16 (bytes: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len bytes in
  if len >=. sz 65536
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let len:t_Array u8 (sz 2) = u16_as_be_bytes (v_U16 (cast (len <: usize) <: u16) <: u16) in
    let lenb:t_Bytes =
      impl__Bytes__new_alloc (sz 2 +! (impl__Bytes__len bytes <: usize) <: usize)
    in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 0 ] <: u8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: u8) in
    let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
      Alloc.Vec.impl_1__append lenb._0 bytes._0
    in
    let lenb:t_Bytes = { lenb with _0 = tmp0 } <: t_Bytes in
    let bytes:t_Bytes = { bytes with _0 = tmp1 } <: t_Bytes in
    let _:Prims.unit = () in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let encode_length_u24 (bytes: t_Bytes) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = impl__Bytes__len bytes in
  if len >=. sz 16777216
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let len:t_Array u8 (sz 4) = u32_as_be_bytes (v_U32 (cast (len <: usize) <: u32) <: u32) in
    let lenb:t_Bytes =
      impl__Bytes__new_alloc (sz 3 +! (impl__Bytes__len bytes <: usize) <: usize)
    in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: u8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 2 ] <: u8) in
    let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 3 ] <: u8) in
    let lenb:t_Bytes = impl__Bytes__extend_from_slice lenb bytes in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let encode_length_u8 (bytes: t_Slice u8) : Core.Result.t_Result t_Bytes u8 =
  let len:usize = Core.Slice.impl__len bytes in
  if len >=. sz 256
  then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  else
    let lenb:t_Bytes =
      impl__Bytes__new_alloc (sz 1 +! (Core.Slice.impl__len bytes <: usize) <: usize)
    in
    let lenb:t_Bytes = impl__Bytes__push lenb (v_U8 (cast (len <: usize) <: u8) <: u8) in
    let lenb:t_Bytes =
      { lenb with _0 = Alloc.Vec.impl_2__extend_from_slice lenb._0 bytes } <: t_Bytes
    in
    Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let eq (b1 b2: t_Bytes) : bool =
  eq_slice (Core.Ops.Deref.f_deref b1._0 <: t_Slice u8) (Core.Ops.Deref.f_deref b2._0 <: t_Slice u8)

let random_bytes (len: usize) : t_Bytes =
  Core.Convert.f_into (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map ({
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = len
              }
              <:
              Core.Ops.Range.t_Range usize)
            (fun temp_0_ ->
                let _:usize = temp_0_ in
                Rand.random () <: u8)
          <:
          Core.Iter.Adapters.Map.t_Map (Core.Ops.Range.t_Range usize) (usize -> u8))
      <:
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

type t_AppData = | AppData : t_Bytes -> t_AppData

let impl__AppData__as_raw (self: t_AppData) : t_Bytes = self._0

let impl__AppData__into_raw (self: t_AppData) : t_Bytes = self._0

let impl__AppData__new (b: t_Bytes) : t_AppData = AppData b <: t_AppData

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_AppData (t_Slice u8) =
  { f_from = fun (value: t_Slice u8) -> AppData (Core.Convert.f_into value) <: t_AppData }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13 (v_N: usize) : Core.Convert.t_From t_AppData (t_Array u8 v_N) =
  { f_from = fun (value: t_Array u8 v_N) -> AppData (Core.Convert.f_into value) <: t_AppData }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from
    =
    fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
      AppData (Core.Convert.f_into value) <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From t_AppData t_Bytes =
  { f_from = fun (value: t_Bytes) -> AppData value <: t_AppData }
