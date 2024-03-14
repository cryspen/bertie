module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_U16 (x: u16) = x

let v_U32 (x: u32) = x

let v_U8 (x: u8) = x

let dummy_fn (_: Prims.unit) = v_PAYLOAD_TOO_LONG

let parse_failed (_: Prims.unit) = v_PARSE_FAILED

let eq1 (b1 b2: u8) = (f_declassify b1 <: u8) =. (f_declassify b2 <: u8)

let u32_from_be_bytes (v_val: t_Array u8 (sz 4)) =
  let v_val:u32 = Core.Num.impl__u32__from_be_bytes v_val in
  v_U32 v_val

let u16_as_be_bytes (v_val: u16) =
  let v_val:t_Array u8 (sz 2) = Core.Num.impl__u16__to_be_bytes v_val in
  let list = [v_U8 (v_val.[ sz 0 ] <: u8); v_U8 (v_val.[ sz 1 ] <: u8)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let u32_as_be_bytes (v_val: u32) =
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
  Rust_primitives.Hax.array_of_list 4 list

let check (b: bool) =
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let check_eq1 (b1 b2: u8) =
  if eq1 b1 b2
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let length_u16_encoded_slice (bytes: t_Slice u8) =
  if (Core.Slice.impl__len bytes <: usize) <. sz 2
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l0:usize = cast (f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize in
    let l1:usize = cast (f_declassify (bytes.[ sz 1 ] <: u8) <: u8) <: usize in
    let l:usize = (l0 *! sz 256 <: usize) +! l1 in
    if ((Core.Slice.impl__len bytes <: usize) -! sz 2 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let length_u16_encoded (bytes: t_Slice u8) = length_u16_encoded_slice bytes

let length_u24_encoded (bytes: t_Slice u8) =
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

let length_u8_encoded (bytes: t_Slice u8) =
  if Core.Slice.impl__is_empty bytes
  then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
  else
    let l:usize = cast (f_declassify (bytes.[ sz 0 ] <: u8) <: u8) <: usize in
    if ((Core.Slice.impl__len bytes <: usize) -! sz 1 <: usize) <. l
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result usize u8
    else Core.Result.Result_Ok l <: Core.Result.t_Result usize u8

let check_length_encoding_u16_slice (bytes: t_Slice u8) =
  match length_u16_encoded bytes with
  | Core.Result.Result_Ok hoist1 ->
    if (hoist1 +! sz 2 <: usize) <>. (Core.Slice.impl__len bytes <: usize)
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
    else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let check_length_encoding_u24 (bytes: t_Slice u8) =
  match length_u24_encoded bytes with
  | Core.Result.Result_Ok hoist4 ->
    if (hoist4 +! sz 3 <: usize) <>. (Core.Slice.impl__len bytes <: usize)
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
    else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let check_length_encoding_u8_slice (bytes: t_Slice u8) =
  match length_u8_encoded bytes with
  | Core.Result.Result_Ok hoist7 ->
    if (hoist7 +! sz 1 <: usize) <>. (Core.Slice.impl__len bytes <: usize)
    then Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8
    else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit u8

let eq_slice (b1 b2: t_Slice u8) =
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

let check_eq_slice (b1 b2: t_Slice u8) =
  let b:bool = eq_slice b1 b2 in
  if b
  then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
  else Core.Result.Result_Err (parse_failed ()) <: Core.Result.t_Result Prims.unit u8

let check_mem (b1 b2: t_Slice u8) =
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

let error_string (c: u8) =
  Alloc.Fmt.format (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice string)
        (Rust_primitives.unsize (let list =
                [Core.Fmt.Rt.impl_1__new_display c <: Core.Fmt.Rt.t_Argument]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          t_Slice Core.Fmt.Rt.t_Argument)
      <:
      Core.Fmt.t_Arguments)

let tlserr (#v_T: Type) (err: u8) =
  // let bt:Backtrace.Capture.t_Backtrace = Backtrace.Capture.impl__Backtrace__new () in
  // let _:Prims.unit =
  //   Std.Io.Stdio.v__print (Core.Fmt.impl_2__new_v1 (Rust_primitives.unsize (let list = [""; "\n"] in
  //               FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  //               Rust_primitives.Hax.array_of_list 2 list)
  //           <:
  //           t_Slice string)
  //         (Rust_primitives.unsize (let list =
  //                 [Core.Fmt.Rt.impl_1__new_debug bt <: Core.Fmt.Rt.t_Argument]
  //               in
  //               FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
  //               Rust_primitives.Hax.array_of_list 1 list)
  //           <:
  //           t_Slice Core.Fmt.Rt.t_Argument)
  //       <:
  //       Core.Fmt.t_Arguments)
  // in
  // let _:Prims.unit = () in
  Core.Result.Result_Err err <: Core.Result.t_Result v_T u8

let impl__Bytes__as_raw (self: t_Bytes) = Core.Ops.Deref.f_deref self._0

let impl__Bytes__declassify (self: t_Bytes) =
  admit ()
  // Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map (Core.Slice.impl__iter (Core.Ops.Deref.f_deref
  //               self._0
  //             <:
  //             t_Slice u8)
  //         <:
  //         Core.Slice.Iter.t_Iter u8)
  //       (fun x ->
  //           let x:u8 = x in
  //           f_declassify x <: u8)
  //     <:
  //     Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter u8) (u8 -> u8))

let impl__Bytes__into_raw (self: t_Bytes) = self._0

let impl__Bytes__declassify_array (v_C: usize) (self: t_Bytes) =
  Core.Result.impl__map_err (Core.Convert.f_try_into (impl__Bytes__declassify self
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      Core.Result.t_Result (t_Array u8 v_C) (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    (fun temp_0_ ->
        let _:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = temp_0_ in
        v_INCORRECT_ARRAY_LENGTH)

let impl__Bytes__append (self x: t_Bytes) =
    admit ()
  //   Alloc.Vec.impl_1__append self._0 x._0
  // in
  // let self:t_Bytes = { self with _0 = tmp0 } <: t_Bytes in
  // let x:t_Bytes = { x with _0 = tmp1 } <: t_Bytes in
  // let hax_temp_output:Prims.unit = () in
  // self

let impl__Bytes__concat (self other: t_Bytes) =
  admit ()
  // let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  // =
  //   Alloc.Vec.impl_1__append self._0 other._0
  // in
  // let self:t_Bytes = { self with _0 = tmp0 } <: t_Bytes in
  // let other:t_Bytes = { other with _0 = tmp1 } <: t_Bytes in
  // let _:Prims.unit = () in
  // self

let impl__Bytes__concat_array (v_N: usize) (self: t_Bytes) (other: t_Array u8 v_N) =
  let self:t_Bytes =
    {
      self with
      _0 = Alloc.Vec.impl_2__extend_from_slice self._0 (Rust_primitives.unsize other <: t_Slice u8)
    }
    <:
    t_Bytes
  in
  self

let impl__Bytes__extend_from_slice (self x: t_Bytes) =
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

let impl__Bytes__from_hex (s: string) =
  admit ()

let impl__Bytes__from_slice (s: t_Slice u8) = Core.Convert.f_into s

let impl__Bytes__len (self: t_Bytes) = Alloc.Vec.impl_1__len self._0

let impl__Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8) =
  admit ()
  // let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  //   Alloc.Vec.impl__with_capacity ((Core.Slice.impl__len prefix <: usize) +!
  //       (impl__Bytes__len self <: usize)
  //       <:
  //       usize)
  // in
  // let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  //   Alloc.Vec.impl_2__extend_from_slice out prefix
  // in
  // let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  // =
  //   Alloc.Vec.impl_1__append out self._0
  // in
  // let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = tmp0 in
  // let self:t_Bytes = { self with _0 = tmp1 } <: t_Bytes in
  // let _:Prims.unit = () in
  // Bytes out <: t_Bytes

let impl__Bytes__new (_: Prims.unit) = Bytes (Alloc.Vec.impl__new ()) <: t_Bytes

let impl__Bytes__new_alloc (len: usize) = Bytes (Alloc.Vec.impl__with_capacity len) <: t_Bytes

let impl__Bytes__push (self: t_Bytes) (x: u8) =
  let hax_temp_output, self:(Prims.unit & t_Bytes) =
    (), ({ self with _0 = Alloc.Vec.impl_1__push self._0 x } <: t_Bytes) <: (Prims.unit & t_Bytes)
  in
  self

let impl__Bytes__raw_slice (self: t_Bytes) (range: Core.Ops.Range.t_Range usize) = self._0.[ range ]

let impl__Bytes__slice (self: t_Bytes) (start len: usize) =
  Core.Convert.f_into (self._0.[ {
          Core.Ops.Range.f_start = start;
          Core.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)

let impl__Bytes__slice_range (self: t_Bytes) (range: Core.Ops.Range.t_Range usize) =
  Core.Convert.f_into (self._0.[ range ] <: t_Slice u8)

let impl__Bytes__zeroes (len: usize) = Bytes (Alloc.Vec.from_elem (v_U8 0uy <: u8) len) <: t_Bytes

let impl__Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize) =
  admit ()
  // let res:t_Bytes = Core.Clone.f_clone self in
  // let res:t_Bytes =
  //   Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
  //             Core.Ops.Range.f_start = sz 0;
  //             Core.Ops.Range.f_end = len
  //           }
  //           <:
  //           Core.Ops.Range.t_Range usize)
  //       <:
  //       Core.Ops.Range.t_Range usize)
  //     res
  //     (fun res i ->
  //         let res:t_Bytes = res in
  //         let i:usize = i in
  //         Rust_primitives.Hax.update_at res
  //           (start +! i <: usize)
  //           (other.[ beg +! i <: usize ] <: u8)
  //         <:
  //         t_Bytes)
  // in
  // res

let bytes (x: t_Slice u8) = Core.Convert.f_into x

let bytes1 (x: u8) =
  Core.Convert.f_into (let list = [x] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list)

let bytes2 (x y: u8) =
  Core.Convert.f_into (let list = [x; y] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list 2 list)

let check_eq (b1 b2: t_Bytes) =
  check_eq_slice (impl__Bytes__as_raw b1 <: t_Slice u8) (impl__Bytes__as_raw b2 <: t_Slice u8)

let check_length_encoding_u16 (bytes: t_Bytes) =
  check_length_encoding_u16_slice (impl__Bytes__as_raw bytes <: t_Slice u8)

let check_length_encoding_u8 (bytes: t_Bytes) =
  check_length_encoding_u8_slice (impl__Bytes__as_raw bytes <: t_Slice u8)

let encode_length_u16 (bytes: t_Bytes) =
  admit ()
  // let len:usize = impl__Bytes__len bytes in
  // if len >=. sz 65536
  // then Core.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core.Result.t_Result t_Bytes u8
  // else
  //   let len:t_Array u8 (sz 2) = u16_as_be_bytes (v_U16 (cast (len <: usize) <: u16) <: u16) in
  //   let lenb:t_Bytes =
  //     impl__Bytes__new_alloc (sz 2 +! (impl__Bytes__len bytes <: usize) <: usize)
  //   in
  //   let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 0 ] <: u8) in
  //   let lenb:t_Bytes = impl__Bytes__push lenb (len.[ sz 1 ] <: u8) in
  //   let tmp0, tmp1:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
  //     Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  //     Alloc.Vec.impl_1__append lenb._0 bytes._0
  //   in
  //   let lenb:t_Bytes = { lenb with _0 = tmp0 } <: t_Bytes in
  //   let bytes:t_Bytes = { bytes with _0 = tmp1 } <: t_Bytes in
  //   let _:Prims.unit = () in
  //   Core.Result.Result_Ok lenb <: Core.Result.t_Result t_Bytes u8

let encode_length_u24 (bytes: t_Bytes) =
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

let encode_length_u8 (bytes: t_Slice u8) =
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

let eq (b1 b2: t_Bytes) =
  eq_slice (Core.Ops.Deref.f_deref b1._0 <: t_Slice u8) (Core.Ops.Deref.f_deref b2._0 <: t_Slice u8)

let random_bytes (len: usize) =
  admit ()
  // Core.Convert.f_into (Core.Iter.Traits.Iterator.f_collect (Core.Iter.Traits.Iterator.f_map ({
  //               Core.Ops.Range.f_start = sz 0;
  //               Core.Ops.Range.f_end = len
  //             }
  //             <:
  //             Core.Ops.Range.t_Range usize)
  //           (fun temp_0_ ->
  //               let _:usize = temp_0_ in
  //               Rand.random () <: u8)
  //         <:
  //         Core.Iter.Adapters.Map.t_Map (Core.Ops.Range.t_Range usize) (usize -> u8))
  //     <:
  //     Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let impl__AppData__as_raw (self: t_AppData) = self._0

let impl__AppData__into_raw (self: t_AppData) = self._0

let impl__AppData__new (b: t_Bytes) = AppData b <: t_AppData
