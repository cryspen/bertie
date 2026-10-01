module Bertie.Tls13utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Fmt.t_Debug t_Error

let impl_10 = impl_10'

let parse_failed (_: Prims.unit) = v_PARSE_FAILED

let error_string (c: u8) =
  let args:u8 = c <: u8 in
  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 1) =
    let list = [Core_models.Fmt.Rt.impl__new_display #u8 args] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  Core_models.Hint.must_use #Alloc.String.t_String
    (Alloc.Fmt.format (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
            (mk_usize 1)
            (let list = [""] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
            args
          <:
          Core_models.Fmt.t_Arguments)
      <:
      Alloc.String.t_String)

let tlserr (#v_T: Type0) (err: u8) =
  Core_models.Result.Result_Err err <: Core_models.Result.t_Result v_T u8

let v_U8 (x: u8) = x

let v_U16 (x: u16) = x

let v_U32 (x: u32) = x

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core_models.Marker.t_StructuralPartialEq t_Bytes

let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core_models.Cmp.t_PartialEq t_Bytes t_Bytes

let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core_models.Fmt.t_Debug t_Bytes

let impl_15 = impl_15'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core_models.Default.t_Default t_Bytes

let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Convert.t_From t_Bytes (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from_pre = (fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> true);
    f_from_post = (fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (out: t_Bytes) -> true);
    f_from = fun (x: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> Bytes x <: t_Bytes
  }

let assume_no_alloc_overflow (len extra: usize) =
  let _:Prims.unit =
    Hax_lib.v_assume (b2t
        (((Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int) +
            (Rust_primitives.Hax.Int.from_machine extra <: Hax_lib.Int.t_Int)
            <:
            Hax_lib.Int.t_Int) <=
          (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int
          )
          <:
          bool))
  in
  ()

let impl_Bytes__into_raw (self: t_Bytes) = self._0

let impl_Bytes__declassify (self: t_Bytes) =
  Core_models.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    #FStar.Tactics.Typeclasses.solve
    self._0

let impl_Bytes__as_raw (self: t_Bytes) = Alloc.Vec.impl_1__as_slice self._0

let impl_Bytes__declassify_array (v_C: usize) (self: t_Bytes) =
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = impl_Bytes__declassify self in
  if (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global bytes <: usize) =. v_C
  then
    let out:t_Array u8 v_C = Rust_primitives.Hax.repeat (mk_u8 0) v_C in
    let out:t_Array u8 v_C =
      Core_models.Slice.impl__copy_from_slice #u8
        out
        (Alloc.Vec.impl_1__as_slice bytes <: t_Slice u8)
    in
    Core_models.Result.Result_Ok out <: Core_models.Result.t_Result (t_Array u8 v_C) u8
  else
    Core_models.Result.Result_Err v_INCORRECT_ARRAY_LENGTH
    <:
    Core_models.Result.t_Result (t_Array u8 v_C) u8

let u16_as_be_bytes (v_val: u16) =
  let v_val:t_Array u8 (mk_usize 2) = Core_models.Num.impl_u16__to_be_bytes v_val in
  let list = [v_U8 (v_val.[ mk_usize 0 ] <: u8); v_U8 (v_val.[ mk_usize 1 ] <: u8)] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
  Rust_primitives.Hax.array_of_list 2 list

let u32_as_be_bytes (v_val: u32) =
  let v_val:t_Array u8 (mk_usize 4) = Core_models.Num.impl_u32__to_be_bytes v_val in
  let list =
    [
      v_U8 (v_val.[ mk_usize 0 ] <: u8);
      v_U8 (v_val.[ mk_usize 1 ] <: u8);
      v_U8 (v_val.[ mk_usize 2 ] <: u8);
      v_U8 (v_val.[ mk_usize 3 ] <: u8)
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  Rust_primitives.Hax.array_of_list 4 list

let u32_from_be_bytes (v_val: t_Array u8 (mk_usize 4)) =
  let v_val:u32 = Core_models.Num.impl_u32__from_be_bytes v_val in
  v_U32 v_val

let impl_Bytes__new (_: Prims.unit) = Bytes (Alloc.Vec.impl__new #u8 ()) <: t_Bytes

let impl_Bytes__new_alloc (len: usize) = Bytes (Alloc.Vec.impl__with_capacity #u8 len) <: t_Bytes

let impl_Bytes__zeroes (len: usize) =
  Bytes (Alloc.Vec.from_elem #u8 (v_U8 (mk_u8 0) <: u8) len) <: t_Bytes

let impl_Bytes__len (self: t_Bytes) = Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0

let impl_Bytes__prefix (self: t_Bytes) (prefix: t_Slice u8) =
  let _:Prims.unit =
    assume_no_alloc_overflow (Core_models.Slice.impl__len #u8 prefix <: usize)
      (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize)
  in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity #u8
      ((Core_models.Slice.impl__len #u8 prefix <: usize) +! (impl_Bytes__len self <: usize) <: usize
      )
  in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8 #Alloc.Alloc.t_Global out prefix
  in
  let out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      out
      (Alloc.Vec.impl_1__as_slice self._0 <: t_Slice u8)
  in
  Bytes out <: t_Bytes

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core_models.Convert.t_From t_Bytes (t_Slice u8) =
  {
    f_from_pre = (fun (x: t_Slice u8) -> true);
    f_from_post
    =
    (fun (x: t_Slice u8) (result: t_Bytes) ->
        (impl_Bytes__len result <: usize) =. (Core_models.Slice.impl__len #u8 x <: usize));
    f_from
    =
    fun (x: t_Slice u8) ->
      Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__to_vec #u8 x <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19 (v_C: usize) : Core_models.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from_pre = (fun (x: t_Array u8 v_C) -> true);
    f_from_post
    =
    (fun (x: t_Array u8 v_C) (result: t_Bytes) -> (impl_Bytes__len result <: usize) =. v_C);
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__to_vec #u8 (x <: t_Slice u8) <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20 (v_C: usize) : Core_models.Convert.t_From t_Bytes (t_Array u8 v_C) =
  {
    f_from_pre = (fun (x: t_Array u8 v_C) -> true);
    f_from_post
    =
    (fun (x: t_Array u8 v_C) (result: t_Bytes) -> (impl_Bytes__len result <: usize) =. v_C);
    f_from
    =
    fun (x: t_Array u8 v_C) ->
      Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #t_Bytes
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__to_vec #u8 (x <: t_Slice u8) <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  }

let bytes (x: t_Slice u8) =
  Core_models.Convert.f_into #(t_Slice u8) #t_Bytes #FStar.Tactics.Typeclasses.solve x

let bytes1 (x: u8) =
  Core_models.Convert.f_into #(t_Array u8 (mk_usize 1))
    #t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (let list = [x] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list)

let bytes2 (x y: u8) =
  Core_models.Convert.f_into #(t_Array u8 (mk_usize 2))
    #t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (let list = [x; y] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
      Rust_primitives.Hax.array_of_list 2 list)

let e_update_at_usize_bytes_test (b: t_Bytes) =
  let b:t_Bytes =
    if (impl_Bytes__len b <: usize) >. mk_usize 0
    then Rust_primitives.Hax.update_at b (mk_usize 0) (v_U8 (mk_u8 0) <: u8)
    else b
  in
  b

let impl_Bytes__from_slice (s: t_Slice u8) =
  Core_models.Convert.f_into #(t_Slice u8) #t_Bytes #FStar.Tactics.Typeclasses.solve s

let impl_Bytes__push (self: t_Bytes) (x: u8) =
  let _:Prims.unit =
    assume_no_alloc_overflow (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize)
      (mk_usize 1)
  in
  let self:t_Bytes =
    { self with _0 = Alloc.Vec.impl_1__push #u8 #Alloc.Alloc.t_Global self._0 x } <: t_Bytes
  in
  self

let impl_Bytes__extend_from_slice (self x: t_Bytes) =
  let _:Prims.unit =
    assume_no_alloc_overflow (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize)
      (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global x._0 <: usize)
  in
  let self:t_Bytes =
    {
      self with
      _0
      =
      Alloc.Vec.impl_2__extend_from_slice #u8
        #Alloc.Alloc.t_Global
        self._0
        (Alloc.Vec.impl_1__as_slice x._0 <: t_Slice u8)
    }
    <:
    t_Bytes
  in
  self

let concat_inner (bytes other: t_Bytes) =
  let result:t_Bytes = bytes in
  let result:t_Bytes = impl_Bytes__extend_from_slice result other in
  result

let impl_Bytes__append (self x: t_Bytes) =
  let _:Prims.unit =
    assume_no_alloc_overflow (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize)
      (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global x._0 <: usize)
  in
  let
  (tmp0: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global), (tmp1: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Alloc.Vec.impl_1__append #u8 #Alloc.Alloc.t_Global self._0 x._0
  in
  let self:t_Bytes = { self with _0 = tmp0 } <: t_Bytes in
  let x:t_Bytes = { x with _0 = tmp1 } <: t_Bytes in
  let _:Prims.unit = () in
  self

let impl_Bytes__raw_slice (self: t_Bytes) (range: Core_models.Ops.Range.t_Range usize) =
  self._0.[ range ]

let impl_Bytes__slice_range (self: t_Bytes) (range: Core_models.Ops.Range.t_Range usize) =
  Core_models.Convert.f_into #(t_Slice u8)
    #t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (self._0.[ range ] <: t_Slice u8)

let impl_Bytes__slice (self: t_Bytes) (start len: usize) =
  Core_models.Convert.f_into #(t_Slice u8)
    #t_Bytes
    #FStar.Tactics.Typeclasses.solve
    (self._0.[ {
          Core_models.Ops.Range.f_start = start;
          Core_models.Ops.Range.f_end = start +! len <: usize
        }
        <:
        Core_models.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)

let impl_Bytes__concat (self other: t_Bytes) = concat_inner self other

let impl_Bytes__concat_array (v_N: usize) (self: t_Bytes) (other: t_Array u8 v_N) =
  let _:Prims.unit =
    assume_no_alloc_overflow (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize) v_N
  in
  let self:t_Bytes =
    {
      self with
      _0
      =
      Alloc.Vec.impl_2__extend_from_slice #u8 #Alloc.Alloc.t_Global self._0 (other <: t_Slice u8)
    }
    <:
    t_Bytes
  in
  self

let impl_Bytes__update_slice (self: t_Bytes) (start: usize) (other: t_Bytes) (beg len: usize) =
  let res:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core_models.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      self._0
  in
  let res:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      len
      (fun res temp_1_ ->
          let res:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = res in
          let _:usize = temp_1_ in
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global res <: usize) =.
          (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self._0 <: usize)
          <:
          bool)
      res
      (fun res i ->
          let res:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = res in
          let i:usize = i in
          let res:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice
                      res
                    <:
                    t_Slice u8)
                  (start +! i <: usize)
                  (other._0.[ beg +! i <: usize ] <: u8)
                <:
                t_Slice u8)
          in
          res)
  in
  Bytes res <: t_Bytes

let check (b: bool) =
  if b
  then Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  else Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let encode_length_u8 (bytes: t_Slice u8) =
  let len:usize = Core_models.Slice.impl__len #u8 bytes in
  if len >=. mk_usize 256
  then Core_models.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core_models.Result.t_Result t_Bytes u8
  else
    let lenb:t_Bytes =
      impl_Bytes__new_alloc (mk_usize 1 +! (Core_models.Slice.impl__len #u8 bytes <: usize) <: usize
        )
    in
    let lenb:t_Bytes = impl_Bytes__push lenb (v_U8 (cast (len <: usize) <: u8) <: u8) in
    let lenb:t_Bytes =
      { lenb with _0 = Alloc.Vec.impl_2__extend_from_slice #u8 #Alloc.Alloc.t_Global lenb._0 bytes }
      <:
      t_Bytes
    in
    Core_models.Result.Result_Ok lenb <: Core_models.Result.t_Result t_Bytes u8

let encode_length_u16 (bytes: t_Bytes) =
  let len:usize = impl_Bytes__len bytes in
  if len >=. mk_usize 65536
  then Core_models.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core_models.Result.t_Result t_Bytes u8
  else
    let len:t_Array u8 (mk_usize 2) = u16_as_be_bytes (v_U16 (cast (len <: usize) <: u16) <: u16) in
    let lenb:t_Bytes =
      impl_Bytes__new_alloc (mk_usize 2 +! (impl_Bytes__len bytes <: usize) <: usize)
    in
    let lenb:t_Bytes = impl_Bytes__push lenb (len.[ mk_usize 0 ] <: u8) in
    let lenb:t_Bytes = impl_Bytes__push lenb (len.[ mk_usize 1 ] <: u8) in
    let
    (tmp0: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global), (tmp1: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    =
      Alloc.Vec.impl_1__append #u8 #Alloc.Alloc.t_Global lenb._0 bytes._0
    in
    let lenb:t_Bytes = { lenb with _0 = tmp0 } <: t_Bytes in
    let bytes:t_Bytes = { bytes with _0 = tmp1 } <: t_Bytes in
    let _:Prims.unit = () in
    Core_models.Result.Result_Ok lenb <: Core_models.Result.t_Result t_Bytes u8

let encode_length_u24 (bytes: t_Bytes) =
  let len:usize = impl_Bytes__len bytes in
  if len >=. mk_usize 16777216
  then Core_models.Result.Result_Err v_PAYLOAD_TOO_LONG <: Core_models.Result.t_Result t_Bytes u8
  else
    let len:t_Array u8 (mk_usize 4) = u32_as_be_bytes (v_U32 (cast (len <: usize) <: u32) <: u32) in
    let lenb:t_Bytes =
      impl_Bytes__new_alloc (mk_usize 3 +! (impl_Bytes__len bytes <: usize) <: usize)
    in
    let lenb:t_Bytes = impl_Bytes__push lenb (len.[ mk_usize 1 ] <: u8) in
    let lenb:t_Bytes = impl_Bytes__push lenb (len.[ mk_usize 2 ] <: u8) in
    let lenb:t_Bytes = impl_Bytes__push lenb (len.[ mk_usize 3 ] <: u8) in
    let lenb:t_Bytes = impl_Bytes__extend_from_slice lenb bytes in
    Core_models.Result.Result_Ok lenb <: Core_models.Result.t_Result t_Bytes u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_24': Core_models.Marker.t_StructuralPartialEq t_AppData

let impl_24 = impl_24'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_25': Core_models.Cmp.t_PartialEq t_AppData t_AppData

let impl_25 = impl_25'

let impl_AppData__new (b: t_Bytes) = AppData b <: t_AppData

let impl_AppData__into_raw (self: t_AppData) = self._0

let impl_AppData__as_raw (self: t_AppData) = self._0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core_models.Convert.t_From t_AppData (t_Slice u8) =
  {
    f_from_pre = (fun (value: t_Slice u8) -> true);
    f_from_post = (fun (value: t_Slice u8) (out: t_AppData) -> true);
    f_from
    =
    fun (value: t_Slice u8) ->
      AppData
      (Core_models.Convert.f_into #(t_Slice u8) #t_Bytes #FStar.Tactics.Typeclasses.solve value)
      <:
      t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (v_N: usize) : Core_models.Convert.t_From t_AppData (t_Array u8 v_N) =
  {
    f_from_pre = (fun (value: t_Array u8 v_N) -> true);
    f_from_post = (fun (value: t_Array u8 v_N) (out: t_AppData) -> true);
    f_from
    =
    fun (value: t_Array u8 v_N) ->
      AppData
      (Core_models.Convert.f_into #(t_Array u8 v_N) #t_Bytes #FStar.Tactics.Typeclasses.solve value)
      <:
      t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core_models.Convert.t_From t_AppData (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  {
    f_from_pre = (fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) -> true);
    f_from_post = (fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (out: t_AppData) -> true);
    f_from
    =
    fun (value: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
      AppData
      (Core_models.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #t_Bytes
          #FStar.Tactics.Typeclasses.solve
          value)
      <:
      t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core_models.Convert.t_From t_AppData t_Bytes =
  {
    f_from_pre = (fun (value: t_Bytes) -> true);
    f_from_post = (fun (value: t_Bytes) (out: t_AppData) -> true);
    f_from = fun (value: t_Bytes) -> AppData value <: t_AppData
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Declassify u8 u8 =
  {
    f_declassify_pre = (fun (self: u8) -> true);
    f_declassify_post = (fun (self: u8) (out: u8) -> true);
    f_declassify = fun (self: u8) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_Declassify u32 u32 =
  {
    f_declassify_pre = (fun (self: u32) -> true);
    f_declassify_post = (fun (self: u32) (out: u32) -> true);
    f_declassify = fun (self: u32) -> self
  }

let eq1 (b1 b2: u8) =
  (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve b1 <: u8) =.
  (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve b2 <: u8)

let check_eq1 (b1 b2: u8) =
  if eq1 b1 b2
  then Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  else Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let eq_slice (b1 b2: t_Slice u8) =
  if (Core_models.Slice.impl__len #u8 b1 <: usize) <>. (Core_models.Slice.impl__len #u8 b2 <: usize)
  then false
  else
    let (b: bool):bool = true in
    let b:bool =
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        (Core_models.Slice.impl__len #u8 b1 <: usize)
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            b2t b ==>
            (forall (j: usize).
                b2t (j <. i <: bool) ==> b2t ((b1.[ j ] <: u8) =. (b2.[ j ] <: u8) <: bool)))
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            let b:bool =
              if ~.(eq1 (b1.[ i ] <: u8) (b2.[ i ] <: u8) <: bool)
              then
                let b:bool = false in
                b
              else b
            in
            b)
    in
    let _:Prims.unit =
      if b
      then
        let _:Prims.unit =
          introduce forall (k: nat{k < Seq.length b1}) . Seq.index b1 k == Seq.index b2 k
          with assert (b1.[ mk_usize k ] == b2.[ mk_usize k ]);
          Seq.lemma_eq_intro b1 b2
        in
        ()
    in
    b

let eq_inner (b1 b2: t_Bytes) =
  eq_slice (Alloc.Vec.impl_1__as_slice b1._0 <: t_Slice u8)
    (Alloc.Vec.impl_1__as_slice b2._0 <: t_Slice u8)

let eq (b1 b2: t_Bytes) = eq_inner b1 b2

let check_eq_slice (b1 b2: t_Slice u8) =
  let b:bool = eq_slice b1 b2 in
  if b
  then Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  else Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let check_eq_inner (b1 b2: t_Bytes) =
  check_eq_slice (impl_Bytes__as_raw b1 <: t_Slice u8) (impl_Bytes__as_raw b2 <: t_Slice u8)

let check_eq_with_slice (b1 b2: t_Slice u8) (start v_end: usize) =
  if
    start >. (Core_models.Slice.impl__len #u8 b2 <: usize) ||
    v_end >. (Core_models.Slice.impl__len #u8 b2 <: usize) ||
    v_end <. start
  then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8
  else
    let b:bool =
      eq_slice b1
        (b2.[ { Core_models.Ops.Range.f_start = start; Core_models.Ops.Range.f_end = v_end }
            <:
            Core_models.Ops.Range.t_Range usize ]
          <:
          t_Slice u8)
    in
    if b
    then
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
    else
      Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let check_eq (b1 b2: t_Bytes) = check_eq_inner b1 b2

let check_eq_option (b1 b2: Core_models.Option.t_Option t_Bytes) =
  match b1, b2 <: (Core_models.Option.t_Option t_Bytes & Core_models.Option.t_Option t_Bytes) with
  | Core_models.Option.Option_None , Core_models.Option.Option_None  ->
    Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | Core_models.Option.Option_Some b1, Core_models.Option.Option_Some b2 -> check_eq_inner b1 b2
  | _ ->
    Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let check_mem (b1 b2: t_Slice u8) =
  if
    Core_models.Slice.impl__is_empty #u8 b1 ||
    ((Core_models.Slice.impl__len #u8 b2 <: usize) %! (Core_models.Slice.impl__len #u8 b1 <: usize)
      <:
      usize) <>.
    mk_usize 0
  then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8
  else
    let b:bool = false in
    let b:bool =
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        ((Core_models.Slice.impl__len #u8 b2 <: usize) /!
          (Core_models.Slice.impl__len #u8 b1 <: usize)
          <:
          usize)
        (fun b temp_1_ ->
            let b:bool = b in
            let _:usize = temp_1_ in
            true)
        b
        (fun b i ->
            let b:bool = b in
            let i:usize = i in
            if
              eq_slice b1
                (b2.[ {
                      Core_models.Ops.Range.f_start
                      =
                      i *! (Core_models.Slice.impl__len #u8 b1 <: usize) <: usize;
                      Core_models.Ops.Range.f_end
                      =
                      (i +! mk_usize 1 <: usize) *! (Core_models.Slice.impl__len #u8 b1 <: usize)
                      <:
                      usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
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
    then
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
    else
      Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8

let length_u8_encoded (bytes: t_Slice u8) =
  if Core_models.Slice.impl__is_empty #u8 bytes
  then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
  else
    let l:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 0 ] <: u8) <: u8
        )
      <:
      usize
    in
    if ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 1 <: usize) <. l
    then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
    else Core_models.Result.Result_Ok l <: Core_models.Result.t_Result usize u8

let length_u16_encoded_slice (bytes: t_Slice u8) =
  if (Core_models.Slice.impl__len #u8 bytes <: usize) <. mk_usize 2
  then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
  else
    let l0:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 0 ] <: u8) <: u8
        )
      <:
      usize
    in
    let l1:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 1 ] <: u8) <: u8
        )
      <:
      usize
    in
    let l:usize = (l0 *! mk_usize 256 <: usize) +! l1 in
    if ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 2 <: usize) <. l
    then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
    else Core_models.Result.Result_Ok l <: Core_models.Result.t_Result usize u8

let length_u16_encoded (bytes: t_Slice u8) = length_u16_encoded_slice bytes

let length_u24_encoded (bytes: t_Slice u8) =
  if (Core_models.Slice.impl__len #u8 bytes <: usize) <. mk_usize 3
  then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
  else
    let l0:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 0 ] <: u8) <: u8
        )
      <:
      usize
    in
    let l1:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 1 ] <: u8) <: u8
        )
      <:
      usize
    in
    let l2:usize =
      cast (f_declassify #u8 #u8 #FStar.Tactics.Typeclasses.solve (bytes.[ mk_usize 2 ] <: u8) <: u8
        )
      <:
      usize
    in
    let l:usize =
      ((l0 *! mk_usize 65536 <: usize) +! (l1 *! mk_usize 256 <: usize) <: usize) +! l2
    in
    if ((Core_models.Slice.impl__len #u8 bytes <: usize) -! mk_usize 3 <: usize) <. l
    then Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result usize u8
    else Core_models.Result.Result_Ok l <: Core_models.Result.t_Result usize u8

let check_length_encoding_u8_slice (bytes: t_Slice u8) =
  match length_u8_encoded bytes <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok hoist200 ->
    if (hoist200 +! mk_usize 1 <: usize) <>. (Core_models.Slice.impl__len #u8 bytes <: usize)
    then
      Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8
    else
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8

let check_length_encoding_u8 (bytes: t_Bytes) =
  check_length_encoding_u8_slice (impl_Bytes__as_raw bytes <: t_Slice u8)

let check_length_encoding_u16_slice (bytes: t_Slice u8) =
  match length_u16_encoded bytes <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok hoist203 ->
    if (hoist203 +! mk_usize 2 <: usize) <>. (Core_models.Slice.impl__len #u8 bytes <: usize)
    then
      Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8
    else
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8

let check_length_encoding_u16 (bytes: t_Bytes) =
  check_length_encoding_u16_slice (impl_Bytes__as_raw bytes <: t_Slice u8)

let check_length_encoding_u24 (bytes: t_Slice u8) =
  match length_u24_encoded bytes <: Core_models.Result.t_Result usize u8 with
  | Core_models.Result.Result_Ok hoist206 ->
    if (hoist206 +! mk_usize 3 <: usize) <>. (Core_models.Slice.impl__len #u8 bytes <: usize)
    then
      Core_models.Result.Result_Err (parse_failed ()) <: Core_models.Result.t_Result Prims.unit u8
    else
      Core_models.Result.Result_Ok (() <: Prims.unit) <: Core_models.Result.t_Result Prims.unit u8
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit u8
