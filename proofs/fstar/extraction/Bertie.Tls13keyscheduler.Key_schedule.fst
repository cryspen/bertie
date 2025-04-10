module Bertie.Tls13keyscheduler.Key_schedule
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Bertie.Tls13crypto in
  let open Bertie.Tls13utils in
  ()

let hkdf_expand_label
      (hash_algorithm: Bertie.Tls13crypto.t_HashAlgorithm)
      (key label context: Bertie.Tls13utils.t_Bytes)
      (len: usize)
     =
  if len >=. mk_usize 65536
  then
    Core.Result.Result_Err Bertie.Tls13utils.v_PAYLOAD_TOO_LONG
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  else
    let lenb:t_Array u8 (mk_usize 2) =
      Bertie.Tls13utils.u16_as_be_bytes (Bertie.Tls13utils.v_U16 (cast (len <: usize) <: u16) <: u16
        )
    in
    let tls13_label:Bertie.Tls13utils.t_Bytes =
      Bertie.Tls13utils.impl_Bytes__concat (Bertie.Tls13utils.impl_Bytes__from_slice (Bertie.Tls13formats.v_LABEL_TLS13
              <:
              t_Slice u8)
          <:
          Bertie.Tls13utils.t_Bytes)
        label
    in
    match
      Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw tls13_label
          <:
          t_Slice u8)
      <:
      Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
    with
    | Core.Result.Result_Ok hoist131 ->
      (match
          Bertie.Tls13utils.encode_length_u8 (Bertie.Tls13utils.impl_Bytes__as_raw context
              <:
              t_Slice u8)
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        with
        | Core.Result.Result_Ok hoist130 ->
          let info:Bertie.Tls13utils.t_Bytes =
            Bertie.Tls13utils.impl_Bytes__prefix (Bertie.Tls13utils.impl_Bytes__concat hoist131
                  hoist130
                <:
                Bertie.Tls13utils.t_Bytes)
              (lenb <: t_Slice u8)
          in
          Bertie.Tls13crypto.hkdf_expand hash_algorithm key info len
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8)
    | Core.Result.Result_Err err ->
      Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8

let t_TLSnames_cast_to_repr (x: t_TLSnames) =
  match x <: t_TLSnames with
  | TLSnames_ES  -> mk_isize 0
  | TLSnames_EEM  -> mk_isize 1
  | TLSnames_CET  -> mk_isize 2
  | TLSnames_Bind  -> mk_isize 3
  | TLSnames_Binder  -> mk_isize 4
  | TLSnames_HS  -> mk_isize 5
  | TLSnames_SHT  -> mk_isize 6
  | TLSnames_CHT  -> mk_isize 7
  | TLSnames_HSalt  -> mk_isize 8
  | TLSnames_AS  -> mk_isize 9
  | TLSnames_RM  -> mk_isize 10
  | TLSnames_CAT  -> mk_isize 11
  | TLSnames_SAT  -> mk_isize 12
  | TLSnames_EAM  -> mk_isize 13
  | TLSnames_PSK  -> mk_isize 14
  | TLSnames_ZeroSalt  -> mk_isize 15
  | TLSnames_ESalt  -> mk_isize 16
  | TLSnames_KEM  -> mk_isize 17
  | TLSnames_ZeroIKM  -> mk_isize 18

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Clone.t_Clone t_TLSnames

let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_TLSnames

let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Marker.t_StructuralPartialEq t_TLSnames

let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Cmp.t_PartialEq t_TLSnames t_TLSnames

let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Cmp.t_Eq t_TLSnames

let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Hash.t_Hash t_TLSnames

let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_TLSnames

let impl_7 = impl_7'

let t_Label_cast_to_repr (x: t_Label) =
  match x <: t_Label with
  | Label_e__e__e__e__e__e__  -> mk_isize 0
  | Label_RES_BINDER_e_  -> mk_isize 1
  | Label_EXT_BINDER_e_  -> mk_isize 2
  | Label_C_E_TRAFFIC_  -> mk_isize 3
  | Label_E_EXP_MASTER  -> mk_isize 4
  | Label_EXP_MASTER_e_  -> mk_isize 5
  | Label_RES_MASTER_e_  -> mk_isize 6
  | Label_C_HS_TRAFFIC  -> mk_isize 7
  | Label_S_HS_TRAFFIC  -> mk_isize 8
  | Label_DERIVED_e__e__  -> mk_isize 9
  | Label_C_AP_TRAFFIC  -> mk_isize 10
  | Label_S_AP_TRAFFIC  -> mk_isize 11
  | Label_RESUMPTION_e_  -> mk_isize 12

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core.Fmt.t_Debug t_Label

let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Marker.t_StructuralPartialEq t_Label

let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core.Cmp.t_PartialEq t_Label t_Label

let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core.Cmp.t_Eq t_Label

let impl_11 = impl_11'

let convert_label (label: Bertie.Tls13utils.t_Bytes) =
  let l:t_Slice u8 =
    (Bertie.Tls13utils.impl_Bytes__declassify label <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global).[ Core.Ops.Range.RangeFull
      <:
      Core.Ops.Range.t_RangeFull ]
  in
  if
    l =.
    (let list =
        [
          mk_u8 101; mk_u8 120; mk_u8 116; mk_u8 32; mk_u8 98; mk_u8 105; mk_u8 110; mk_u8 100;
          mk_u8 101; mk_u8 114
        ]
      in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
      Rust_primitives.Hax.array_of_list 10 list)
  then Core.Option.Option_Some (Label_EXT_BINDER_e_ <: t_Label) <: Core.Option.t_Option t_Label
  else
    if
      l =.
      (let list =
          [
            mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 98; mk_u8 105; mk_u8 110; mk_u8 100;
            mk_u8 101; mk_u8 114
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
        Rust_primitives.Hax.array_of_list 10 list)
    then Core.Option.Option_Some (Label_RES_BINDER_e_ <: t_Label) <: Core.Option.t_Option t_Label
    else
      if
        l =.
        (let list =
            [
              mk_u8 99; mk_u8 32; mk_u8 101; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97; mk_u8 102;
              mk_u8 102; mk_u8 105; mk_u8 99
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
          Rust_primitives.Hax.array_of_list 11 list)
      then Core.Option.Option_Some (Label_C_E_TRAFFIC_ <: t_Label) <: Core.Option.t_Option t_Label
      else
        if
          l =.
          (let list =
              [
                mk_u8 101; mk_u8 32; mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109; mk_u8 97;
                mk_u8 115; mk_u8 116; mk_u8 101; mk_u8 114
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
            Rust_primitives.Hax.array_of_list 12 list)
        then Core.Option.Option_Some (Label_E_EXP_MASTER <: t_Label) <: Core.Option.t_Option t_Label
        else
          if
            l =.
            (let list =
                [
                  mk_u8 99; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97;
                  mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
              Rust_primitives.Hax.array_of_list 12 list)
          then
            Core.Option.Option_Some (Label_C_AP_TRAFFIC <: t_Label) <: Core.Option.t_Option t_Label
          else
            if
              l =.
              (let list =
                  [
                    mk_u8 115; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114;
                    mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                Rust_primitives.Hax.array_of_list 12 list)
            then
              Core.Option.Option_Some (Label_S_AP_TRAFFIC <: t_Label)
              <:
              Core.Option.t_Option t_Label
            else
              if
                l =.
                (let list =
                    [
                      mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115;
                      mk_u8 116; mk_u8 101; mk_u8 114
                    ]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                  Rust_primitives.Hax.array_of_list 10 list)
              then
                Core.Option.Option_Some (Label_EXP_MASTER_e_ <: t_Label)
                <:
                Core.Option.t_Option t_Label
              else
                if
                  l =.
                  (let list =
                      [
                        mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115;
                        mk_u8 116; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                then
                  Core.Option.Option_Some (Label_RES_MASTER_e_ <: t_Label)
                  <:
                  Core.Option.t_Option t_Label
                else
                  if
                    l =.
                    (let list =
                        [
                          mk_u8 100;
                          mk_u8 101;
                          mk_u8 114;
                          mk_u8 105;
                          mk_u8 118;
                          mk_u8 101;
                          mk_u8 100
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
                      Rust_primitives.Hax.array_of_list 7 list)
                  then
                    Core.Option.Option_Some (Label_DERIVED_e__e__ <: t_Label)
                    <:
                    Core.Option.t_Option t_Label
                  else
                    if
                      l =.
                      (let list =
                          [
                            mk_u8 99; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116; mk_u8 114;
                            mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                          ]
                        in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                        Rust_primitives.Hax.array_of_list 12 list)
                    then
                      Core.Option.Option_Some (Label_C_HS_TRAFFIC <: t_Label)
                      <:
                      Core.Option.t_Option t_Label
                    else
                      if
                        l =.
                        (let list =
                            [
                              mk_u8 115; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116;
                              mk_u8 114; mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                            ]
                          in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                          Rust_primitives.Hax.array_of_list 12 list)
                      then
                        Core.Option.Option_Some (Label_S_HS_TRAFFIC <: t_Label)
                        <:
                        Core.Option.t_Option t_Label
                      else
                        if
                          l =.
                          (let list =
                              [
                                mk_u8 82; mk_u8 69; mk_u8 83; mk_u8 85; mk_u8 77; mk_u8 80; mk_u8 84;
                                mk_u8 73; mk_u8 79; mk_u8 78
                              ]
                            in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                            Rust_primitives.Hax.array_of_list 10 list)
                        then
                          Core.Option.Option_Some (Label_RESUMPTION_e_ <: t_Label)
                          <:
                          Core.Option.t_Option t_Label
                        else
                          if
                            l =.
                            (let list:Prims.list u8 = [] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
                              Rust_primitives.Hax.array_of_list 0 list)
                          then
                            Core.Option.Option_Some (Label_e__e__e__e__e__e__ <: t_Label)
                            <:
                            Core.Option.t_Option t_Label
                          else Core.Option.Option_None <: Core.Option.t_Option t_Label

let label_to_bytes (label: t_Label) =
  match label <: t_Label with
  | Label_EXT_BINDER_e_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 101; mk_u8 120; mk_u8 116; mk_u8 32; mk_u8 98; mk_u8 105; mk_u8 110;
                        mk_u8 100; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 10)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_RES_BINDER_e_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 98; mk_u8 105; mk_u8 110;
                        mk_u8 100; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 10)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_C_E_TRAFFIC_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 99; mk_u8 32; mk_u8 101; mk_u8 32; mk_u8 116; mk_u8 114; mk_u8 97;
                        mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 11);
                    Rust_primitives.Hax.array_of_list 11 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 11)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_E_EXP_MASTER  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 101; mk_u8 32; mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109;
                        mk_u8 97; mk_u8 115; mk_u8 116; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                    Rust_primitives.Hax.array_of_list 12 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 12)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_C_AP_TRAFFIC  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 99; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114;
                        mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                    Rust_primitives.Hax.array_of_list 12 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 12)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_S_AP_TRAFFIC  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 115; mk_u8 32; mk_u8 97; mk_u8 112; mk_u8 32; mk_u8 116; mk_u8 114;
                        mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                    Rust_primitives.Hax.array_of_list 12 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 12)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_EXP_MASTER_e_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 101; mk_u8 120; mk_u8 112; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115;
                        mk_u8 116; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 10)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_RES_MASTER_e_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 114; mk_u8 101; mk_u8 115; mk_u8 32; mk_u8 109; mk_u8 97; mk_u8 115;
                        mk_u8 116; mk_u8 101; mk_u8 114
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 10)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_DERIVED_e__e__  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [mk_u8 100; mk_u8 101; mk_u8 114; mk_u8 105; mk_u8 118; mk_u8 101; mk_u8 100]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
                    Rust_primitives.Hax.array_of_list 7 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 7)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_C_HS_TRAFFIC  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 99; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116; mk_u8 114;
                        mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                    Rust_primitives.Hax.array_of_list 12 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 12)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_S_HS_TRAFFIC  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 115; mk_u8 32; mk_u8 104; mk_u8 115; mk_u8 32; mk_u8 116; mk_u8 114;
                        mk_u8 97; mk_u8 102; mk_u8 102; mk_u8 105; mk_u8 99
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
                    Rust_primitives.Hax.array_of_list 12 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 12)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_RESUMPTION_e_  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #u8
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        mk_u8 82; mk_u8 69; mk_u8 83; mk_u8 85; mk_u8 77; mk_u8 80; mk_u8 84;
                        mk_u8 73; mk_u8 79; mk_u8 78
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 10);
                    Rust_primitives.Hax.array_of_list 10 list)
                <:
                Alloc.Boxed.t_Box (t_Array u8 (mk_usize 10)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice u8) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  | Label_e__e__e__e__e__e__  ->
    Core.Convert.f_into #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #Bertie.Tls13utils.t_Bytes
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_KeySchedule t_TLSkeyscheduler t_TLSnames =
  {
    f_prnt_n_pre = (fun (a: t_TLSnames) -> true);
    f_prnt_n_post
    =
    (fun
        (a: t_TLSnames)
        (out: (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames))
        ->
        true);
    f_prnt_n
    =
    (fun (a: t_TLSnames) ->
        match a <: t_TLSnames with
        | TLSnames_ES  ->
          (Core.Option.Option_Some (TLSnames_ZeroSalt <: t_TLSnames)
            <:
            Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_Some (TLSnames_PSK <: t_TLSnames) <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_EEM
        | TLSnames_CET
        | TLSnames_Bind  ->
          (Core.Option.Option_Some (TLSnames_ES <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_Binder  ->
          (Core.Option.Option_Some (TLSnames_Bind <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_HS  ->
          (Core.Option.Option_Some (TLSnames_ESalt <: t_TLSnames) <: Core.Option.t_Option t_TLSnames
          ),
          (Core.Option.Option_Some (TLSnames_KEM <: t_TLSnames) <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_SHT
        | TLSnames_CHT
        | TLSnames_HSalt  ->
          (Core.Option.Option_Some (TLSnames_HS <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_AS  ->
          (Core.Option.Option_Some (TLSnames_HSalt <: t_TLSnames) <: Core.Option.t_Option t_TLSnames
          ),
          (Core.Option.Option_Some (TLSnames_ZeroIKM <: t_TLSnames)
            <:
            Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_RM
        | TLSnames_CAT
        | TLSnames_SAT
        | TLSnames_EAM  ->
          (Core.Option.Option_Some (TLSnames_AS <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_PSK  ->
          (Core.Option.Option_Some (TLSnames_RM <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_ZeroSalt
        | TLSnames_KEM
        | TLSnames_ZeroIKM  ->
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames)
        | TLSnames_ESalt  ->
          (Core.Option.Option_Some (TLSnames_ES <: t_TLSnames) <: Core.Option.t_Option t_TLSnames),
          (Core.Option.Option_None <: Core.Option.t_Option t_TLSnames)
          <:
          (Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames));
    f_labels_pre = (fun (a: t_TLSnames) (b: bool) -> true);
    f_labels_post
    =
    (fun (a: t_TLSnames) (b: bool) (out: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8) -> true);
    f_labels
    =
    (fun (a: t_TLSnames) (b: bool) ->
        match a <: t_TLSnames with
        | TLSnames_Bind  ->
          Core.Result.Result_Ok
          (label_to_bytes (if b
                then Label_RES_BINDER_e_ <: t_Label
                else Label_EXT_BINDER_e_ <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_RM  ->
          Core.Result.Result_Ok (label_to_bytes (Label_RES_MASTER_e_ <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_ESalt
        | TLSnames_HSalt  ->
          Core.Result.Result_Ok (label_to_bytes (Label_DERIVED_e__e__ <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_EEM
        | TLSnames_EAM  ->
          Core.Result.Result_Ok (label_to_bytes (Label_E_EXP_MASTER <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_CET  ->
          Core.Result.Result_Ok (label_to_bytes (Label_C_E_TRAFFIC_ <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_Binder  ->
          Core.Result.Result_Ok (label_to_bytes (Label_e__e__e__e__e__e__ <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_SHT  ->
          Core.Result.Result_Ok (label_to_bytes (Label_S_HS_TRAFFIC <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_CHT  ->
          Core.Result.Result_Ok (label_to_bytes (Label_C_HS_TRAFFIC <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_CAT  ->
          Core.Result.Result_Ok (label_to_bytes (Label_C_AP_TRAFFIC <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | TLSnames_SAT  ->
          Core.Result.Result_Ok (label_to_bytes (Label_S_AP_TRAFFIC <: t_Label))
          <:
          Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
        | _ ->
          match
            Core.Result.Result_Err Bertie.Tls13utils.v_INCORRECT_STATE
            <:
            Core.Result.t_Result t_Label u8
          with
          | Core.Result.Result_Ok ok ->
            Core.Result.Result_Ok (label_to_bytes ok)
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8);
    f_get_pre
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        ->
        true);
    f_get_post
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        (out: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
        ->
        true);
    f_get
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        ->
        Core.Option.impl__map #Bertie.Tls13utils.t_Bytes
          #Bertie.Tls13utils.t_Bytes
          (Std.Collections.Hash.Map.impl_2__get #(t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm &
                u8)
              #Bertie.Tls13utils.t_Bytes
              #Std.Hash.Random.t_RandomState
              #(t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8)
              self.f_keys
              h
            <:
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          (fun x ->
              let x:Bertie.Tls13utils.t_Bytes = x in
              Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve x
              <:
              Bertie.Tls13utils.t_Bytes));
    f_set_pre
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        (k: Bertie.Tls13utils.t_Bytes)
        ->
        true);
    f_set_post
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        (k: Bertie.Tls13utils.t_Bytes)
        (out1: t_TLSkeyscheduler)
        ->
        true);
    f_set
    =
    (fun
        (self: t_TLSkeyscheduler)
        (name: t_TLSnames)
        (level: u8)
        (h: (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
        (k: Bertie.Tls13utils.t_Bytes)
        ->
        let tmp0, out:(Std.Collections.Hash.Map.t_HashMap
            (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8)
            Bertie.Tls13utils.t_Bytes
            Std.Hash.Random.t_RandomState &
          Core.Option.t_Option Bertie.Tls13utils.t_Bytes) =
          Std.Collections.Hash.Map.impl_2__insert #(t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm &
              u8)
            #Bertie.Tls13utils.t_Bytes
            #Std.Hash.Random.t_RandomState
            self.f_keys
            h
            k
        in
        let self:t_TLSkeyscheduler = { self with f_keys = tmp0 } <: t_TLSkeyscheduler in
        let _:Core.Option.t_Option Bertie.Tls13utils.t_Bytes = out in
        self);
    f_hash_pre = (fun (d: Bertie.Tls13utils.t_Bytes) -> true);
    f_hash_post = (fun (d: Bertie.Tls13utils.t_Bytes) (out: Bertie.Tls13utils.t_Bytes) -> true);
    f_hash
    =
    fun (d: Bertie.Tls13utils.t_Bytes) ->
      Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve d
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core.Clone.t_Clone t_TagKey

let impl_12 = impl_12'

let xtr_alg (alg: Bertie.Tls13crypto.t_HashAlgorithm) (k1 k2: Bertie.Tls13utils.t_Bytes) =
  Bertie.Tls13crypto.hkdf_extract alg k1 k2

let xpd_alg (alg: Bertie.Tls13crypto.t_HashAlgorithm) (k1 label d: Bertie.Tls13utils.t_Bytes) =
  let kvt:Core.Option.t_Option t_Label =
    convert_label (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes
          #FStar.Tactics.Typeclasses.solve
          label
        <:
        Bertie.Tls13utils.t_Bytes)
  in
  if
    kvt =.
    (Core.Option.Option_Some (Label_e__e__e__e__e__e__ <: t_Label) <: Core.Option.t_Option t_Label)
  then Bertie.Tls13crypto.hmac_tag alg k1 d
  else
    hkdf_expand_label alg k1 label d (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len alg <: usize)

let xtr (k1 k2: t_TagKey) =
  match xtr_alg k1.f_alg k1.f_val k2.f_val <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
  | Core.Result.Result_Ok v_val ->
    Core.Result.Result_Ok
    ({
        f_alg
        =
        Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm
          #FStar.Tactics.Typeclasses.solve
          k1.f_alg;
        f_tag = Core.Clone.f_clone #t_TLSnames #FStar.Tactics.Typeclasses.solve k1.f_tag;
        f_val = v_val
      }
      <:
      t_TagKey)
    <:
    Core.Result.t_Result t_TagKey u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_TagKey u8

let xpd (k1: t_TagKey) (label d: Bertie.Tls13utils.t_Bytes) =
  let { f_alg = alg ; f_tag = tag ; f_val = k1 }:t_TagKey =
    Core.Clone.f_clone #t_TagKey #FStar.Tactics.Typeclasses.solve k1
  in
  match xpd_alg alg k1 label d <: Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8 with
  | Core.Result.Result_Ok v_val ->
    Core.Result.Result_Ok ({ f_tag = tag; f_alg = alg; f_val = v_val } <: t_TagKey)
    <:
    Core.Result.t_Result t_TagKey u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_TagKey u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core.Clone.t_Clone t_Handle

let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core.Fmt.t_Debug t_Handle

let impl_14 = impl_14'

let xpd_angle
      (name: t_TLSnames)
      (label: Bertie.Tls13utils.t_Bytes)
      (parrent_handle: t_Handle)
      (args: Bertie.Tls13utils.t_Bytes)
     =
  Core.Result.Result_Ok
  ({ f_name = name; f_alg = parrent_handle.f_alg; f_level = parrent_handle.f_level } <: t_Handle)
  <:
  Core.Result.t_Result t_Handle u8

let set_by_handle (ks: t_TLSkeyscheduler) (handle: t_Handle) (key: Bertie.Tls13utils.t_Bytes) =
  let ks:t_TLSkeyscheduler =
    f_set #t_TLSkeyscheduler
      #t_TLSnames
      #FStar.Tactics.Typeclasses.solve
      ks
      handle.f_name
      handle.f_level
      (handle.f_name, handle.f_alg, handle.f_level
        <:
        (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
      key
  in
  ks

let zero_salt (ks: t_TLSkeyscheduler) (alg: Bertie.Tls13crypto.t_HashAlgorithm) =
  let handle:t_Handle =
    {
      f_alg
      =
      Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm #FStar.Tactics.Typeclasses.solve alg;
      f_name = TLSnames_ZeroSalt <: t_TLSnames;
      f_level = mk_u8 0
    }
    <:
    t_Handle
  in
  let ks:t_TLSkeyscheduler =
    set_by_handle ks
      handle
      (Bertie.Tls13utils.impl_Bytes__zeroes (mk_usize 1) <: Bertie.Tls13utils.t_Bytes)
  in
  let hax_temp_output:t_Handle = handle in
  ks, hax_temp_output <: (t_TLSkeyscheduler & t_Handle)

let no_psk (ks: t_TLSkeyscheduler) (alg: Bertie.Tls13crypto.t_HashAlgorithm) =
  let handle:t_Handle =
    {
      f_alg
      =
      Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm #FStar.Tactics.Typeclasses.solve alg;
      f_name = TLSnames_PSK <: t_TLSnames;
      f_level = mk_u8 0
    }
    <:
    t_Handle
  in
  let ks:t_TLSkeyscheduler =
    set_by_handle ks
      handle
      (Bertie.Tls13utils.impl_Bytes__zeroes (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len alg
            <:
            usize)
        <:
        Bertie.Tls13utils.t_Bytes)
  in
  let hax_temp_output:t_Handle = handle in
  ks, hax_temp_output <: (t_TLSkeyscheduler & t_Handle)

let zero_ikm (ks: t_TLSkeyscheduler) (alg: Bertie.Tls13crypto.t_HashAlgorithm) =
  let handle:t_Handle =
    {
      f_alg
      =
      Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm #FStar.Tactics.Typeclasses.solve alg;
      f_name = TLSnames_ZeroIKM <: t_TLSnames;
      f_level = mk_u8 0
    }
    <:
    t_Handle
  in
  let ks:t_TLSkeyscheduler =
    set_by_handle ks
      handle
      (Bertie.Tls13utils.impl_Bytes__zeroes (Bertie.Tls13crypto.impl_HashAlgorithm__hash_len alg
            <:
            usize)
        <:
        Bertie.Tls13utils.t_Bytes)
  in
  let hax_temp_output:t_Handle = handle in
  ks, hax_temp_output <: (t_TLSkeyscheduler & t_Handle)

let get_by_handle (ks: t_TLSkeyscheduler) (handle: t_Handle) =
  f_get #t_TLSkeyscheduler
    #t_TLSnames
    #FStar.Tactics.Typeclasses.solve
    ks
    handle.f_name
    handle.f_level
    (handle.f_name, handle.f_alg, handle.f_level
      <:
      (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))

let tagkey_from_handle (ks: t_TLSkeyscheduler) (handle: t_Handle) =
  match
    Core.Option.impl__ok_or #Bertie.Tls13utils.t_Bytes
      #u8
      (get_by_handle ks handle <: Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
      Bertie.Tls13utils.v_INCORRECT_STATE
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok hoist135 ->
    Core.Result.Result_Ok
    ({ f_alg = handle.f_alg; f_tag = handle.f_name; f_val = hoist135 } <: t_TagKey)
    <:
    Core.Result.t_Result t_TagKey u8
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_TagKey u8

let v_XPD
      (ks: t_TLSkeyscheduler)
      (n: t_TLSnames)
      (l: u8)
      (h1: t_Handle)
      (r: bool)
      (args: Bertie.Tls13utils.t_Bytes)
     =
  let n1, _:(Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames) =
    f_prnt_n #t_TLSkeyscheduler #t_TLSnames #FStar.Tactics.Typeclasses.solve n
  in
  match
    f_labels #t_TLSkeyscheduler #t_TLSnames #FStar.Tactics.Typeclasses.solve n r
    <:
    Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
  with
  | Core.Result.Result_Ok label ->
    (match
        xpd_angle n
          (Core.Clone.f_clone #Bertie.Tls13utils.t_Bytes #FStar.Tactics.Typeclasses.solve label
            <:
            Bertie.Tls13utils.t_Bytes)
          h1
          args
        <:
        Core.Result.t_Result t_Handle u8
      with
      | Core.Result.Result_Ok h ->
        (match
            Core.Option.impl__ok_or #Bertie.Tls13utils.t_Bytes
              #u8
              (f_get #t_TLSkeyscheduler
                  #t_TLSnames
                  #FStar.Tactics.Typeclasses.solve
                  ks
                  (Core.Option.impl__unwrap #t_TLSnames n1 <: t_TLSnames)
                  l
                  (h1.f_name, h1.f_alg, h1.f_level
                    <:
                    (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
                <:
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
              Bertie.Tls13utils.v_INCORRECT_STATE
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok k1 ->
            if n =. (TLSnames_PSK <: t_TLSnames)
            then
              let l:u8 = l +! mk_u8 1 in
              match
                xpd ({ f_alg = h1.f_alg; f_tag = h1.f_name; f_val = k1 } <: t_TagKey) label args
                <:
                Core.Result.t_Result t_TagKey u8
              with
              | Core.Result.Result_Ok ok ->
                let l, (k: t_TagKey):(u8 & t_TagKey) = l, ok <: (u8 & t_TagKey) in
                let ks:t_TLSkeyscheduler =
                  f_set #t_TLSkeyscheduler
                    #t_TLSnames
                    #FStar.Tactics.Typeclasses.solve
                    ks
                    n
                    l
                    (h.f_name, h.f_alg, h.f_level
                      <:
                      (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
                    k.f_val
                in
                let hax_temp_output:Core.Result.t_Result t_Handle u8 =
                  Core.Result.Result_Ok h <: Core.Result.t_Result t_Handle u8
                in
                ks, hax_temp_output <: (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
              | Core.Result.Result_Err err ->
                ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
                <:
                (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
            else
              let d:Bertie.Tls13utils.t_Bytes =
                f_hash #t_TLSkeyscheduler #t_TLSnames #FStar.Tactics.Typeclasses.solve args
              in
              (match
                  xpd ({ f_alg = h1.f_alg; f_tag = h1.f_name; f_val = k1 } <: t_TagKey) label d
                  <:
                  Core.Result.t_Result t_TagKey u8
                with
                | Core.Result.Result_Ok ok ->
                  let l, (k: t_TagKey):(u8 & t_TagKey) = l, ok <: (u8 & t_TagKey) in
                  let ks:t_TLSkeyscheduler =
                    f_set #t_TLSkeyscheduler
                      #t_TLSnames
                      #FStar.Tactics.Typeclasses.solve
                      ks
                      n
                      l
                      (h.f_name, h.f_alg, h.f_level
                        <:
                        (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
                      k.f_val
                  in
                  let hax_temp_output:Core.Result.t_Result t_Handle u8 =
                    Core.Result.Result_Ok h <: Core.Result.t_Result t_Handle u8
                  in
                  ks, hax_temp_output <: (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
                | Core.Result.Result_Err err ->
                  ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
                  <:
                  (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
          | Core.Result.Result_Err err ->
            ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
            <:
            (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
      | Core.Result.Result_Err err ->
        ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
        <:
        (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
  | Core.Result.Result_Err err ->
    ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
    <:
    (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)

let xtr_angle (name: t_TLSnames) (left right: t_Handle) =
  Core.Result.Result_Ok ({ f_alg = left.f_alg; f_name = name; f_level = left.f_level } <: t_Handle)
  <:
  Core.Result.t_Result t_Handle u8

#push-options "--admit_smt_queries true"

let v_XTR (ks: t_TLSkeyscheduler) (level: u8) (name: t_TLSnames) (h1 h2: t_Handle) =
  let n1, n2:(Core.Option.t_Option t_TLSnames & Core.Option.t_Option t_TLSnames) =
    f_prnt_n #t_TLSkeyscheduler #t_TLSnames #FStar.Tactics.Typeclasses.solve name
  in
  match
    xtr_angle name
      (Core.Clone.f_clone #t_Handle #FStar.Tactics.Typeclasses.solve h1 <: t_Handle)
      (Core.Clone.f_clone #t_Handle #FStar.Tactics.Typeclasses.solve h2 <: t_Handle)
    <:
    Core.Result.t_Result t_Handle u8
  with
  | Core.Result.Result_Ok h ->
    (match
        Core.Option.impl__ok_or #Bertie.Tls13utils.t_Bytes
          #u8
          (f_get #t_TLSkeyscheduler
              #t_TLSnames
              #FStar.Tactics.Typeclasses.solve
              ks
              (Core.Option.impl__unwrap #t_TLSnames n1 <: t_TLSnames)
              (Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve level <: u8)
              (h1.f_name, h1.f_alg, h1.f_level
                <:
                (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
            <:
            Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
          Bertie.Tls13utils.v_INCORRECT_STATE
        <:
        Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
      with
      | Core.Result.Result_Ok k1 ->
        (match
            Core.Option.impl__ok_or #Bertie.Tls13utils.t_Bytes
              #u8
              (f_get #t_TLSkeyscheduler
                  #t_TLSnames
                  #FStar.Tactics.Typeclasses.solve
                  ks
                  (Core.Option.impl__unwrap #t_TLSnames n2 <: t_TLSnames)
                  (Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve level <: u8)
                  (h2.f_name, h2.f_alg, h2.f_level
                    <:
                    (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
                <:
                Core.Option.t_Option Bertie.Tls13utils.t_Bytes)
              Bertie.Tls13utils.v_INCORRECT_STATE
            <:
            Core.Result.t_Result Bertie.Tls13utils.t_Bytes u8
          with
          | Core.Result.Result_Ok k2 ->
            (match
                xtr ({
                      f_alg
                      =
                      Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm
                        #FStar.Tactics.Typeclasses.solve
                        h1.f_alg
                      <:
                      Bertie.Tls13crypto.t_HashAlgorithm;
                      f_tag = h1.f_name;
                      f_val = k1
                    }
                    <:
                    t_TagKey)
                  ({
                      f_alg
                      =
                      Core.Clone.f_clone #Bertie.Tls13crypto.t_HashAlgorithm
                        #FStar.Tactics.Typeclasses.solve
                        h2.f_alg
                      <:
                      Bertie.Tls13crypto.t_HashAlgorithm;
                      f_tag = h2.f_name;
                      f_val = k2
                    }
                    <:
                    t_TagKey)
                <:
                Core.Result.t_Result t_TagKey u8
              with
              | Core.Result.Result_Ok k ->
                let ks:t_TLSkeyscheduler =
                  f_set #t_TLSkeyscheduler
                    #t_TLSnames
                    #FStar.Tactics.Typeclasses.solve
                    ks
                    name
                    level
                    (h.f_name, h.f_alg, h.f_level
                      <:
                      (t_TLSnames & Bertie.Tls13crypto.t_HashAlgorithm & u8))
                    k.f_val
                in
                let hax_temp_output:Core.Result.t_Result t_Handle u8 =
                  Core.Result.Result_Ok h <: Core.Result.t_Result t_Handle u8
                in
                ks, hax_temp_output <: (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
              | Core.Result.Result_Err err ->
                ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
                <:
                (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
          | Core.Result.Result_Err err ->
            ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
            <:
            (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
      | Core.Result.Result_Err err ->
        ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
        <:
        (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8))
  | Core.Result.Result_Err err ->
    ks, (Core.Result.Result_Err err <: Core.Result.t_Result t_Handle u8)
    <:
    (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)

#pop-options
