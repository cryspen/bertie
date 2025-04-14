module t13.Tls13keyscheduler.Key_schedule
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open t13.Tls13crypto in
  let open t13.Tls13utils in
  ()

/// HKDF expand with a `label`.
val hkdf_expand_label
      (hash_algorithm: t13.Tls13crypto.t_HashAlgorithm)
      (key label context: t13.Tls13utils.t_Bytes)
      (len: usize)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

class t_KeySchedule (v_Self: Type0) (v_N: Type0) = {
  f_labels_pre:v_N -> bool -> Type0;
  f_labels_post:v_N -> bool -> Core.Result.t_Result t13.Tls13utils.t_Bytes u8 -> Type0;
  f_labels:x0: v_N -> x1: bool
    -> Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
        (f_labels_pre x0 x1)
        (fun result -> f_labels_post x0 x1 result);
  f_prnt_n_pre:v_N -> Type0;
  f_prnt_n_post:v_N -> (Core.Option.t_Option v_N & Core.Option.t_Option v_N) -> Type0;
  f_prnt_n:x0: v_N
    -> Prims.Pure (Core.Option.t_Option v_N & Core.Option.t_Option v_N)
        (f_prnt_n_pre x0)
        (fun result -> f_prnt_n_post x0 result);
  f_get_pre:v_Self -> v_N -> u8 -> (v_N & t13.Tls13crypto.t_HashAlgorithm & u8) -> Type0;
  f_get_post:
      v_Self ->
      v_N ->
      u8 ->
      (v_N & t13.Tls13crypto.t_HashAlgorithm & u8) ->
      Core.Option.t_Option t13.Tls13utils.t_Bytes
    -> Type0;
  f_get:x0: v_Self -> x1: v_N -> x2: u8 -> x3: (v_N & t13.Tls13crypto.t_HashAlgorithm & u8)
    -> Prims.Pure (Core.Option.t_Option t13.Tls13utils.t_Bytes)
        (f_get_pre x0 x1 x2 x3)
        (fun result -> f_get_post x0 x1 x2 x3 result);
  f_set_pre:
      v_Self ->
      v_N ->
      u8 ->
      (v_N & t13.Tls13crypto.t_HashAlgorithm & u8) ->
      t13.Tls13utils.t_Bytes
    -> Type0;
  f_set_post:
      v_Self ->
      v_N ->
      u8 ->
      (v_N & t13.Tls13crypto.t_HashAlgorithm & u8) ->
      t13.Tls13utils.t_Bytes ->
      v_Self
    -> Type0;
  f_set:
      x0: v_Self ->
      x1: v_N ->
      x2: u8 ->
      x3: (v_N & t13.Tls13crypto.t_HashAlgorithm & u8) ->
      x4: t13.Tls13utils.t_Bytes
    -> Prims.Pure v_Self (f_set_pre x0 x1 x2 x3 x4) (fun result -> f_set_post x0 x1 x2 x3 x4 result);
  f_hash_pre:t13.Tls13utils.t_Bytes -> Type0;
  f_hash_post:t13.Tls13utils.t_Bytes -> t13.Tls13utils.t_Bytes -> Type0;
  f_hash:x0: t13.Tls13utils.t_Bytes
    -> Prims.Pure t13.Tls13utils.t_Bytes (f_hash_pre x0) (fun result -> f_hash_post x0 result)
}

type t_TLSnames =
  | TLSnames_ES : t_TLSnames
  | TLSnames_EEM : t_TLSnames
  | TLSnames_CET : t_TLSnames
  | TLSnames_Bind : t_TLSnames
  | TLSnames_Binder : t_TLSnames
  | TLSnames_HS : t_TLSnames
  | TLSnames_SHT : t_TLSnames
  | TLSnames_CHT : t_TLSnames
  | TLSnames_HSalt : t_TLSnames
  | TLSnames_AS : t_TLSnames
  | TLSnames_RM : t_TLSnames
  | TLSnames_CAT : t_TLSnames
  | TLSnames_SAT : t_TLSnames
  | TLSnames_EAM : t_TLSnames
  | TLSnames_PSK : t_TLSnames
  | TLSnames_ZeroSalt : t_TLSnames
  | TLSnames_ESalt : t_TLSnames
  | TLSnames_KEM : t_TLSnames
  | TLSnames_ZeroIKM : t_TLSnames

type t_TLSkeyscheduler = {
  f_keys:Std.Collections.Hash.Map.t_HashMap (t_TLSnames & t13.Tls13crypto.t_HashAlgorithm & u8)
    t13.Tls13utils.t_Bytes
    Std.Hash.Random.t_RandomState
}

val t_TLSnames_cast_to_repr (x: t_TLSnames) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Clone.t_Clone t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_Copy t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:Core.Marker.t_StructuralPartialEq t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4:Core.Cmp.t_PartialEq t_TLSnames t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Cmp.t_Eq t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:Core.Hash.t_Hash t_TLSnames

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core.Fmt.t_Debug t_TLSnames

type t_Label =
  | Label_e__e__e__e__e__e__ : t_Label
  | Label_RES_BINDER_e_ : t_Label
  | Label_EXT_BINDER_e_ : t_Label
  | Label_C_E_TRAFFIC_ : t_Label
  | Label_E_EXP_MASTER : t_Label
  | Label_EXP_MASTER_e_ : t_Label
  | Label_RES_MASTER_e_ : t_Label
  | Label_C_HS_TRAFFIC : t_Label
  | Label_S_HS_TRAFFIC : t_Label
  | Label_DERIVED_e__e__ : t_Label
  | Label_C_AP_TRAFFIC : t_Label
  | Label_S_AP_TRAFFIC : t_Label
  | Label_RESUMPTION_e_ : t_Label

val t_Label_cast_to_repr (x: t_Label) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core.Fmt.t_Debug t_Label

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core.Marker.t_StructuralPartialEq t_Label

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core.Cmp.t_PartialEq t_Label t_Label

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11:Core.Cmp.t_Eq t_Label

val convert_label (label: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Option.t_Option t_Label) Prims.l_True (fun _ -> Prims.l_True)

val label_to_bytes (label: t_Label)
    : Prims.Pure t13.Tls13utils.t_Bytes Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_KeySchedule t_TLSkeyscheduler t_TLSnames

type t_TagKey = {
  f_alg:t13.Tls13crypto.t_HashAlgorithm;
  f_tag:t_TLSnames;
  f_val:t13.Tls13utils.t_Bytes
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12:Core.Clone.t_Clone t_TagKey

val xtr_alg (alg: t13.Tls13crypto.t_HashAlgorithm) (k1 k2: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val xpd_alg (alg: t13.Tls13crypto.t_HashAlgorithm) (k1 label d: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t13.Tls13utils.t_Bytes u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val xtr (k1 k2: t_TagKey)
    : Prims.Pure (Core.Result.t_Result t_TagKey u8) Prims.l_True (fun _ -> Prims.l_True)

val xpd (k1: t_TagKey) (label d: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_TagKey u8) Prims.l_True (fun _ -> Prims.l_True)

type t_Handle = {
  f_name:t_TLSnames;
  f_alg:t13.Tls13crypto.t_HashAlgorithm;
  f_level:u8
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13:Core.Clone.t_Clone t_Handle

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core.Fmt.t_Debug t_Handle

val xpd_angle
      (name: t_TLSnames)
      (label: t13.Tls13utils.t_Bytes)
      (parrent_handle: t_Handle)
      (args: t13.Tls13utils.t_Bytes)
    : Prims.Pure (Core.Result.t_Result t_Handle u8) Prims.l_True (fun _ -> Prims.l_True)

val set_by_handle (ks: t_TLSkeyscheduler) (handle: t_Handle) (key: t13.Tls13utils.t_Bytes)
    : Prims.Pure t_TLSkeyscheduler Prims.l_True (fun _ -> Prims.l_True)

/// Get an empty key of the correct size.
val zero_salt (ks: t_TLSkeyscheduler) (alg: t13.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (t_TLSkeyscheduler & t_Handle) Prims.l_True (fun _ -> Prims.l_True)

/// Get an empty key of the correct size.
val no_psk (ks: t_TLSkeyscheduler) (alg: t13.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (t_TLSkeyscheduler & t_Handle) Prims.l_True (fun _ -> Prims.l_True)

/// Get an empty key of the correct size.
val zero_ikm (ks: t_TLSkeyscheduler) (alg: t13.Tls13crypto.t_HashAlgorithm)
    : Prims.Pure (t_TLSkeyscheduler & t_Handle) Prims.l_True (fun _ -> Prims.l_True)

val get_by_handle (ks: t_TLSkeyscheduler) (handle: t_Handle)
    : Prims.Pure (Core.Option.t_Option t13.Tls13utils.t_Bytes)
      Prims.l_True
      (fun _ -> Prims.l_True)

val tagkey_from_handle (ks: t_TLSkeyscheduler) (handle: t_Handle)
    : Prims.Pure (Core.Result.t_Result t_TagKey u8) Prims.l_True (fun _ -> Prims.l_True)

val v_XPD
      (ks: t_TLSkeyscheduler)
      (n: t_TLSnames)
      (l: u8)
      (h1: t_Handle)
      (r: bool)
      (args: t13.Tls13utils.t_Bytes)
    : Prims.Pure (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
      Prims.l_True
      (fun _ -> Prims.l_True)

val xtr_angle (name: t_TLSnames) (left right: t_Handle)
    : Prims.Pure (Core.Result.t_Result t_Handle u8) Prims.l_True (fun _ -> Prims.l_True)

val v_XTR (ks: t_TLSkeyscheduler) (level: u8) (name: t_TLSnames) (h1 h2: t_Handle)
    : Prims.Pure (t_TLSkeyscheduler & Core.Result.t_Result t_Handle u8)
      Prims.l_True
      (fun _ -> Prims.l_True)
