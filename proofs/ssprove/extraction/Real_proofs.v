From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import word_ssrZ word.
(* From Jasmin Require Import word. *)

From Coq Require Import ZArith.
From Coq Require Import Strings.String.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

From HB Require Import structures.

From Crypt Require Import jasmin_word.

From Crypt Require Import Schnorr SigmaProtocol.

From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import PackageNotation.

(* Translated definitions *)

Definition t_HashAlgorithm : choice_type :=
  ('unit ∐ 'unit ∐ 'unit).
Notation "'HashAlgorithm_SHA256_case'" := (inl (inl tt)) (at level 100).
Equations HashAlgorithm_SHA256 : both t_HashAlgorithm :=
  HashAlgorithm_SHA256  :=
    solve_lift (ret_both (inl (inl (Datatypes.tt : chUnit)) : t_HashAlgorithm)) : both t_HashAlgorithm.
Fail Next Obligation.
Notation "'HashAlgorithm_SHA384_case'" := (inl (inr tt)) (at level 100).
Equations HashAlgorithm_SHA384 : both t_HashAlgorithm :=
  HashAlgorithm_SHA384  :=
    solve_lift (ret_both (inl (inr (Datatypes.tt : 'unit)) : t_HashAlgorithm)) : both t_HashAlgorithm.
Fail Next Obligation.
Notation "'HashAlgorithm_SHA512_case'" := (inr tt) (at level 100).
Equations HashAlgorithm_SHA512 : both t_HashAlgorithm :=
  HashAlgorithm_SHA512  :=
    solve_lift (ret_both (inr (Datatypes.tt : 'unit) : t_HashAlgorithm)) : both t_HashAlgorithm.
Fail Next Obligation.

Definition t_TLSnames : choice_type :=
  ('unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit ∐ 'unit).
Notation "'TLSnames_ES_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl Datatypes.tt)))))))))))))))))) (at level 100).
Program Definition TLSnames_ES : both t_TLSnames :=
  (ret_both _ ) : both t_TLSnames.
Next Obligation.
  ltac:(do 18 apply inl ; exact (Datatypes.tt : chUnit)).
Defined.
Fail Next Obligation.
Notation "'TLSnames_EEM_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))))))))))))) (at level 100).
Equations TLSnames_EEM : both t_TLSnames :=
  TLSnames_EEM  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_CET_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))))))))))))) (at level 100).
Equations TLSnames_CET : both t_TLSnames :=
  TLSnames_CET  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_Bind_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))))))))))) (at level 100).
Equations TLSnames_Bind : both t_TLSnames :=
  TLSnames_Bind  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_Binder_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))))))))))) (at level 100).
Equations TLSnames_Binder : both t_TLSnames :=
  TLSnames_Binder  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_HS_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))))))))) (at level 100).
Equations TLSnames_HS : both t_TLSnames :=
  TLSnames_HS  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_SHT_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))))))))) (at level 100).
Equations TLSnames_SHT : both t_TLSnames :=
  TLSnames_SHT  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_CHT_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))))))) (at level 100).
Equations TLSnames_CHT : both t_TLSnames :=
  TLSnames_CHT  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_HSalt_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))))))) (at level 100).
Equations TLSnames_HSalt : both t_TLSnames :=
  TLSnames_HSalt  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_AS_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))))) (at level 100).
Equations TLSnames_AS : both t_TLSnames :=
  TLSnames_AS  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_RM_case'" := (inl (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))))) (at level 100).
Equations TLSnames_RM : both t_TLSnames :=
  TLSnames_RM  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_CAT_case'" := (inl (inl (inl (inl (inl (inl (inl (inr Datatypes.tt)))))))) (at level 100).
Equations TLSnames_CAT : both t_TLSnames :=
  TLSnames_CAT  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_SAT_case'" := (inl (inl (inl (inl (inl (inl (inr Datatypes.tt))))))) (at level 100).
Equations TLSnames_SAT : both t_TLSnames :=
  TLSnames_SAT  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_EAM_case'" := (inl (inl (inl (inl (inl (inr Datatypes.tt)))))) (at level 100).
Equations TLSnames_EAM : both t_TLSnames :=
  TLSnames_EAM  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inl (inr (Datatypes.tt : 'unit))))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_PSK_case'" := (inl (inl (inl (inl (inr Datatypes.tt))))) (at level 100).
Equations TLSnames_PSK : both t_TLSnames :=
  TLSnames_PSK  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inl (inr (Datatypes.tt : 'unit)))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_ZeroSalt_case'" := (inl (inl (inl (inr Datatypes.tt)))) (at level 100).
Equations TLSnames_ZeroSalt : both t_TLSnames :=
  TLSnames_ZeroSalt  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inl (inr (Datatypes.tt : 'unit))))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_ESalt_case'" := (inl (inl (inr Datatypes.tt))) (at level 100).
Equations TLSnames_ESalt : both t_TLSnames :=
  TLSnames_ESalt  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inl (inr (Datatypes.tt : 'unit)))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_DH_case'" := (inl (inr Datatypes.tt)) (at level 100).
Equations TLSnames_DH : both t_TLSnames :=
  TLSnames_DH  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inl (inr (Datatypes.tt : 'unit))).
Defined.
Fail Next Obligation.
Notation "'TLSnames_ZeroIKM_case'" := (inr Datatypes.tt) (at level 100).
Equations TLSnames_ZeroIKM : both t_TLSnames :=
  TLSnames_ZeroIKM  :=
    solve_lift (ret_both (_ : t_TLSnames)) : both t_TLSnames.
Next Obligation.
  refine (inr (Datatypes.tt : 'unit)).
Defined.
Fail Next Obligation.

Definition t_Bytes : choice_type :=
  (t_Vec int8 t_Global).
Equations t_Bytes_0 (s : both t_Bytes) : both (t_Vec int8 t_Global) :=
  t_Bytes_0 s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : (t_Vec int8 t_Global)))) : both (t_Vec int8 t_Global).
Fail Next Obligation.
Equations Build_t_Bytes {t_Bytes_0 : both (t_Vec int8 t_Global)} : both (t_Bytes) :=
  Build_t_Bytes  :=
    bind_both t_Bytes_0 (fun t_Bytes_0 =>
      solve_lift (ret_both ((t_Bytes_0) : (t_Bytes)))) : both (t_Bytes).
Fail Next Obligation.
Notation "'Build_t_Bytes' '[' x ']' '(' '0' ':=' y ')'" := (Build_t_Bytes (t_Bytes_0 := y)).

Definition t_TagKey : choice_type :=
  (t_TLSnames × t_Bytes).
Equations f_tag (s : both t_TagKey) : both t_TLSnames :=
  f_tag s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst x : t_TLSnames))) : both t_TLSnames.
Fail Next Obligation.
Equations f_val (s : both t_TagKey) : both t_Bytes :=
  f_val s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : t_Bytes))) : both t_Bytes.
Fail Next Obligation.
Equations Build_t_TagKey {f_tag : both t_TLSnames} {f_val : both t_Bytes} : both (t_TagKey) :=
  Build_t_TagKey  :=
    bind_both f_val (fun f_val =>
      bind_both f_tag (fun f_tag =>
        solve_lift (ret_both ((f_tag,f_val) : (t_TagKey))))) : both (t_TagKey).
Fail Next Obligation.
Notation "'Build_t_TagKey' '[' x ']' '(' 'f_tag' ':=' y ')'" := (Build_t_TagKey (f_tag := y) (f_val := f_val x)).
Notation "'Build_t_TagKey' '[' x ']' '(' 'f_val' ':=' y ')'" := (Build_t_TagKey (f_tag := f_tag x) (f_val := y)).

Definition t_Handle : choice_type :=
  (t_TLSnames × t_Bytes × t_HashAlgorithm × int8).
Equations f_name (s : both t_Handle) : both t_TLSnames :=
  f_name s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst (fst (fst x)) : t_TLSnames))) : both t_TLSnames.
Fail Next Obligation.
Equations f_key (s : both t_Handle) : both t_Bytes :=
  f_key s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst (fst x)) : t_Bytes))) : both t_Bytes.
Fail Next Obligation.
Equations f_alg (s : both t_Handle) : both t_HashAlgorithm :=
  f_alg s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst x) : t_HashAlgorithm))) : both t_HashAlgorithm.
Fail Next Obligation.
Equations f_level (s : both t_Handle) : both int8 :=
  f_level s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : int8))) : both int8.
Fail Next Obligation.
Equations Build_t_Handle {L0 : {fset Location}} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I0 : Interface} {I1 : Interface} {I2 : Interface} {I3 : Interface} {f_name : both t_TLSnames} {f_key : both t_Bytes} {f_alg : both t_HashAlgorithm} {f_level : both int8} : both (t_Handle) :=
  Build_t_Handle  :=
    bind_both f_level (fun f_level =>
      bind_both f_alg (fun f_alg =>
        bind_both f_key (fun f_key =>
          bind_both f_name (fun f_name =>
            solve_lift (ret_both ((f_name,f_key,f_alg,f_level) : (t_Handle))))))) : both (t_Handle).
Fail Next Obligation.
Notation "'Build_t_Handle' '[' x ']' '(' 'f_name' ':=' y ')'" := (Build_t_Handle (f_name := y) (f_key := f_key x) (f_alg := f_alg x) (f_level := f_level x)).
Notation "'Build_t_Handle' '[' x ']' '(' 'f_key' ':=' y ')'" := (Build_t_Handle (f_name := f_name x) (f_key := y) (f_alg := f_alg x) (f_level := f_level x)).
Notation "'Build_t_Handle' '[' x ']' '(' 'f_alg' ':=' y ')'" := (Build_t_Handle (f_name := f_name x) (f_key := f_key x) (f_alg := y) (f_level := f_level x)).
Notation "'Build_t_Handle' '[' x ']' '(' 'f_level' ':=' y ')'" := (Build_t_Handle (f_name := f_name x) (f_key := f_key x) (f_alg := f_alg x) (f_level := y)).

(* Packages and proofs *)

(* From Bertie Require Import Bertie_Tls13keyscheduler. *)
(* Axiom xpd : forall (hash_algorithm : both t_HashAlgorithm) (key : both t_TagKey) (label : both t_Bytes) (transcript_hash : both t_Bytes), both (t_Result t_TagKey int8). *)
(* Axiom xpd_angle : forall (name : both t_TLSnames) (label : both t_Bytes) (parrent_handle : both t_Handle) (args : both t_Bytes), both (t_Result t_Handle int8). *)

Axiom xpd : forall (key : both t_TagKey) (label : both t_Bytes), both t_TagKey.

Notation " 'chSETInput' " :=
  ((t_Handle × t_Bytes) × t_TagKey)
    (in custom pack_type at level 2).

Notation " 'chSETOutput' " :=
  (chUnit)
    (in custom pack_type at level 2).

Notation " 'chGETInput' " :=
  (t_Handle)
    (in custom pack_type at level 2).

Notation " 'chGETOutput' " :=
  (t_TagKey)
    (in custom pack_type at level 2).

Notation " 'chXPDInput' " :=
  (t_Handle × t_Bytes)
    (in custom pack_type at level 2).

Notation " 'chXPDOutput' " :=
  (chUnit)
    (in custom pack_type at level 2).

Definition XPD : nat := 2.

Program Definition Xpd (GET : nat) (SET : nat) :
  package fset0
    [interface
       #val #[ GET ] : chGETInput → chGETOutput ;
       #val #[ SET ] : chSETInput → chSETOutput
    ]
    [interface
       #val #[ XPD ] : chXPDInput → chXPDOutput
    ]
  :=
  [package #def #[ XPD ] ('(p_handle, label) : chXPDInput) :
    chXPDOutput {
        #import {sig #[ GET ] : chGETInput → chGETOutput }
        as get_fn ;;
        #import {sig #[ SET ] : chSETInput → chSETOutput }
        as set_fn ;;
        key ← get_fn (p_handle) ;;
        xpd_val ← is_state (xpd (ret_both key) (ret_both (label : t_Bytes))) ;;
        set_fn ((p_handle, label), xpd_val) ;;
        ret Datatypes.tt
      }
  ].
Next Obligation.
Admitted.
Fail Next Obligation.

Program Definition Key_real (SET : nat) (GET : nat) :
  package fset0
    [interface]
    [interface
       #val #[ SET ] : chSETInput → chSETOutput ;
       #val #[ GET ] : chGETInput → chGETOutput
    ]
  :=
  [package
     #def #[ SET ] ('(p_handle, label) : chSETInput) :
    chSETOutput {
        ret Datatypes.tt (* TODO *)
      };
   #def #[ GET ] ('(p_handle) : chGETInput) :
     chGETOutput {
         ret (fst (fst p_handle)) (* TODO *)
       }

  ].
Next Obligation.
Admitted.
Fail Next Obligation.

Program Definition Key_ideal (SET : nat) (GET : nat) :
  package fset0
    [interface]
    [interface
       #val #[ SET ] : chSETInput → chSETOutput ;
       #val #[ GET ] : chGETInput → chGETOutput
    ]
  :=
  [package
     #def #[ SET ] ('(p_handle, label) : chSETInput) :
    chSETOutput {
        ret Datatypes.tt (* TODO *)
      };
   #def #[ GET ] ('(p_handle) : chGETInput) :
     chGETOutput {
         ret (fst (fst p_handle)) (* TODO *)
       }

  ].
Next Obligation.
Admitted.
Fail Next Obligation.

Definition Key_game (SET : nat) (GET : nat) :
  loc_GamePair [interface
       #val #[ SET ] : chSETInput → chSETOutput ;
       #val #[ GET ] : chGETInput → chGETOutput
    ] :=
  λ b,
    if b then {locpackage Key_ideal SET GET} else {locpackage Key_real SET GET}.

Notation " 'chGXPDInput' " :=
  (t_HashAlgorithm × t_Bytes × t_Bytes)
    (in custom pack_type at level 2).

Notation " 'chGXPDOutput' " :=
  (t_Result t_TagKey int8)
    (in custom pack_type at level 2).

Definition GXPD : nat := 101.

Program Definition Gxpd (SET0 : nat) (GET1 : nat)  (SET1 : nat) (GET2 : nat) :
  loc_GamePair [interface
       #val #[ XPD ] : chXPDInput → chXPDOutput
    ] :=
  λ b,
    {locpackage (
         {package Xpd GET1 SET1 ∘ (par (Key_game SET0 GET1 true) (Key_game SET1 GET2 b))}
         : package fset0 [interface] [interface
       #val #[ XPD ] : chXPDInput → chXPDOutput
    ])}.
Next Obligation.
  refine fset0.
Defined.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Fail Next Obligation.

Lemma advantage_Gxpd_b :
  forall (SET0 : nat) (GET1 : nat)  (SET1 : nat) (GET2 : nat),
  ∀ (LA : {fset Location}) (A : raw_package),
    ValidPackage LA [interface #val #[ XPD ] : chXPDInput → chXPDOutput ] A_export A →
    (AdvantageE
       (Gxpd SET0 GET1 SET1 GET2 false)
       (Gxpd SET0 GET1 SET1 GET2 true)
       A = 0)%R.
Proof.
  intros.

  apply: eq_rel_perf_ind_ignore.
  1: (apply fsubsetxx || solve_in_fset || shelve).
  2,3: apply fdisjoints0.

  simplify_eq_rel inp_unit.

  repeat choice_type_eqP_handle.
  unfold code_link.

  fold chElement.
Admitted.

Definition get_or_fn (n : nat) (T : finType) `{Positive #|T|} (fn : raw_code T) : raw_code T :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  match k with
  | None =>
      fn
  | Some x =>
      ret (otf x)
  end.

Definition get_or_sample (n : nat) (T : finType) `{Positive #|T|} : raw_code T :=
  get_or_fn n T (
      x ← sample uniform #| T | ;;
      #put (chOption ('fin #| T |) ; n ) := Some x ;;
      ret (otf x)
    ).

Parameter A : finType.
Instance A_pos : Positive #|A|. Admitted.
Definition A_choice : choice_type := 'fin #|A|.

Notation " 'chEVALInput' " :=
  (A_choice)
    (in custom pack_type at level 2).

Notation " 'chEVALOutput' " :=
  (A_choice)
    (in custom pack_type at level 2).

Axiom key_to_bytes : forall n, 'I_n -> t_Bytes.

Definition EVAL : nat := 20.
Definition eval_loc : Location := ( t_Option (t_Bytes) ; 0%nat ).

Program Definition Eval_real (f_alg : A -> A_choice -> both A_choice) :
  package (fset [eval_loc])
    [interface
    ]
    [interface
       #val #[ EVAL ] : chEVALInput → chEVALOutput
    ]
  :=
  [package
     #def #[ EVAL ] (x : chEVALInput) :
    chEVALOutput {
        k ← get_or_sample 0%nat A  ;;
        is_state (f_alg k x)
      }
  ].
Next Obligation.
  admit.
Admitted.
Fail Next Obligation.

Program Definition Eval_ideal (T : A_choice -> nat) :
  package (fset [eval_loc])
    [interface
    ]
    [interface
       #val #[ EVAL ] : chEVALInput → chEVALOutput
    ]
  :=
  [package
     #def #[ EVAL ] (x : chEVALInput) :
    chEVALOutput {
        get_or_sample (T x) A
      }
  ].
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
Fail Next Obligation.

Definition G_eval (T : A_choice -> nat) (f_alg : A -> A_choice -> both A_choice) :
  loc_GamePair [interface
       #val #[ EVAL ] : chEVALInput → chEVALOutput
    ] :=
  λ b,
    if b then {locpackage (Eval_ideal T)} else {locpackage (Eval_real f_alg)}.

Notation " 'chHASHInput' " :=
  (A_choice)
    (in custom pack_type at level 2).

Notation " 'chHASHOutput' " :=
  (A_choice)
    (in custom pack_type at level 2).

Definition HASH : nat := 10.
Program Definition Hash_Gpr_Gcr (H : A_choice -> nat) (b : bool) (in_range : A_choice -> bool) :
  package fset0
    [interface
       #val #[ EVAL ] : chEVALInput → chEVALOutput
    ]
    [interface
       #val #[ HASH ] : chHASHInput → chHASHOutput
    ]
  :=
  [package
     #def #[ HASH ] (t : chHASHInput) :
    chHASHOutput {
        #import {sig #[ EVAL ] : chEVALInput → chEVALOutput }
        as eval_fn ;;
        d ← eval_fn t ;;
        get_or_fn (H t) A (
            if b && (in_range d)
            then x ← @fail A_choice ;; ret (otf x)
            else ret (otf d)) ;;
        ret d
      }
  ].
Next Obligation.
  admit.
Admitted.
Fail Next Obligation.

Program Definition Gpr
  (SET0 : nat) (GET1 : nat)  (SET1 : nat) (GET2 : nat) (H : A_choice -> nat) (in_range : A_choice -> bool) :
  loc_GamePair [interface
       #val #[ HASH ] : chHASHInput → chHASHOutput
    ] :=
  λ b,
    {locpackage (
         {package Hash_Gpr_Gcr H b in_range ∘ G_eval _ _ b}
         : package fset0 [interface] [interface
       #val #[ HASH ] : chHASHInput → chHASHOutput
    ])}.
Next Obligation.
  refine fset0.
Defined.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Fail Next Obligation.

Parameter gT : finGroupType.
Parameter g :  gT.

Definition GroupSpace : finType := gT.
#[local] Instance GroupSpace_pos : Positive #|GroupSpace|.
Proof.
  apply /card_gt0P; by exists g.
  (* Needs to be transparent to unify with local positivity proof? *)
Defined.

Definition chGroup : choice_type := 'fin #|GroupSpace|.
Definition q : nat := <[g]>.

(* begin details : Positivity checks *)
#[export] Instance positive_zq : Positive #|'Z_q|.
Proof.
  apply /card_gt0P. exists 0. auto.
Qed.

Notation " 'chDHGENInput' " :=
  (chGroup)
    (in custom pack_type at level 2).

Notation " 'chDHGENOutput' " :=
  (chGroup)
    (in custom pack_type at level 2).


Definition DHGEN : nat := 14.

Notation " 'chXTRInput' " :=
  (chGroup × chGroup × chGroup)
    (in custom pack_type at level 2).

Notation " 'chXTROutput' " :=
  (chGroup)
    (in custom pack_type at level 2).

Definition XTR : nat := 15.

Definition is_some {A} (x : option A) : bool := match x with | (Some _) => true | _ => false end.

Program Definition Xtr (L : gT -> nat) (S : chGroup -> chGroup -> nat) (b : bool) (dh : chGroup × chGroup -> chGroup) (sort : chGroup -> chGroup -> chGroup × chGroup) (xtr_alg : chGroup -> chGroup -> chGroup) :
  package fset0
    [interface]
    [interface
       #val #[ DHGEN ] : chDHGENInput → chDHGENOutput ;
       #val #[ XTR ] : chXTRInput → chXTROutput
    ]
  :=
  [package
     #def #[ DHGEN ] (grp : chDHGENInput) : chDHGENOutput {
        (* g ← gen grp ;; *)
        (* q ← ord g ;; *)
        x ← sample (uniform #|'Z_q| (H := positive_zq)) ;;
        X ← ret (g ^+ otf x) ;;
        #put ( chOption ('fin #| 'Z_q |) ; L X) := Some x ;;
        ret (fto X)
    } ;
   #def #[ XTR ] ('(X, Y, salt) : chXTRInput) : chXTROutput {
        k ← get ( chOption ('fin #| 'Z_q |) ; L (otf X)) ;;
        assert (Datatypes.andb (is_some k) (X == Y)) ;;
        (* alg = salt.alg ;; *)
        k ← get ( chOption ('fin #| 'Z_q |) ; L (otf Y)) ;;
        if Datatypes.andb b (Datatypes.negb (is_some k))
        then
          (h ← ret (dh (sort X Y)) ;;
           t ← get_or_sample (S h salt) (GroupSpace) ;;
           ret (fto t))
        else
          ret (xtr_alg salt (fto ((otf Y : gT) ^+ L (otf X))))
   }
  ].
Next Obligation.
Admitted.
Fail Next Obligation.
