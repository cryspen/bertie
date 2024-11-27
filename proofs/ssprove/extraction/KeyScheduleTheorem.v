
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

(*** Key Schedule theorem *)

Notation " 'chTranscript' " :=
  (t_Handle)
    (in custom pack_type at level 2).

Definition KS : nat := 0%nat.

(* Fig. 12, p. 18 *)
(* Fig.29, P.63 *)

Inductive name :=
| N | PSK | ESALT
| ES
| HS
| AS.
Definition bitvec := chFin (mkpos (Nat.pow 2 96)). (* {0,1}^96 *)
Definition chName : choice_type := chFin (mkpos 6).

(* Base handles are defined on p. 16 *)
(* Definition handle := chName × t_Bytes × t_HashAlgorithm × int8. *)
Definition calc_handle_size := ( 6 + Nat.pow 2 96 + 3 + Nat.pow 2 256 ).
Definition chHandle : choice_type := chFin (mkpos calc_handle_size).

Axiom chName_to_name : chName -> name.

Axiom xpd_square : name -> bitvec -> chHandle -> bitvec -> raw_code chHandle.

Inductive XPR :=
| XPR_N
| XPR_PSK
| XPR_ESALT.

Inductive O_star := TODO.

Notation " 'chSET' " :=
  ('unit × 'unit)
    (in custom pack_type at level 2).
Definition SET_psk (i : nat) : nat := 10.

Definition DHGEN : nat := 11.
Definition DHEXP : nat := 12.

Notation " 'chXTRinp' " :=
  (chHandle × chHandle)
    (in custom pack_type at level 2).
Notation " 'chXTRout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition XTR (n : name) (ℓ (* 0 .. d *) : nat) : nat := 13.

Fixpoint XTR_n_ℓ (d : nat) :=
  match d with
  | O => [interface]
  | S d' =>
      [interface
       #val #[ XTR ES d' ] : chXTRinp → chXTRout ;
       #val #[ XTR HS d' ] : chXTRinp → chXTRout ;
       #val #[ XTR AS d' ] : chXTRinp → chXTRout
      ] :|: XTR_n_ℓ d'
  end.

Notation " 'chXPDinp' " :=
  (chHandle × 'bool × bitvec)
    (in custom pack_type at level 2).
Notation " 'chXPDout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition XPD (n : name) (ℓ : nat) : nat := 13.

Fixpoint XPD_n_ℓ (d : nat) :=
  match d with
  | O => [interface]
  | S d' =>
      [interface
       #val #[ XPD N d' ] : chXPDinp → chXPDout ;
       #val #[ XPD PSK d' ] : chXPDinp → chXPDout ;
       #val #[ XPD ESALT d' ] : chXPDinp → chXPDout
      ] :|: XPD_n_ℓ d'
  end.


Definition GET (n : O_star) (ℓ : nat) : nat := 13.

Fixpoint GET_o_star_ℓ (d : nat) :=
  match d with
  | O => [interface]
  | S d' =>
      [interface
       #val #[ GET TODO d' ] : 'unit → 'unit
      ] :|: GET_o_star_ℓ d'
  end.

Definition UNQ (n : O_star) : nat := 14.

Definition UNQ_o_star :=
  [interface
     #val #[ UNQ TODO ] : 'unit → 'unit
  ].


Definition get_or_fn (n : nat) (T : finType) `{Positive #|T|} (fn : raw_code T) : raw_code T :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  match k with
  | None =>
      fn
  | Some x =>
      ret (otf x)
  end.

Definition set_at (n : nat) (T : finType) `{Positive #|T|} (x : T)
  : raw_code 'unit :=
  #put (chOption ('fin #| T |) ; n ) := Some (fto x) ;; ret Datatypes.tt.

Definition get_or_sample (n : nat) (T : finType) `{Positive #|T|} : raw_code T :=
  get_or_fn n T (
      x ← sample uniform #| T | ;;
      #put (chOption ('fin #| T |) ; n ) := Some x ;;
      ret (otf x)
    ).

Instance pos_unit : Positive #|'unit| :=
  eq_ind_r [eta Positive] (erefl : Positive 1) card_unit.

Instance pos_chName : Positive #|chName| :=
  eq_ind_r [eta Positive] (erefl : Positive 6) (card_ord 6).

Instance pos_chHandle : Positive #|chHandle| :=
  eq_ind_r [eta Positive] (erefl : Positive calc_handle_size) (card_ord calc_handle_size).

Axiom PrntIdx : name -> bitvec -> name × name.

(* p. 5,6 *)
Axiom xtr_square : name -> chHandle -> chHandle -> raw_code chHandle.

Axiom XTR_LABAL_from_index : nat -> name.

Axiom nfto : chName -> name.

Program Definition R_ch_map_XTR_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) :
  package fset0 (XTR_n_ℓ ℓ)
    [interface
       #val #[ XTR n ℓ ] : chXTRinp → chXTRout
    ]
  :=
  [package
     #def #[ XTR n ℓ ] ('(h1,h2) : chXTRinp) : chXTRout {
        '(i1,i2) ← ret (_ : chProd chName chName) (* (PrntIdx n d') *) ;;
        temp1 ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret _) ;;
        temp2 ← get_or_fn (M (nfto i2) h2) chHandle (@fail _ ;; ret _) ;;
        ℓ' ← (*choos*) ret ((ℓ-1)%nat : 'nat (* TODO *)) ;;
        #import {sig #[ XTR n ℓ' ] : chXTRinp → chXTRout }
        as XTR_fn ;;
        h ← xtr_square n h1 h2 ;;
        h' ← XTR_fn (fto temp1, fto temp2) ;;
        set_at (M n h) chHandle h' ;;
        ret h
      }
  ].
Admit Obligations.
Fail Next Obligation.

Program Fixpoint R_ch_map_XTR_packages (d : nat) (M : chHandle -> nat) :
  package fset0 (XTR_n_ℓ d) (XTR_n_ℓ d) :=
  match d with
  | O => [package]
  | S d' => (fun x => _) (R_ch_map_XTR_packages d' M)
      (* {package (par _ )} *)
  end.
Next Obligation.
  refine {package (par _ x)}.
  Unshelve.
  2:{
    epose (R_ch_map_XTR_package d' ES (fun _ => M)).
    epose (R_ch_map_XTR_package d' AS (fun _ => M)).
    epose (R_ch_map_XTR_package d' HS (fun _ => M)).

    epose (par (par p p0) p1).
    refine f.
  }
  unfold pack.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + eapply valid_par_upto.
      * admit.
      * apply (R_ch_map_XTR_package d' ES (λ _, M)).
      * apply (R_ch_map_XTR_package d' AS (λ _, M)).
      * solve_in_fset.
      * apply fsubsetxx.
      * apply fsubsetxx.
    + apply (R_ch_map_XTR_package d' HS (λ _, M)).
    + apply fsubsetxx.
    + apply fsubsetxx.
    + apply fsubsetxx.
  - apply x.
  - rewrite !fsetU0.
    apply fsubsetxx.
  - rewrite !fsetUid.
    solve_in_fset.
  - rewrite <- !fset_cat. simpl.
    apply fsubsetxx.
Admitted.
Fail Next Obligation.

Axiom Labels : name -> bool -> raw_code bitvec.

Axiom XPN_LABAL_from_index : nat -> name.

Axiom xpn_eq : name -> name -> bool.

Definition R_ch_map_XPD_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) (M_ℓ : name -> nat -> chHandle -> nat) :
  package fset0 (XPD_n_ℓ ℓ)
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  refine [package
     #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
        '(i1,_) ← ret (_ : chProd chName chName) (* (PrntIdx n d') *) ;;
        temp ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret (chCanonical chHandle)) ;;
        ℓ1 ← (*choos*) ret ((ℓ-1)%nat : 'nat (* TODO *)) ;;
        #import {sig #[ XPD n ℓ1 ] : chXPDinp → chXPDout }
        as XPD_fn ;;
        label ← Labels n r ;;
        h ← xpd_square n label h1 args ;;
        h' ← XPD_fn (temp, r, args) ;;
        ℓ ← ret (if xpn_eq n PSK then (ℓ + 1) else ℓ) ;;
        set_at (M_ℓ n ℓ h) chHandle (h') ;;
        ret h
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

Program Fixpoint R_ch_map_XPD_packages (d : nat) (M : chHandle -> nat) :
  package fset0 (XPD_n_ℓ d) (XPD_n_ℓ d) :=
  match d with
  | O => [package]
  | S d' =>
      _ (R_ch_map_XPD_packages d' M)
      (* {package (par _ (R_ch_map_XPD_packages d' M)) #with valid_par_upto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ } *)
      (* {package (par _ )} *)
  end.
Next Obligation.
  refine {package (par _ x)}.
  Unshelve.
  2:{
    epose (R_ch_map_XPD_package d' N (fun _ => M) (fun _ _ => M)).
    epose (R_ch_map_XPD_package d' PSK (fun _ => M) (fun _ _ => M)).
    epose (R_ch_map_XPD_package d' ESALT (fun _ => M) (fun _ _ => M)).

    epose (par (par p p0) p1).
    refine f.
  }
  unfold pack.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + eapply valid_par_upto.
      * admit.
      * apply (R_ch_map_XPD_package d' N (λ _, M) (λ _ _, M)).
      * apply (R_ch_map_XPD_package d' PSK (λ _, M) (λ _ _, M)).
      * solve_in_fset.
      * apply fsubsetxx.
      * apply fsubsetxx.
    + apply (R_ch_map_XPD_package d' ESALT (λ _, M) (λ _ _, M)).
    + apply fsubsetxx.
    + apply fsubsetxx.
    + apply fsubsetxx.
  - apply x.
  - rewrite !fsetU0.
    apply fsubsetxx.
  - rewrite !fsetUid.
    solve_in_fset.
  - rewrite <- !fset_cat. simpl.
    apply fsubsetxx.
Admitted.

(* R_ch_map, fig.25, Fig. 27, Fig. 29 *)
Program Definition R_ch_map (d : nat) (M : 'unit -> nat) :
  package fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
  :=
  let base_package : package fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d) ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ])
  :=
    [package
     #def #[ SET_psk 0 ] ('(h,hon) : chSET) : 'unit {
        #import {sig #[ SET_psk 0 ] : 'unit → 'unit }
        as set_fn ;;
        nh ← set_fn h ;;
        set_at (M h) 'unit nh ;;
        ret h
      } ;
   #def #[ DHGEN ] (t : 'unit) : 'unit {
        #import {sig #[ DHGEN ] : 'unit → 'unit }
        as dhgen ;;
        dhgen Datatypes.tt
      } ;
     #def #[ DHEXP ] (t : 'unit) : 'unit {
        ret (Datatypes.tt : 'unit)
      }
    ]
  in
  {package
     par (base_package
     ) (R_ch_map_XTR_packages _ _) }.
Admit Obligations.
Fail Next Obligation.

(* Fig 12. the real XPD and XTR games *)

Definition Xpd
  (n : name) (ℓ : nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code bitvec)
  :
  package
    fset0
    [interface]
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  refine [package
     #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
        '(n1,_) ← PrntN n ;;
        label ← Labels n r ;;
        h ← xpd_square n label h1 args ;;
        ret h
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

(* R-M-Pr-io^xpd - Interesting Fig 45., Fig.51-55 *)

(* Fig.11, p.17 *)
Program Definition Gks_real (d : nat) (M : 'unit -> nat) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ]
  :=
  [package
  ].
Admit Obligations.
Fail Next Obligation.

Definition Simulator d :=
  (package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d)
    [interface
    ]
  ).

Axiom Key_o_star_ideal : forall (d : nat), package
    fset0
    (GET_o_star_ℓ d)
    (UNQ_o_star).

Program Definition Gks_ideal d (M : 'unit -> nat)
  (S : package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d)
    [interface
    ]
  ) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ]
  :=
  {package S ∘ Key_o_star_ideal d }.
Admit Obligations.
Fail Next Obligation.


Axiom Gcore_real : package fset0 [interface] [interface].
Program Definition Gcore_ideal (d : nat) (Score : Simulator d) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ] := {package (Score ∘ Key_o_star_ideal d) }.
Admit Obligations.
Fail Next Obligation.

Program Definition Gks_real_map (d : nat) (M : 'unit -> nat) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ] :=
  {package (R_ch_map d M ∘ Gcore_real) }.
Admit Obligations.
Fail Next Obligation.

Program Definition Gks_ideal_map (d : nat) (M : 'unit -> nat) (Score : Simulator d) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSET → 'unit ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ] := {package (R_ch_map d M ∘ Gcore_ideal d Score) }.
Admit Obligations.
Fail Next Obligation.

Lemma map_reduction :
  forall (d : nat) (M : 'unit -> nat),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real d M)
       (Gks_ideal d M Score) A =
     AdvantageE
       (Gks_real_map d M)
       (Gks_ideal_map d M Score) A
    )%R.
Proof.
  intros.
  unfold Gks_real.
  unfold Gks_ideal.
  unfold Gks_real_map.
  unfold Gks_ideal_map.
  unfold pack.
  rewrite <- Advantage_link.
Admitted.

Lemma main_reduction :
  forall (d : nat) (M : 'unit -> nat),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real d M)
       (Gks_ideal d M Score) A =
     AdvantageE
       (Gcore_real)
       (Gcore_ideal d Score) (A ∘ R_ch_map d M)
    )%R.
Proof.
  intros.
  rewrite map_reduction.
  unfold Gks_real_map , Gks_ideal_map , pack.
  rewrite <- Advantage_link.
  unfold Gcore_ideal.
  reflexivity.
Qed.

Axiom R_cr : package fset0 [interface] [interface].
Axiom R_Z : package fset0 [interface] [interface].
Axiom R_D : package fset0 [interface] [interface].

Fixpoint sum_accum (fuel : nat) (index : nat) (f : nat -> nat) (accum : nat) : nat :=
  match fuel with
  | O => accum
  | S n' => sum_accum n' (index + 1%nat) f (accum + f index)
  end.

Axiom sum : nat -> nat -> (nat -> R) -> R.

Axiom sum_le : forall l u f g, (forall v, (f v <= g v)) -> (sum l u f <= sum l u g).

Axiom sum_l : forall {T : Type}, list T -> (T -> R) -> R.
(* Definition sum (l u : nat) (f : nat -> nat) : nat := sum_accum (u - l) l f 0%R. *)

Axiom Gacr :
    loc_GamePair
      [interface
         (* #val #[ ACR ] : 'unit → 'unit *)
      ].

Axiom Gsodh :
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

Axiom Ai : raw_package -> bool -> raw_package.
Axiom R_sodh : package fset0 [interface] [interface].

Definition max_val : R -> R -> R :=
  fun x y =>
    if x > y
    then x
    else y.

Definition max (f : bool -> R) : R :=
  max_val (f false) (f true).

Axiom max_leq : forall f g, (forall b, f b <= g b) -> max f <= max g.

Axiom Gcore_sodh : package fset0 [interface] [interface].

Lemma core_theorem :
  forall (d : nat) (M : 'unit -> nat),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gcore_real)
       (Gcore_ideal d Score) (A ∘ R_ch_map d M)
     <= sum_l [R_cr; R_Z; R_D] (fun R => Advantage Gacr (A ∘ R))
     +max (fun i => Advantage Gsodh (Ai A i ∘ R_sodh) + AdvantageE Gcore_sodh (Gcore_ideal d Score) (Ai A i))
    )%R.
Proof. Admitted.

Axiom Gcore_ki : package fset0 [interface] [interface].
Axiom Gcore_hyb : nat -> package fset0 [interface] [interface].

Lemma equation20_lhs :
  forall (d : nat),
  forall (Score : Simulator d),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_sodh (Gcore_hyb 0) (Ai A i) = 0)%R.
Proof. Admitted.

Lemma equation20_rhs :
  forall (d : nat),
  forall (Score : Simulator d),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_ki (Gcore_hyb d) (Ai A i) = 0)%R.
Proof. Admitted.

Lemma hyb_telescope :
  forall (d : nat),
  forall (Score : Simulator d),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
      (AdvantageE (Gcore_hyb 0) (Gcore_hyb d) (Ai A i)
       = sum 0 (d-1) (fun ℓ => AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ+1)) (Ai A i))
      )%R.
Proof. Admitted.

Lemma equation20_eq :
  forall (d : nat),
  forall (Score : Simulator d),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_sodh (Gcore_ideal d Score) (Ai A i)
     <= AdvantageE Gcore_ki (Gcore_ideal d Score) (Ai A i)
     +sum 0 (d-1) (fun ℓ => AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ + 1)) (Ai A i))
    )%R.
Proof.
  intros.

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := (Gcore_hyb 0)).
  rewrite (equation20_lhs d Score).
  rewrite add0r.

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := Gcore_ki).
  rewrite addrC.
  apply Num.Theory.lerD ; [ easy | ].

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := (Gcore_hyb d)).

  epose (e := equation20_rhs d Score).
  setoid_rewrite (Advantage_sym _ _) in e.
  rewrite e ; clear e.
  rewrite addr0.

  setoid_rewrite <- hyb_telescope ; easy.
Qed.

Axiom ε_acr : R.
Axiom ε_sodh_ki : bool -> R.

Axiom R_es : nat -> package fset0 [interface] [interface].
Axiom Gxtr_es : nat -> loc_GamePair
      [interface
         (* #val #[ ES ] : 'unit → 'unit *)
      ].

Axiom R_as : nat -> package fset0 [interface] [interface].
Axiom Gxtr_as : nat -> loc_GamePair
      [interface
         (* #val #[ AS ] : 'unit → 'unit *)
      ].

Axiom R_hs : nat -> package fset0 [interface] [interface].
Axiom Gxtr_hs : nat -> loc_GamePair
      [interface
         (* #val #[ HS ] : 'unit → 'unit *)
      ].

Axiom Gxpd : XPR -> nat -> loc_GamePair
      [interface
         (* #val #[ ES ] : 'unit → 'unit *)
      ].


Axiom R_ : XPR -> nat -> package fset0 [interface] [interface].

Ltac split_advantage O :=
  try apply (AdvantageE_le_0 _ _ _ ) ;
  eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
  replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
      symmetry ] ; revgoals.

Axiom ki_hybrid :
  forall (ℓ : nat),
  forall (LA : {fset Location}) (A : raw_package),
  forall i,
    ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
  AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ + 1)) (Ai A i) <=
  Advantage (λ x : bool, Gxtr_es ℓ x) (Ai A i ∘ R_es ℓ) + Advantage (λ x : bool, Gxtr_hs ℓ x) (Ai A i ∘ R_hs ℓ) +
    Advantage (λ x : bool, Gxtr_as ℓ x) (Ai A i ∘ R_as ℓ) + sum_l [:: XPR_N; XPR_PSK; XPR_ESALT] (λ n : XPR, Advantage (λ x : bool, Gxpd n ℓ x) (Ai A i ∘ R_ n ℓ)).

Lemma key_schedule_theorem :
  forall (d : nat) (M : 'unit -> nat),
  forall (S : Simulator d),
  forall (hash : nat),
  forall (LA : {fset Location}) (A : raw_package),
    ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
  forall (H_ε_acr : sum_l [:: R_cr; R_Z; R_D] (λ R : package f_parameter_cursor_loc (fset [::]) (fset [::]), Advantage (λ x : bool, Gacr x) (A ∘ R)) <= ε_acr),
  forall (H_ε_sodh_ki : (forall i, Advantage (λ x : bool, Gsodh x) (Ai A i ∘ R_sodh) + AdvantageE Gcore_ki (Gcore_ideal d S) (Ai A i) <= ε_sodh_ki i)%R),
    (AdvantageE
       (Gks_real d M)
       (Gks_ideal d M S) A <=
     ε_acr +
     max (fun i =>
      ε_sodh_ki i
      +sum 0 (d-1) (fun ℓ =>
         Advantage (Gxtr_es ℓ) (Ai A i ∘ R_es ℓ)
        +Advantage (Gxtr_hs ℓ) (Ai A i ∘ R_hs ℓ)
        +Advantage (Gxtr_as ℓ) (Ai A i ∘ R_as ℓ)
        +sum_l [XPR_N; XPR_PSK; XPR_ESALT] (fun n => Advantage (Gxpd n ℓ) (Ai A i ∘ R_ n ℓ)
       )))
    )%R.
Proof.
  intros.
  rewrite main_reduction.

  eapply Order.le_trans.
  - eapply (core_theorem _ _ _ _ _).
    apply H.
  - apply Num.Theory.lerD ; [ apply H_ε_acr | ].
    apply max_leq.
    intros i.

    eapply Order.le_trans.
    + apply Num.Theory.lerD ; [ easy | ].
      epose (equation20_eq d S i).
      eapply i0.
      easy.
    + rewrite addrA.
      apply Num.Theory.lerD ; [ apply H_ε_sodh_ki | ].
      apply sum_le.
      intros ℓ.
      eapply ki_hybrid.
      easy.
Qed.

(*** Concrete instance *)

Theorem Advantage_xtr_es :
  forall A ℓ i ε_dt,
    Advantage (Gxtr_es ℓ) (Ai A i ∘ R_es ℓ) <= ε_dt.
Proof.
  intros.
Admitted.
