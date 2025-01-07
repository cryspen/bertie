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

From KeyScheduleTheorem Require Import Types.
From KeyScheduleTheorem Require Import ExtraTypes.

(*** Utility *)

Definition get_or_case_fn (n : nat) (T : finType) (A : choiceType) `{Positive #|T|}
  (fn : raw_code A)
  (fnSucc : ('fin #|T|) -> raw_code A)
  : raw_code A :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  match k with
  | None =>
      fn
  | Some x =>
      fnSucc x
  end.

Definition get_or_fn (n : nat) (T : finType) `{Positive #|T|} (fn : raw_code ('fin #|T|)) : raw_code ('fin #|T|) :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  match k with
  | None =>
      fn
  | Some x =>
      ret x
  end.

Definition get_or_fail (n : nat) (T : finType) `{Positive #|T|} : raw_code ('fin #|T|) :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  match k with
  | None =>
      @fail ('fin #|T|) ;;
      ret (chCanonical 'fin #|T|)
  | Some x =>
      ret x
  end.

Definition get_has (n : nat) (T : finType) `{Positive #|T|} : raw_code 'bool :=
  k ← get (chOption ('fin #| T |) ; n ) ;;
  ret match k with
    | None =>
        false
    | Some x =>
        true
    end.

Definition set_at (n : nat) (T : finType) `{Positive #|T|} (x : T)
  : raw_code 'unit :=
  #put (chOption ('fin #| T |) ; n ) := Some (fto x) ;; ret Datatypes.tt.

Definition get_or_sample (n : nat) (T : finType) `{Positive #|T|} : raw_code ('fin #|T|) :=
  get_or_fn n T (
      x ← sample uniform #| T | ;;
      #put (chOption ('fin #| T |) ; n ) := Some x ;;
      ret x
    ).

Definition untag : chKey -> chKey := id.

Axiom xpn_eq : name -> name -> bool.

Axiom nfto : chName -> name.

Axiom len : chKey -> chNat (* TODO: should be key *).
Definition alg : chKey -> chHash := (fun x => fto (fst (otf x))). (* TODO: should be key *)
Axiom alg2 : chHandle -> chName (* TODO: should be key *).
Definition tag : chHash -> chName -> chKey (* TODO: should be key *) :=
  fun x y => fto (pair (otf x) (otf y)).
