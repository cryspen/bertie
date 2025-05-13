(* begin details : imports *)
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

Require Import Lia.

Import PackageNotation.
(* end details *)

(** * FunExt rewrite *)

Lemma function_fset_cons_l :
  forall {A : eqType} {T} x xs K,
    (fun (n : A) => fset (x n :: xs n) :|: K)
    = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n) :|: K).
Proof. now intros ; setoid_rewrite <- (fset_cat). Qed.

Lemma function_fset_cat_l :
  forall {A : eqType} {T} ys xs K,
    (fun (n : A) => fset (ys n ++ xs n) :|: K)
    = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n) :|: K).
Proof. now intros ; setoid_rewrite <- (fset_cat). Qed.

Lemma function_fset_cat_middle :
  forall {A : eqType} {T} ys xs L R,
    (fun (n : A) => L :|: fset (ys n ++ xs n) :|: R)
    = (fun (n : A) => L :|: fset (T := T) (ys n) :|: fset (xs n) :|: R).
Proof.
  intros.
  setoid_rewrite fsetUC.
  setoid_rewrite <- fsetUA.
  setoid_rewrite <- (fset_cat).
  reflexivity.
Qed.

Lemma function_fset_cat :
  forall {A : eqType} {T} ys xs,
    (fun (n : A) => fset (ys n ++ xs n))
    = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n)).
Proof. now setoid_rewrite <- (fset_cat). Qed.

Lemma function_fset_cons :
  forall {A : eqType} {T} x xs,
    (fun (n : A) => fset (x n :: xs n))
    = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n)).
Proof. now setoid_rewrite <- (fset_cat). Qed.

Lemma function2_fset_cat :
  forall {A B : eqType} {T} x xs,
    (fun (a : A) (b : B) => fset (x a b :: xs a b))
    = (fun (a : A) (b : B) => fset (T := T) ([x a b]) :|: fset (xs a b)).
Proof. now setoid_rewrite <- (fset_cat). Qed.
