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
From KeyScheduleTheorem Require Import Utility.

(*** Base Packages *)

Definition serialize_name  (n : name) (ℓ (* 0 .. d *) : nat) (d : nat) (index : nat) : nat :=
  let start := 100%nat in
  let size := 20%nat in
  (match n with
  | BOT => 0

  | ES => 1
  | EEM => 2
  | CET => 3
  | BIND => 4
  | BINDER => 5
  | HS => 6
  | SHT => 7
  | CHT => 8
  | HSALT => 9
  | AS => 10
  | RM => 11
  | CAT => 12
  | SAT => 13
  | EAM => 14
  | PSK => 15

  | ZERO_SALT => 16
  | ESALT => 17
  | DH => 18
  | ZERO_IKM => 19
  end%nat) + size * ℓ + index * size * d.+1 + start.

Lemma serialize_name_notin :
  forall d,
  forall (ℓ1 ℓ2 : nat),
    (ℓ2 >= ℓ1.+1)%N ->
    forall  (n1 n2 : name),
    forall index,
           serialize_name n1 ℓ1 d index \notin
             fset1 (T:=Datatypes_nat__canonical__Ord_Ord) (serialize_name n2 ℓ2 d index).
Proof.
  intros.
  unfold "\notin".
  rewrite !ifF ; [ reflexivity | ].
  unfold "\in"; simpl; unfold "\in"; simpl.
  destruct n1, n2 ; unfold serialize_name.
  all: try Lia.lia.
Qed.

Lemma serialize_name_notin_different_index :
  forall d,
  forall (ℓ1 ℓ2 : nat),
    (ℓ1 <= d)%N ->
    (ℓ2 <= d)%N ->
    forall  (n1 n2 : name),
    forall (index1 index2 : nat),
      (index1 <> index2)%nat ->
      serialize_name n1 ℓ1 d index1 \notin
        fset1 (T:=Datatypes_nat__canonical__Ord_Ord) (serialize_name n2 ℓ2 d index2).
Proof.
  intros.
  unfold "\notin".
  rewrite !ifF ; [ reflexivity | ].
  unfold "\in"; simpl; unfold "\in"; simpl.
  rewrite Bool.orb_false_r.

  unfold serialize_name.
  set 100%N.
  generalize dependent n.
  generalize dependent index1.
  induction index2.
  - intros.
    destruct index1 ; intros.
    {
      destruct n1, n2 ; unfold serialize_name.
      all: Lia.lia.
    }
    {
      destruct n1, n2 ; unfold serialize_name.
      all: Lia.lia.
    }
  - destruct index1 ; intros.
    {
      destruct n1, n2 ; unfold serialize_name.
      all: Lia.lia.
    }

    rewrite <- (mulnA index2.+1).
    rewrite (mulSnr index2).
    rewrite (mulnA index2).
    rewrite <- (addnA _ (_ + _)%nat n).
    rewrite <- (addnA _ (20 * d.+1)%nat _).
    rewrite addnA.

    rewrite <- (mulnA index1.+1).
    rewrite (mulSnr index1).
    rewrite (mulnA index1).
    rewrite <- (addnA _ (_ + _)%nat n).
    rewrite <- (addnA _ (20 * d.+1)%nat _).
    rewrite addnA.

    now apply IHindex2.
Qed.

#[global] Notation " 'chSETinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
#[global] Notation " 'chSETout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition SET (n : name) (ℓ : nat) (d : nat) := serialize_name n ℓ d 0.

#[global] Notation " 'chGETinp' " :=
  (chHandle)
    (in custom pack_type at level 2).
#[global] Notation " 'chGETout' " :=
  (chKey × 'bool)
    (in custom pack_type at level 2).
Definition GET (n : name) (ℓ : nat) (d : nat) := serialize_name n ℓ d 1.

Notation " 'chHASHinp' " :=
  (bitvec)
    (in custom pack_type at level 2).
Notation " 'chHASHout' " :=
  (bitvec)
    (in custom pack_type at level 2).
Definition HASH := 1%nat.

Definition len_ {n} (_ : 'I_ n) := n.
