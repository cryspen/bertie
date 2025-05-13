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

From KeyScheduleTheorem Require Import ExtraTypes.
(* From KeyScheduleTheorem Require Import ssp_helper. *)

(** * Serialize name *)

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
    (ℓ2 <> ℓ1)%N ->
    forall  (n1 n2 : name),
    forall index,
      serialize_name n1 ℓ1 d index <> serialize_name n2 ℓ2 d index.
Proof.
  intros.
  destruct n1, n2 ; unfold serialize_name.
  all: try Lia.lia.
Qed.

Lemma serialize_name_notin_different_name :
  forall d,
  forall (ℓ1 ℓ2 : nat),
  forall (n1 n2 : name),
    (n1 <> n2)%N ->
    forall index,
      serialize_name n1 ℓ1 d index <> serialize_name n2 ℓ2 d index.
Proof.
  intros.
  unfold "\notin".
  destruct n1, n2 ; unfold serialize_name.
  all: try (Lia.nia || contradiction).
Qed.

Lemma serialize_name_notin_different_index :
  forall d,
  forall (ℓ1 ℓ2 : nat),
    (ℓ1 <= d)%N ->
    (ℓ2 <= d)%N ->
    forall  (n1 n2 : name),
    forall (index1 index2 : nat),
      (index1 <> index2)%nat ->
      serialize_name n1 ℓ1 d index1 <> serialize_name n2 ℓ2 d index2.
Proof.
  intros.

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

    apply IHindex2 ; eauto.
Qed.

Lemma serialize_name_notin_smaller_than_start :
  forall d,
  forall (ℓ : nat),
  forall  (n : name),
  forall (index : nat),
  forall k,
    (k < 100)%nat ->
    serialize_name n ℓ d index <> k.
Proof.
  intros.
  unfold serialize_name.
  Lia.lia.
Qed.

Definition name_eq (x y : name) : bool :=
  match x, y with
  | BOT, BOT => true

  | ES, ES => true
  | EEM, EEM => true
  | CET, CET => true
  | BIND, BIND => true
  | BINDER, BINDER => true
  | HS, HS => true
  | SHT, SHT => true
  | CHT, CHT => true
  | HSALT, HSALT => true
  | AS, AS => true
  | RM, RM => true
  | CAT, CAT => true
  | SAT, SAT => true
  | EAM, EAM => true
  | PSK, PSK => true

  | ZERO_SALT, ZERO_SALT => true
  | ESALT, ESALT => true
  | DH, DH => true
  | ZERO_IKM, ZERO_IKM => true
  | _, _ => false
  end.

Definition name_equality :
  Equality.axiom (T:=name) name_eq.
Proof.
  intros ? ?.
  destruct x, y.
  all: try now apply Bool.ReflectF.
  all: now apply Bool.ReflectT.
Qed.

HB.instance Definition _ : Equality.axioms_ name :=
  {|
    Equality.eqtype_hasDecEq_mixin :=
      {| hasDecEq.eq_op := name_eq;
        hasDecEq.eqP := name_equality |}
  |}.

Lemma serialize_name_notin_all :
  forall d,
  forall (ℓ1 ℓ2 : nat),
  forall (n1 n2 : name),
  forall (index1 index2 : nat),
    (index1 = index2) /\ ((ℓ1 <> ℓ2)%N \/ (n1 <> n2)%N)
    \/ ((index1 <> index2)%nat /\ (ℓ1 <= d)%N /\ (ℓ2 <= d)%N) ->
    serialize_name n1 ℓ1 d index1 <> serialize_name n2 ℓ2 d index2.
Proof.
  intros.
  destruct H as [[? [ | ]] | ] ; subst.
  + now apply serialize_name_notin.
  + now apply serialize_name_notin_different_name.
  + now apply serialize_name_notin_different_index.
Qed.

(** * Ltac *)

Ltac solve_imfset_disjoint :=
  try rewrite !imfsetU
  ; try rewrite !fdisjointUr
  ; try rewrite !fdisjointUl
  ; try rewrite  <- !fset1E
  ; try rewrite !imfset1
  ; try rewrite !fdisjoints1
  ; repeat (apply /andP ; split)
  ; try (rewrite (ssrbool.introF (fset1P _ _)) ; [ reflexivity | ])
  ; try (now apply serialize_name_notin_all ; Lia.lia
        || (now left ; split ; [ reflexivity
                              | ((timeout 5 now right) || (timeout 5 now left)) ])
        || (now right ; split ; [ discriminate | split ; Lia.lia ]))
  ; try (now apply serialize_name_notin_smaller_than_start ; try Lia.lia)
  ; try (now symmetry ; apply serialize_name_notin_smaller_than_start ; try Lia.lia).
