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

From KeyScheduleTheorem Require Import Types.
From KeyScheduleTheorem Require Import ExtraTypes.
From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem.Utility Require Import random_util.
From KeyScheduleTheorem.Utility Require Import interface_foreach_and_hierarchy.

Fixpoint map_with_in
  {A: eqType} {B}
  (l : list A)
  (f : forall (x : A), (x \in l) -> B)
  : list B :=
  match l as k return (k = l -> _) with
  | [] => fun _ => []
  | ( x :: xs ) =>
      fun H =>
        f x (eq_ind
               (x :: xs)
               (fun l => x \in l)
               (mem_head x xs)
               _ H)
          :: map_with_in xs
            (fun y H0 =>
               f y (eq_ind
                      (x :: xs)%SEQ
                      (λ l0 : seq A,
                          (∀ x0 : A, x0 \in l0 → B)
                          → (y \in l0) = true)
                      (λ f0 : ∀ x0 : A, x0 \in (x :: xs)%SEQ → B,
                         (eq_ind_r
                            (Logic.eq^~ true)
                            ([eta introTF (c:=true) orP] (or_intror H0))
                            (in_cons (T:=A) x xs y)))
                      l H f))
  end erefl.

Fixpoint map_with_in_rel
  {A : eqType} {B}
  (l : list A) (l' : list A)
  {H_in : forall a, a \in l' -> a \in l}
  (f : forall (x : A), (x \in l) -> B)
  {struct l'} : list B :=
  match l' as k return (forall a, a \in k -> a \in l)%nat -> _ with
  | [] => fun H => [::]
  | (x :: xs) =>
      fun H =>
        (f x (H x (mem_head x xs)))
          :: (map_with_in_rel l xs
               (H_in := fun a H0 =>
                          H a (eq_ind_r
                                 [eta is_true]
                                 ([eta introTF (c:=true) orP] (or_intror H0))
                                 (in_cons (T:=A) x xs a)))
               f)
  end H_in.

Fixpoint map_with_in_num
  (d : nat) (f : forall (x : nat), (x <= d)%nat -> raw_package)
  {struct d} : raw_package
  :=
  match d as k return (k <= d)%nat -> _ with
  | O => fun H => f O H
  | S n =>
      fun H =>
        par
          (map_with_in_num n
             (fun y Hf => f y (leq_trans Hf (leq_trans (leqnSn n) H))))
          (f (S n) H)
  end (leqnn d).

Fixpoint map_with_in_num_upper
  (d : nat) (i : nat) {H_le : (i <= d)%nat}
  (f : forall (x : nat), (x <= d)%nat -> raw_package)
  {struct i} : raw_package :=
  match i as k return (k <= d)%nat -> _ with
  | O => fun H => f O H
  | S n =>
      fun H => par
              (map_with_in_num_upper d n (H_le := (leq_trans (leqnSn n) H)) f)
              (f (S n) H)
  end H_le.

Lemma map_eta : forall {A B} (f : A -> B) a l,
    List.map f (a :: l) = f a :: List.map f l.
Proof. reflexivity. Qed.

Lemma map_with_in_eta :
  forall {A : eqType} {B} a l (f : forall (x : A), (x \in a :: l) -> B),
    map_with_in (a :: l) f
    = f a (mem_head (T:=A) a l)
        :: map_with_in l
        (λ (y : A) (H0 : y \in l), f y (mem_tail a l H0)).
Proof. reflexivity. Qed.

Lemma map_with_in_rel_eta :
  forall {A : eqType} {B}
    l a l' H_in
    (f : forall (x : A), (x \in l) -> B),
    map_with_in_rel l (a :: l') (H_in := H_in) f
    = f a (H_in a (mem_head a l'))
        :: map_with_in_rel l l' (H_in := fun x H => H_in x (mem_tail a l' H)) f.
Proof. reflexivity. Qed.

Theorem map_with_in_num_upper_trimmed :
  forall (* {L I} *)
    (d : nat)
    {f : nat -> Interface}
    (p : forall (ℓ : nat) , (ℓ <= d)%N → raw_package (* L I (f ℓ) *))
    (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le))
    (Hdisj : ∀ (n ℓ : nat) ,
        (n > ℓ)%nat ->
        (d >= n)%nat ->
        idents (f ℓ) :#: idents (f n)),
  forall k (K_le : (k <= d)%nat),
    trimmed (interface_hierarchy f k) (map_with_in_num_upper d k (H_le := K_le) p).
Proof.
  intros.
  induction k ; intros.
  - simpl.
    apply H_trim_p.
  - unfold interface_hierarchy ; fold interface_hierarchy.

    apply trimmed_par.
    {
      apply (idents_interface_hierachy).
      - Lia.lia.
      - intros.
        now apply Hdisj.
    }
    {
      apply IHk ; auto.
    }
    {
      apply H_trim_p.
    }
Qed.
