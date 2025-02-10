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

Lemma parable_par_l :
  forall a b c, Parable a c -> Parable b c -> Parable (par a b) c.
Proof.
  clear ; intros.
  unfold Parable.
  rewrite domm_union.
  rewrite fdisjointUl.
  rewrite H H0.
  reflexivity.
Qed.

Lemma parable_par_r :
  forall a b c, Parable c a -> Parable c b -> Parable c (par a b).
Proof.
  clear ; intros.
  unfold Parable.
  rewrite domm_union.
  rewrite fdisjointUr.
  rewrite H H0.
  reflexivity.
Qed.

Ltac solve_Parable :=
  match goal with
  | [ |- context [ Parable (trim _ ?a) (trim _ ?b) ] ] =>
      apply parable_trim
      ; try (unfold idents
             ; rewrite <- !fset1E
             ; rewrite !imfset1
             ; now rewrite fdisjoint1s)
  | Ha : trimmed ?Ea ?a ,
      Hb : trimmed ?Eb ?b
    |- context [ Parable ?a ?b ] =>
      rewrite <- Ha ; rewrite <- Hb ; solve_Parable
  | Ha : trimmed ?Ea ?a ,
      Hb : trimmed ?Eb ?b
    |- context [ Parable ?a (?b ∘ ?c) ] =>
      rewrite <- Ha ;
      rewrite <- Hb ;
      erewrite !link_trim_commut ;
      solve_Parable
  | Ha : trimmed ?Ea ?a ,
      Hb : trimmed ?Eb ?b
    |- context [ Parable (?b ∘ ?c) ?a ] =>
      rewrite <- Ha ;
      rewrite <- Hb ;
      erewrite !link_trim_commut ;
      solve_Parable
  | |- context [ Parable ?a (par ?b ?c) ] =>
      apply parable_par_r ; solve_Parable
  | |- context [ Parable (par ?a ?b) ?c ] =>
      apply parable_par_l ; solve_Parable
  end.

From extructures Require Import ord fset fmap.

Ltac trim_is_interface :=
  setoid_rewrite filterm_set ; simpl ; fold chElement ;
  rewrite <- fset1E ;
  rewrite in_fset1 ;
  (* simpl ; *)
  rewrite eqxx ;
  rewrite filterm0 ;
  reflexivity.

From Crypt Require Import pkg_composition.

Ltac trimmed_package p :=
  match type of p with
  | package ?L ?I ?E =>
      assert (trimmed E p) by now unfold trimmed ; trim_is_interface
  end.


Fixpoint sum_accum (fuel : nat) (index : nat) (f : nat -> nat) (accum : nat) : nat :=
  match fuel with
  | O => accum
  | S n' => sum_accum n' (index + 1%nat) f (accum + f index)
  end.

Definition sumR : nat -> nat -> (nat -> R) -> R :=
  (fun l u f => (List.fold_left (fun y x => y + f x) (iota l u) 0)%R).

Fixpoint sumR_H_prime (start : nat) (fuel : nat) (f : forall (ℓ : nat), (ℓ <= start + fuel)%nat -> R) {struct fuel} : R.
  refine (
  match fuel as k return (k <= fuel)%nat -> _ with
  | O => fun _ => 0
  | S n => fun _ => f start _ + sumR_H_prime (S start) n _
  end _).
  - Lia.lia.
  - intros.
    eapply (f ℓ).
    Lia.lia.
  - Lia.lia.
Defined.  

Definition sumR_H (l u : nat) (H_ul : (u >= l)%nat) (f : forall (ℓ : nat), (ℓ <= u)%nat -> R) : R.
Proof.
  refine (sumR_H_prime l (u - l) _).
  intros.
  refine (f ℓ _).
  Lia.lia.
Defined.

Axiom sumR_to_H : forall l u H_ul f, sumR l u f = sumR_H l u H_ul (fun n _ => f n).

Axiom sumR_le : forall l u H_ul f g, (forall v Hf Hg, (f v Hf <= g v Hg))%R -> (sumR_H l u H_ul f  <= sumR_H l u H_ul g)%R.

Axiom sumR_l : forall {T : Type}, list T -> (T -> R) -> R.
(* Definition sum (l u : nat) (f : nat -> nat) : nat := sum_accum (u - l) l f 0%R. *)

Definition max_val : R -> R -> R :=
  fun x y =>
    if (x > y)%R
    then x
    else y.

Definition maxR (f : bool -> R) : R :=
  max_val (f false) (f true).

Axiom max_leq : forall f g, (forall b, f b <= g b)%R -> (maxR f <= maxR g)%R.
