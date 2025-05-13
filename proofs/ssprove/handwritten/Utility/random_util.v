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

From KeyScheduleTheorem Require Import ssp_helper.

(******************************************************************************)
(* This file contains some useful functions, that does not fit anywhere else: *)
(* - `trim_fset0`                                                             *)
(* - `trimmed_par`                                                            *)
(* - `mem_tail`                                                               *)
(* - `fold_left_to_fsetU`                                                     *)
(* - `fold_left_to_par`                                                       *)
(* - `trimmed_eq_rect_r`                                                      *)
(* - `trimmed_eq_rect_r2`                                                     *)
(* - `trimmed_eq_rect`                                                        *)
(* - `trimmed_eq_rect2`                                                       *)
(* - `in_remove_middle`                                                       *)
(* - `unique_middle`                                                          *)
(* - `domm_trim_disjoint_is_ident`                                            *)
(******************************************************************************)

(** * Random util/SSProve functions *)

Lemma trim_fset0 : forall p, trim (fset [::]) p = p -> p = emptym.
Proof.
  intros.

  apply eq_fmap in H.
  unfold trim in H.
  epose filtermE.

  destruct p.
  destruct fmval.
  {
    now apply eq_fmap.
  }
  specialize (H (fst p)).
  rewrite filtermE in H.
  unfold getm in H.
  simpl in H.
  rewrite eqxx in H.
  simpl in H.
  destruct p as [? [? [? ?]]].
  simpl in H.
  rewrite <- fset0E in H.
  rewrite in_fset0 in H.
  discriminate.
Qed.

Theorem trimmed_par :
  forall {E1 E2}
    (p1 : raw_package) (p2 : raw_package)
    (H_disj : idents E1 :#: idents E2)
    (H_trim_p1 : trimmed E1 p1) (H_trim_p2 : trimmed E2 p2),
    trimmed (E1 :|: E2) (par p1 p2).
Proof.
  intros.

  unfold trimmed.

  unfold trim.

  replace (filterm (λ (n : Datatypes_nat__canonical__Ord_Ord) '(So; To; _), (n, (So, To)) \in E1 :|: E2) (par p1 p2)) with
    (filterm (λ (n : Datatypes_nat__canonical__Ord_Ord) '(So; To; _), ((n, (So, To)) \in E1) || ((n, (So, To)) \in E2)) (par p1 p2)).
  2:{
    f_equal.
    apply functional_extensionality.
    intros.
    apply functional_extensionality.
    intros.
    destruct x0 as [? [? ?]].
    rewrite in_fsetU.
    reflexivity.
  }

  assert (filterm
    (λ (n : Datatypes_nat__canonical__Ord_Ord) '(So; To; _),
      ((n, (So, To)) \in E1) || ((n, (So, To)) \in E2)) (par p1 p2) =
            unionm
              (filterm (λ (n : Datatypes_nat__canonical__Ord_Ord) '(So; To; _),
                        ((n, (So, To)) \in E1)) (p1))
              (filterm (λ (n : Datatypes_nat__canonical__Ord_Ord) '(So; To; _),
                        ((n, (So, To)) \in E2)) (p2))).
  {
    rewrite filterm_union.
    2:{
      apply @parable.
      rewrite <- H_trim_p1.
      rewrite <- H_trim_p2.
      solve_Parable.

      apply H_disj.
    }
    f_equal.
    {
      setoid_rewrite H_trim_p1.
      rewrite <- H_trim_p1.
      unfold trim.
      simpl.

      apply eq_fmap.
      intros ?.
      rewrite !filtermE.
      destruct p1.
      clear.
      induction fmval.
      {
        reflexivity.
      }
      {
        unfold getm.
        simpl.
        destruct (x == _).
        {
          simpl.
          destruct a as [? [? []]].
          simpl.
          destruct (_ \in _) eqn:in_E1.
          {
            simpl.
            rewrite in_E1.
            simpl.
            reflexivity.
          }
          {
            reflexivity.
          }
        }
        {
          rewrite IHfmval.
          {
            apply (LocationUtility.path_sorted_tl (T:=Datatypes_nat__canonical__Ord_Ord) i).
          }
          {
            intros.
            reflexivity.
          }
        }
      }
    }
    {
      setoid_rewrite H_trim_p2.
      rewrite <- H_trim_p2.
      unfold trim.
      simpl.

      apply eq_fmap.
      intros ?.
      rewrite !filtermE.
      destruct (p2).
      clear.
      induction fmval.
      {
        reflexivity.
      }
      {
        unfold getm.
        simpl.
        destruct (x == _).
        {
          simpl.
          destruct a as [? [? []]].
          simpl.
          destruct (_ \in _) eqn:in_E2.
          {
            simpl.
            rewrite in_E2.
            rewrite Bool.orb_true_r.
            simpl.
            reflexivity.
          }
          {
            reflexivity.
          }
        }
        {
          rewrite IHfmval.
          {
            apply (LocationUtility.path_sorted_tl (T:=Datatypes_nat__canonical__Ord_Ord) i).
          }
          {
            intros.
            reflexivity.
          }
        }
      }
    }
  }
  rewrite H.

  setoid_rewrite H_trim_p1.
  setoid_rewrite H_trim_p2.
  reflexivity.
Qed.

Definition mem_tail : forall {A : eqType} a (l : list A), forall {x}, x \in l -> x \in a :: l :=
  fun A a l x H =>
    (eq_ind_r
       [eta is_true]
       ([eta introTF (c:=true) orP] (or_intror H))
       (in_cons (T:=A) a l x)).

Lemma fold_left_to_fsetU :
  forall (T : ordType) B (f : B -> {fset T}) L (v : {fset T}),
    List.fold_left (fun y x => f x :|: y) L v
    =
      v :|: List.fold_left (fun y x => f x :|: y) L fset0.
Proof.
  clear ; intros.
  generalize dependent v.
  induction L ; intros.
  - simpl.
    rewrite fsetU0.
    reflexivity.
  - simpl.
    rewrite !(IHL (f _ :|: _)).
    rewrite fsetU0.
    rewrite fsetUA.
    rewrite (fsetUC v).
    reflexivity.
Qed.

Lemma fold_left_to_par :
  forall L (v : raw_package),
    List.fold_left par L v
    =
      par v (List.fold_left par L emptym).
Proof.
  clear ; intros.
  generalize dependent v.
  induction L ; intros.
  - simpl.
    unfold par ; rewrite unionm0.
    reflexivity.
  - simpl.
    rewrite (IHL (par v a)).
    unfold par at 6 ; rewrite union0m ; fold par.
    rewrite (IHL a).
    rewrite par_assoc.
    reflexivity.
Qed.

Lemma trimmed_eq_rect_r :
  forall L I1 I2 E (m : package L I1 E) (f : I2 = I1),
    trimmed E (eq_rect_r (fun I => package L I E) m f)
    = trimmed E m.
Proof. now destruct f. Qed.

Lemma trimmed_eq_rect_r2 :
  forall L I E1 E2 (m : package L I E1) (f : E2 = E1),
    trimmed E1 (eq_rect_r [eta package L I] m f)
    = trimmed E2 m.
Proof. now destruct f. Qed.

Lemma trimmed_eq_rect :
  forall L I E1 E2 (m : package L I E1) g H,
    trimmed E2 (eq_rect E1 (fun E => package L I E) m g H)
    = trimmed E2 m.
Proof. now destruct H. Qed.

Lemma trimmed_eq_rect2 :
  forall L I E1 E2 (m : package L I E1) g H,
    trimmed E2 (eq_rect E1 [eta package L I] m g H)
    = trimmed E2 m.
Proof. now destruct H. Qed.

Lemma in_remove_middle :
  forall {A : eqType} {x a b} {l : list A},
    x \in a :: l ->
    x \in a :: b :: l.
Proof.
  intros. rewrite !in_cons in H |- *.
  apply /orP.
  move : H => /orP [] ; [ left => // | right ; apply /orP ; right => // ].
Defined.

Lemma uniq_middle :
  forall {A : eqType} {a b : A} {L},
    uniq [:: a, b & L] ->
    uniq [:: a & L].
Proof.
  intros.
  rewrite !cons_uniq in H |- *.
  rewrite notin_cons in H.
  move : H => /andP [] /andP [] ? ? /andP [] ? ? ; apply /andP => //.
Defined.

Lemma domm_trim_disjoint_is_ident :
  forall E1 E2 p1 p2, idents E1 :#: idents E2 -> domm (trim E1 p1) :#: domm (trim E2 p2).
Proof.
  intros.
  eapply fdisjoint_trans.
  1: apply domm_trim.
  rewrite fdisjointC.
  eapply fdisjoint_trans.
  1: apply domm_trim.
  rewrite fdisjointC.
  apply H.
Qed.
