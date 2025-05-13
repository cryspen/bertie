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

From KeyScheduleTheorem.Utility Require Import serialize_name.

(** * Interface foreach / hierarchy definitions *)

Fixpoint interface_foreach {A : Type} (f : A -> Interface) (l : list A) :=
  match l with
  | [] => [interface]
  | [x] => f x
  | (x :: xs) => f x :|: interface_foreach f xs
  end.

Fixpoint interface_foreach_in_rel
  {A : eqType} (l : list A) (l' : list A)
  {H_in : forall a, a \in l' -> a \in l}
  (f : forall (a : A), (a \in l) -> Interface)
  {struct l'} : Interface :=
  (match l' as k return (forall a, a \in k -> a \in l) -> _ with
         | [] => fun _ => [interface]
         | (x :: xs) =>
             fun H_in =>
               match xs with
               | [] => f x (H_in x (mem_head x xs))
               | (y :: ys) =>
                   f x (H_in x (mem_head x xs))
                     :|: interface_foreach_in_rel l xs
                           (H_in := fun a H => H_in a (mem_tail x xs H))
                           f
               end
          end H_in).

Fixpoint interface_hierarchy (f : nat -> Interface) (ℓ : nat) : Interface :=
  match ℓ with
  | O => f O
  | S n => interface_hierarchy f n :|: f (S n)
  end.

Definition interface_hierarchy_foreach
  {A : Type} (f : A -> nat -> Interface) (l : list A) :=
  interface_hierarchy (fun ℓ => interface_foreach (fun n => f n ℓ) l).

Lemma lower_level_in_interface :
  forall (f : name -> nat -> Interface) (l : list name) d ℓ (p : nat -> _),
    p ℓ \in interface_foreach (f^~ ℓ) l ->
    (ℓ <= d)%nat ->
    (p ℓ) \in
      interface_hierarchy_foreach f l d.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  simpl.

  induction d.
  - destruct ℓ ; [ apply H | discriminate ].
  - simpl.
    rewrite in_fset.
    rewrite mem_cat.
    apply /orP.
    destruct (ℓ == d.+1) eqn:is_eq.
    {
      right.

      apply (ssrbool.elimT eqP) in is_eq.
      subst.
      simpl.

      simpl.

      apply H.
    }
    {
      apply (ssrbool.elimF eqP) in is_eq.
      simpl.
      rewrite IHd ; [ Lia.lia | Lia.lia ].
    }
Qed.

Lemma idents_interface_hierachy :
  ∀ f n ℓ,
    (n > ℓ)%nat ->
    (forall (ℓ : nat) , (n > ℓ)%nat -> idents (f ℓ) :#: idents (f n)) ->
    idents (interface_hierarchy f ℓ) :#: idents (f n).
Proof.
  clear ; intros.
  unfold idents.
  induction ℓ ; simpl.
  - eauto.
  - rewrite imfsetU.
    rewrite fdisjointUl.
    rewrite IHℓ.
    + simpl.
      now apply H0.
    + Lia.lia.
Qed.

Lemma interface_foreach_cons : forall {A} f n E,
    interface_foreach f (n :: E)
    = f n :|: interface_foreach (A := A) f E.
Proof.
  induction E.
  - simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma interface_foreach_cat : forall {A} f E1 E2,
    interface_foreach f (E1 ++ E2)
    = interface_foreach (A := A) f E1 :|: interface_foreach (A := A) f E2.
Proof.
  induction E1; intros.
  - simpl.
    rewrite <- fset0E.
    rewrite fset0U.
    reflexivity.
  - rewrite interface_foreach_cons.
    rewrite <- List.app_comm_cons.
    rewrite interface_foreach_cons.
    rewrite IHE1.
    rewrite fsetUA.
    reflexivity.
Qed.

Lemma interface_foreach_U : forall {A} f g E,
    interface_foreach f E :|: interface_foreach g E
    = interface_foreach (A := A) (fun n => f n :|: g n) E.
Proof.
  intros.
  induction E.
  - simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    reflexivity.
  - rewrite !interface_foreach_cons.
    rewrite fsetUA.
    rewrite (fsetUC _ (g a)).
    rewrite fsetUA.
    rewrite (fsetUC _ (f a)).
    rewrite <- fsetUA.
    rewrite IHE.
    reflexivity.
Qed.

Lemma interface_hierarchy_U :
  forall f g ℓ,
    (interface_hierarchy f ℓ :|: interface_hierarchy g ℓ)
    = interface_hierarchy (fun n => f n :|: g n) ℓ.
Proof.
  intros.
  induction ℓ.
  - reflexivity.
  - simpl.
    rewrite <- IHℓ.
    rewrite fsetUA.
    rewrite fsetUA.
    f_equal.
    rewrite fsetUC.
    rewrite fsetUA.
    f_equal.
    apply fsetUC.
Qed.

Lemma interface_hierarchy_foreachU :
  forall {A} f g L (d : nat),
    (interface_hierarchy_foreach f L d :|: interface_hierarchy_foreach g L d)
    = interface_hierarchy_foreach (A := A) (fun n d => f n d :|: g n d) L d.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  rewrite interface_hierarchy_U.
  f_equal.
  setoid_rewrite interface_foreach_U.
  reflexivity.
Qed.

Lemma interface_foreach_disjoint :
  forall {A} (f : A -> _) g (L : list A),
    (forall n m, f n :#: g m) ->
    forall a, f a :#: interface_foreach g L.
Proof.
  clear ; intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    apply fdisjoints0.
  - rewrite interface_foreach_cons.
    rewrite fdisjointUr.
    rewrite IHL.
    rewrite H.
    reflexivity.
Qed.

Lemma foreach_disjoint_foreach :
  (forall {A} f g (L : list A),
      (forall n m, f n :#: g m) ->
      interface_foreach f L :#: interface_foreach g L).
Proof.
  intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    apply fdisjoints0.
  - rewrite interface_foreach_cons.
    rewrite interface_foreach_cons.
    rewrite fdisjointUl.
    rewrite !fdisjointUr.
    rewrite H.
    rewrite IHL.
    rewrite Bool.andb_true_r.
    simpl.
    rewrite interface_foreach_disjoint.
    2: apply H.
    rewrite fdisjointC.
    rewrite interface_foreach_disjoint.
    2: intros ; rewrite fdisjointC ; apply H.
    reflexivity.
Qed.

Lemma foreach_imfset :
  (forall {A} g f (L : list A),
      g @: (interface_foreach f L)
      = interface_foreach (fun n => g @: f n) L).
Proof.
  intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    rewrite imfset0.
    reflexivity.
  - rewrite interface_foreach_cons.
    rewrite interface_foreach_cons.
    rewrite !imfsetU.
    rewrite IHL.
    reflexivity.
Qed.

Lemma idents_interface_foreach_disjoint :
  forall {A} (f : A -> _) g (L : list A),
    (forall n m, idents (f n) :#: idents (g m)) ->
    forall a, idents (f a) :#: idents (interface_foreach g L).
Proof.
  clear ; intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  - rewrite interface_foreach_cons.
    unfold idents.
    rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHL.
    rewrite H.
    reflexivity.
Qed.

Lemma idents_foreach_disjoint_foreach :
  (forall {A} f g (L : list A),
      (forall n m, idents (f n) :#: idents (g m)) ->
      idents (interface_foreach f L) :#: idents (interface_foreach g L)).
Proof.
  intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  - rewrite interface_foreach_cons.
    rewrite interface_foreach_cons.
    unfold idents.
    rewrite !imfsetU.
    rewrite fdisjointUl.
    rewrite !fdisjointUr.
    rewrite H.
    rewrite IHL.
    rewrite Bool.andb_true_r.
    simpl.
    rewrite idents_interface_foreach_disjoint.
    2: apply H.
    rewrite fdisjointC.
    rewrite idents_interface_foreach_disjoint.
    2: intros ; rewrite fdisjointC ; apply H.
    reflexivity.
Qed.

Lemma idents_interface_foreach_disjoint_same :
  forall {A : eqType} (f : A -> _) (L : list A),
    (forall n m, (n <> m) -> idents (f n) :#: idents (f m)) ->
    forall a, uniq (a :: L) ->
              idents (f a) :#: idents (interface_foreach f L).
Proof.
  clear ; intros.
  induction L.
  - simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  - rewrite interface_foreach_cons.
    unfold idents.
    rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHL.
    2:{
      apply (ssrbool.elimT andP) in H0 as [].
      apply (ssrbool.elimT andP) in H1 as [].
      apply (ssrbool.introT andP).
      fold (uniq L) in *.
      split.
      - rewrite notin_cons in H0.
        apply (ssrbool.elimT andP) in H0.
        apply H0.
      - apply H2.
    }
    rewrite H ; [ reflexivity | ].
    red ; intros.
    subst.
    apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq L) in *.
    rewrite notin_cons in H0.
    apply (ssrbool.elimT andP) in H0 as [].
    now apply (ssrbool.elimN eqP) in H0.
Qed.

Lemma interface_foreach_idents_cons : forall {A} f n E,
    idents (interface_foreach f (n :: E))
    = (idents (f n)) :|: idents (interface_foreach (A := A) f E).
Proof.
  intros.
  rewrite interface_foreach_cons.
  now setoid_rewrite imfsetU.
Qed.

Lemma interface_foreach_in_rel_cons : forall {A : eqType} l (a : A) l' H_in f,
    interface_foreach_in_rel l (a :: l') (H_in := H_in) f
    = f a (H_in a (mem_head _ _))
        :|: (interface_foreach_in_rel l l'
               (H_in := fun a H => H_in a (mem_tail _ _ H))
               f).
Proof.
  intros.
  induction l'.
  - simpl.
    rewrite <- fset0E ; rewrite fsetU0.
    reflexivity.
  - unfold interface_foreach_in_rel ; fold @interface_foreach_in_rel.
    reflexivity.
Qed.

Lemma idents_disjoint_foreach :
  (forall {A} f g (L : list A),
      (forall m, idents f :#: idents (g m)) ->
      idents f :#: idents (interface_foreach g L)).
Proof.
  intros.
  induction L.
  + simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  + rewrite interface_foreach_cons.
    unfold idents.
    rewrite !imfsetU.
    rewrite fdisjointUr.
    rewrite IHL ; clear IHL.
    rewrite Bool.andb_true_r.
    apply H.
Qed.

Lemma idents_foreach_disjoint_foreach_different :
  (forall {A} f g (Lf Lg : list A),
      (forall n m, idents (f n) :#: idents (g m)) ->
      idents (interface_foreach f Lf) :#: idents (interface_foreach g Lg)).
Proof.
  intros.
  apply idents_disjoint_foreach ; intros.
  rewrite fdisjointC.
  apply idents_disjoint_foreach ; intros.
  rewrite fdisjointC.
  apply H.
Qed.

Lemma interface_foreach_trivial : forall {A} i L (* d *),
    L <> [] ->
    i = (interface_foreach (λ (n : A), i) L ).
Proof.
  intros.
  destruct L ; [ easy | ].
  clear H.
  generalize dependent a.
  induction L ; intros.
  {
    rewrite interface_foreach_cons.
    simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    reflexivity.
  }
  {
    rewrite interface_foreach_cons.
    rewrite <- IHL.
    now rewrite fsetUid.
  }
Qed.

Lemma interface_hierarchy_empty : forall d,
    (interface_hierarchy (λ (n : nat), [interface]) d ) = [interface].
Proof.
  intros.
  rewrite <- fset0E.
  induction d.
  - reflexivity.
  - simpl. rewrite fsetU0. rewrite IHd. reflexivity.
Qed.

Lemma interface_hierarchy_trivial : forall i d,
    i = (interface_hierarchy (λ (_ : nat), i) d ).
Proof.
  intros.
  induction d.
  {
    reflexivity.
  }
  {
    simpl.
    rewrite <- IHd.
    now rewrite fsetUid.
  }
Defined.

Lemma interface_hierarchy_foreach_trivial : forall {A} i L d,
    L <> [] ->
    i = (interface_hierarchy_foreach (λ (_ : A) (_ : nat), i) L d ).
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  rewrite <- interface_hierarchy_trivial.
  now apply interface_foreach_trivial.
Defined.

Lemma idents_interface_hierachy3 :
  forall g f d,
    (forall x,
        (x <= d)%nat ->
        idents g :#: idents (f x)) ->
    idents g :#: idents (interface_hierarchy f d).
Proof.
  clear ; intros.
  unfold idents.
  induction d ; simpl.
  - apply H.
    reflexivity.
  - rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHd.
    + apply H.
      easy.
    + intros. apply H.
      Lia.lia.
Qed.

Lemma idents_disjoint_foreach_in :
  (forall {A: eqType} f g (L : list A),
      (forall m, (m \in L) -> idents f :#: idents (g m)) ->
      idents f :#: idents (interface_foreach g L)).
Proof.
  intros.
  induction L.
  + simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  + rewrite interface_foreach_cons.
    unfold idents.
    rewrite !imfsetU.
    rewrite fdisjointUr.
    rewrite IHL ; clear IHL.
    * rewrite Bool.andb_true_r.
      apply H.
      apply mem_head.
    * intros.
      apply H.
      rewrite in_cons.
      apply /orP.
      now right.
Qed.

Definition idents_foreach_disjoint_foreach_in :
  forall x y k index T1 T2 (Lf Lg : list name),
    (forall x, x \in Lf -> x \notin Lg) ->
    idents (interface_foreach
              (fun a => fset [(serialize_name a x k index, T1)])
              Lf)
      :#: idents (interface_foreach
                    (fun a => fset [(serialize_name a y k index, T2)])
                    Lg).
Proof.
  clear ; intros.
  rewrite fdisjointC.
  apply idents_disjoint_foreach_in.
  intros.
  rewrite fdisjointC.
  apply idents_disjoint_foreach_in.
  intros.
  unfold idents.
  solve_imfset_disjoint.
  apply serialize_name_notin_all.
  left ; split ; [ reflexivity | right ].
  red ; intros ; subst.
  specialize (H m H0).
  now rewrite H1 in H.
Qed.

Lemma interface_hierarchy_foreach_shift :
  forall d k {index p} L,
    interface_hierarchy_foreach
      (fun n ℓ => (fset [(serialize_name n ℓ k index, p)]))
      L d.+1
    = interface_foreach
        (fun n => fset [(serialize_name n O k index, p)])
        L
        :|: interface_hierarchy_foreach
        (fun n ℓ => fset [(serialize_name n (ℓ.+1) k index,p ) ])
        L d.
Proof.
  intros.
  induction d.
  - simpl. reflexivity.
  - unfold interface_hierarchy_foreach at 2.
    unfold interface_hierarchy ; fold interface_hierarchy.
    fold (interface_hierarchy_foreach (λ n ℓ, fset [(serialize_name n ℓ.+1 k index, p)]) L).
    rewrite fsetUA.
    rewrite fsetUC.
    rewrite <- IHd.
    rewrite fsetUC.
    reflexivity.
Qed.

Lemma subset_pair : forall {A : ordType} (x : {fset A}) y Lx Ly,
    x :<=: y ->
    Lx :<=: Ly ->
    x :|: Lx :<=: y :|: Ly.
Proof.
  intros.
  rewrite fsubUset ; apply /andP ; split.
  * rewrite fsubsetU ; [ easy | ].
    apply /orP ; left.
    apply H.
  * rewrite fsubsetU ; [ easy | ].
    apply /orP ; right.
    apply H0.
Qed.

Lemma interface_foreach_subset_pairs :
  forall {A: eqType} f g (L : seq A),
    (forall (x : A), (x \in L) -> f x :<=: g x) ->
    interface_foreach f L :<=: interface_foreach g L.
Proof.
  intros.
  induction L.
  + apply fsubsetxx.
  + rewrite !interface_foreach_cons.
    apply subset_pair.
    * apply H.
      apply mem_head.
    * apply IHL.
      intros.
      apply H.
      rewrite in_cons.
      now apply /orP ; right.
Qed.

Lemma interface_hierarchy_subset_pairs :
  forall f g d,
    (forall ℓ, (ℓ <= d)%nat -> f ℓ :<=: g ℓ) ->
    interface_hierarchy f d :<=: interface_hierarchy g d.
Proof.
  intros.
  induction d.
  + now apply H.
  + simpl.
    apply subset_pair.
    * apply IHd.
      eauto.
    * now apply H.
Qed.

Lemma interface_hierarchy_foreach_subset_pairs :
  forall {A: eqType} f g (L : seq A) d,
    (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: g x ℓ) ->
    interface_hierarchy_foreach f L d
      :<=:
    interface_hierarchy_foreach (A := A) g L d.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  apply interface_hierarchy_subset_pairs.
  intros.
  apply interface_foreach_subset_pairs ; eauto.
Qed.

Lemma interface_foreach_subset :
  forall {A: eqType} f (L : seq A) K,
    (forall (x : A), (x \in L) -> f x :<=: K) ->
    interface_foreach f L :<=: K.
Proof.
  intros.
  induction L.
  + simpl. rewrite <- fset0E. apply fsub0set.
  + rewrite interface_foreach_cons.
    rewrite fsubUset.
    apply /andP ; split.
    * apply H.
      apply mem_head.
    * apply IHL.
      intros.
      apply H.
      rewrite in_cons.
      now apply /orP ; right.
Qed.

Lemma interface_foreach_subsetR :
  forall {A: eqType} f (L : seq A) K,
    (exists (x : A) (H_in : x \in L), K :<=: f x) ->
    L <> [] ->
    K :<=: interface_foreach f L.
Proof.
  intros.
  induction L ; [ easy | ].
  unfold interface_hierarchy.
  rewrite interface_foreach_cons.
  rewrite fsubsetU ; [ easy | ].
  apply /orP.

  destruct H as [? []].
  rewrite in_cons in x0.
  move: x0 => /orP [/eqP ? | x0 ] ; subst.
  + now left.
  + right.
    apply IHL.
    2: destruct L ; easy.
    exists x, x0.
    apply H.
Qed.

Lemma interface_hierarchy_foreach_subset :
  forall {A: eqType} f (L : seq A) d K,
    (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: K) ->
    interface_hierarchy_foreach f L d :<=: K.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  induction d in H |- * at 1.
  - apply interface_foreach_subset ; eauto.
  - simpl.
    rewrite fsubUset.
    apply /andP ; split.
    + apply IHn ; eauto.
    + apply interface_foreach_subset ; eauto.
Qed.

Lemma interface_hierarchy_foreach_subsetR :
  forall {A: eqType} f (L : seq A) d K,
    (exists (x : A) (H_in : x \in L) ℓ (H_le : (ℓ <= d)%nat), K :<=: f x ℓ) ->
    L <> [] ->
    K :<=: interface_hierarchy_foreach f L d.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  induction d in H |- * at 1.
  - destruct H as [? [? [? []]]].
    apply interface_foreach_subsetR.
    2: easy.
    exists x, x0.
    destruct x1 ; [ | easy ].
    apply H.
  - simpl.
    rewrite fsubsetU ; [ easy | ].
    apply /orP.

    destruct H as [? [? [? []]]].
    destruct (x1 == n.+1) eqn:x_eq ; move: x_eq => /eqP x_eq ; subst.
    + right.
      clear IHn.
      apply interface_foreach_subsetR.
      2: easy.
      exists x, x0.
      apply H.
    + left.
      apply IHn.
      exists x, x0, x1.
      eexists ; [ Lia.lia | ].
      apply H.
Qed.

Lemma idents_interface_hierachy2 :
  forall g f d,
    (forall x, idents g :#: idents (f x)) ->
    idents g :#: idents (interface_hierarchy f d).
Proof.
  clear ; intros.
  unfold idents.
  induction d ; simpl.
  - apply H.
  - rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHd.
    apply H.
Qed.

Lemma interface_foreach_swap :
  forall {A} (a b : A) l f,
    interface_foreach f (a :: b :: l)
    = interface_foreach f (b :: a :: l).
Proof.
  intros.
  induction l.
  - simpl.
    now rewrite fsetUC.
  - simpl.
    rewrite fsetUA.
    rewrite (fsetUC (f a)).
    rewrite <- fsetUA.
    reflexivity.
Qed.

Lemma interface_hierarchy_foreach_cons :
  forall {A} f a L (d : nat),
    interface_hierarchy_foreach f (a :: L) d
    = interface_hierarchy (f a) d
        :|: interface_hierarchy_foreach (A := A) f L d.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  rewrite interface_hierarchy_U.
  f_equal.
  setoid_rewrite interface_foreach_cons.
  reflexivity.
Qed.

Lemma interface_hierarchy_foreach_cat : forall {A} f L1 L2 d,
    interface_hierarchy_foreach f (L1 ++ L2) d
    = interface_hierarchy_foreach (A := A) f L1 d
        :|: interface_hierarchy_foreach (A := A) f L2 d.
Proof.
  induction L1 ; intros.
  - unfold interface_hierarchy_foreach.
    simpl.
    rewrite <- interface_hierarchy_trivial.
    simpl.
    rewrite <- fset0E.
    rewrite fset0U.
    reflexivity.
  - rewrite interface_hierarchy_foreach_cons.
    rewrite <- fsetUA.
    rewrite <- IHL1.
    now rewrite <- interface_hierarchy_foreach_cons.
Qed.

Lemma interface_foreach_condition :
  (forall {A : eqType} f (L1 L2 : list A),
      (forall x, x \in L1 -> x \in L2) ->
      interface_foreach f L1 =
        interface_foreach
          (fun x => if x \in L2 then f x else fset [::])
          L1).
Proof.
  clear ; intros.
  induction L1.
  - reflexivity.
  - rewrite interface_foreach_cons.
    rewrite IHL1.
    2:{
      intros.
      apply H.
      apply mem_tail.
      apply H0.
    }
    rewrite interface_foreach_cons.
    rewrite H.
    2: apply mem_head.
    reflexivity.
Qed.

Lemma interface_foreach_func_if_cons :
  forall {A : eqType} a (L1 L2 : seq A) f,
    interface_foreach (λ x : A, if x \in (a :: L2)%SEQ then f x else fset [::]) L1
    =
      (if a \in L1 then f a else fset [::])
        :|: interface_foreach (λ x : A,
              if x \in L2%SEQ then f x else fset [::])
              L1.
Proof.
  induction L1 ; intros.
  + now rewrite fsetUid.
  + rewrite interface_foreach_cons.
    rewrite interface_foreach_cons.

    rewrite IHL1.
    rewrite fsetUA.
    rewrite fsetUA.
    f_equal.
    rewrite <- fset0E.

    rewrite !in_cons.
    rewrite (eq_sym a).
    destruct (a0 == a) eqn:a0a.
    * move: a0a => /eqP ? ; subst.
      simpl.
      destruct (a \in L1), (a \in L2) ; now try rewrite fsetUid ; try rewrite fsetU0.
    * simpl.
      rewrite fsetUC.
      reflexivity.
Qed.

Lemma interface_foreach_sub_list : forall {A : eqType} f L1 L2,
    uniq L1 ->
    (forall x, x \in L1 -> x \in L2) ->
    interface_foreach f L1 =
      interface_foreach (A := A) (fun x =>
        if x \in L1 then f x else [interface])
        L2.
Proof.
  intros.

  rewrite (interface_foreach_condition f L1 L1 (fun _ H => H)).
  induction L1 ; intros.
  - simpl.
    destruct L2 ; [ easy | ].
    now rewrite <- interface_foreach_trivial.
  - rewrite interface_foreach_func_if_cons.
    rewrite interface_foreach_func_if_cons.
    rewrite mem_head.
    rewrite H0.
    2: apply mem_head.
    rewrite interface_foreach_cons.
    (* destruct (a \in _) ; [  ] *)
    rewrite IHL1.
    2:{
      rewrite cons_uniq in H.
      now move: H => /andP [? ?] ; subst.
    }
    2:{
      intros.
      apply H0.
      now apply mem_tail.
    }
    destruct (_ \in _).
    {
      rewrite fsetUA.
      rewrite fsetUid.
      reflexivity.
    }
    {
      rewrite <- fset0E.
      rewrite fset0U.
      reflexivity.
    }
Qed.


Lemma interface_foreach_trivial2 : forall {A} i L (* d *),
    (L <> [] \/ i = [interface]) ->
    i = (interface_foreach (λ (n : A), i) L ).
Proof.
  intros.
  destruct H.
  - destruct L ; [ easy | ].
    clear H.
    generalize dependent a.
    induction L ; intros.
    {
      rewrite interface_foreach_cons.
      simpl.
      rewrite <- fset0E.
      rewrite fsetU0.
      reflexivity.
    }
    {
      rewrite interface_foreach_cons.
      rewrite <- IHL.
      now rewrite fsetUid.
    }
  - rewrite H.
    induction L.
    + reflexivity.
    + rewrite interface_foreach_cons.
      rewrite <- IHL.
      now rewrite fsetUid.
Qed.

Lemma interface_hierarchy_subset : forall f d K,
    (forall (x : nat) (H : (x <= d)%nat), f x :<=: K) ->
    interface_hierarchy f d :<=: K.
Proof.
  intros.
  induction d.
  - now apply H.
  - simpl.
    rewrite fsubUset.
    rewrite H ; [ rewrite IHd | ] ; eauto.
Qed.

Lemma interface_hierarchy_subsetR : forall f d K,
    (exists (x : nat) (H : (x <= d)%nat), K :<=: f x) ->
    K :<=: interface_hierarchy f d.
Proof.
  intros.
  induction d.
  - simpl. destruct H as [? []]. destruct x ; [ | easy ]. apply H.
  - simpl.
    destruct H as [? []].
    destruct (x == d.+1) eqn:x_is_d ; move: x_is_d => /eqP ? ; subst.
    + apply fsubsetU.
      rewrite H ; apply /orP ; eauto.
    + apply fsubsetU.
      rewrite IHd ; [ easy | ].
      exists x.
      eexists.
      * Lia.lia.
      * apply H.
Qed.
