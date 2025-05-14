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

(** * Utility
    This file contains the building blocks for creating the packages
    used in the proofs for the Key Schedule.
    - [serialize_name]
        - assigning the "wires", this makes it easy to proof
          that there is no overlap of names/indexes for
          function definitions.
    - [key_store]
        - helper functions for looking up and storing key.
          These functions ensures  the same key is used by
          all functions, and samples a new key if one is not
          assigned.
    - [map_with_in]
        - defines mapping over lists or ranges propergating
          properties on the list to each element in the mapping
          function. E.g. any value in a range is less than
          the upper bound
    - [interface_foreach_and_hierarchy]
        - [interface_foreach] defines an interface indexed by
          elements of list, while [interface_hierarchy] defines
          an interface indexed by a range, given by an upper bound.
          These can be combined, and form commutative monoids.
    - [funext], [random_util] and [advantage]
        - contains simple helper functions, that makes proofs
          and definitions a bit easier.
    In this file we define
    - [ℓ_package]
        - a package defined by interface functions for import
          and export, index by a natural number in a range,
          together with a function defining the package at each
          index. This allows us to define packages depending on
          all previous levels.
    - [parallel_package]
        - Like [ℓ_package], but where we define the interfaces
          and packages indexed by a list of elements instead of a
          range.
    - [combined]
        - is the composition of [ℓ_package] and [parallel_package]
          to allow indexing on both a range and a list of elements.
          This allows us to define the TLS key schedule as a series
          of packages based on their names and a round index.
    The remainder of the file contains LTac and definitions to ensure
    the packages are valid, trimmed and can be ignored/skipped ([*_ID]).
 *)

From KeyScheduleTheorem Require Import Types.
From KeyScheduleTheorem Require Import ExtraTypes.
From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem.Utility Require Import random_util.
Export random_util.

From KeyScheduleTheorem.Utility Require Import key_store.
Export key_store.

From KeyScheduleTheorem.Utility Require Import serialize_name.
Export serialize_name.

From KeyScheduleTheorem.Utility Require Import interface_foreach_and_hierarchy.
Export interface_foreach_and_hierarchy.

From KeyScheduleTheorem.Utility Require Import map_with_in.
Export map_with_in.

From KeyScheduleTheorem.Utility Require Import funext.
Export funext.

From KeyScheduleTheorem.Utility Require Import advantage.
Export advantage.

(* (* TODO: should be key *) *)
(* Axiom len : chKey -> chNat. *)
(* TODO: chName should be key *)
Definition alg : chKey -> chHash :=
  (fun x => fto (fst (otf x))).
Axiom alg2 : chHandle -> chName. (* TODO: chName should be key *)
Definition tag : chHash -> chName -> chKey :=
  fun x y => fto (pair (otf x) (otf y)).

(** * Ltac *)

Ltac solve_trimmed :=
  match goal with
  | |- context [ trimmed (?IA :|: ?IB) (par (trim _ ?a) (trim _ ?b)) ] =>
      unfold trimmed
      ; rewrite trimmed_par
      ; [ reflexivity
        | refine parable
          ; solve_Parable
          ; unfold idents
          ; solve_imfset_disjoint
        | unfold trimmed ; now rewrite trim_idemp ..
      ]
  | |- context [ trimmed (?IA :|: ?IBC) (par ?a (par ?b ?c)) ] =>
      let H := fresh in
      assert (H : trimmed IBC (par b c)) by solve_trimmed
      ; rewrite <- H
      ; clear H
      ; solve_trimmed
  | |- context [ trimmed (?IAB :|: ?IB) (par (par ?a ?b) ?c) ] =>
      let H := fresh in
      assert (H : trimmed IAB (par a b)) by solve_trimmed
      ; rewrite <- H
      ; clear H
      ; solve_trimmed
  end.

Ltac trim_is_interface :=
  setoid_rewrite filterm_set ; fold chElement ;
  rewrite <- fset1E ;
  setoid_rewrite in_fset1 ;
  (* simpl ; *)
  rewrite eqxx ;
  rewrite filterm0 ;
  reflexivity.

Ltac trimmed_package p :=
  match type of p with
  | package ?L ?I ?E =>
      assert (trimmed E p) by now unfold trimmed ; trim_is_interface
  end.

(** * Package composition *)

Definition parallel_raw (p : list raw_package) : raw_package :=
  match p with
  | [] => emptym
  | (x :: xs) => List.fold_left par xs x
  end.

Theorem valid_parable_cons :
  forall (a : raw_package) (P : list raw_package) L I E1 E2,
    Parable a (parallel_raw P) ->
    valid_package L I E1 a ->
    valid_package L I E2 (parallel_raw P) ->
    valid_package L I (E1 :|: E2) (parallel_raw (a :: P)).
Proof.
  intros.
  simpl in *.
  unfold parallel_raw in H0.
  generalize dependent a.

  destruct P.
  {
    intros.
    assert (E2 = fset0).
    {
      apply eq_fset.
      destruct E2 , fsval.
      - easy.
      - intros ?.
        destruct H1.
        specialize (H1 s).
        rewrite mem_head in H1.
        specialize (H1 isT).
        destruct s as [? []].
        destruct H1.
        easy.
    }
    rewrite H2.
    rewrite fsetU0.
    apply H0.
  }

  simpl.
  generalize dependent r.
  induction P.
  {
    intros.
    rewrite <- (fsetUid L).
    rewrite <- (fsetUid I).
    apply valid_par ; easy.
  }
  simpl.
  intros.

  rewrite fold_left_to_par.
  rewrite <- par_assoc.
  rewrite <- par_assoc.
  rewrite (par_assoc r).
  rewrite <- fold_left_to_par.

  rewrite <- (fsetUid L).
  rewrite <- (fsetUid I).
  apply valid_par ; [ apply H |.. ].
  - apply H0.
  - apply H1.
Qed.

Lemma parallel_raw_cons : forall n E,
    parallel_raw (n :: E) = par n (parallel_raw E).
Proof.
  induction E.
  - simpl.
    unfold par ; rewrite unionm0.
    reflexivity.
  - simpl.
    rewrite fold_left_to_par.
    rewrite <- par_assoc.
    rewrite <- fold_left_to_par.
    reflexivity.
Qed.

(** * Trimmed *)

Fixpoint trimmed_pairs E P :=
  match E, P with
  | [], [] => True
  | [e], [p] => trimmed e p
  | (e :: E'), (p :: P') => trimmed e p /\ trimmed_pairs E' P'
  | _, _ => False
  end.

Lemma trimmed_parallel_raw : forall {A : eqType} {f I L},
    (∀ x y : A, x ≠ y → idents (f x) :#: idents (f y)) -> uniq I ->
    trimmed_pairs (List.map f I) L ->
    trimmed (interface_foreach (A := A) f I) (parallel_raw L).
Proof.
  intros.
  unfold parallel_raw.
  destruct L, I ; [ apply trimmed_empty_package | destruct I ; contradiction.. | ].

  generalize dependent s.
  generalize dependent r.
  generalize dependent I.
  (induction L ; destruct I) ; intros ; [ apply H1 | destruct I ; destruct H1 ; contradiction.. | ].

  rewrite interface_foreach_cons.
  simpl List.fold_left.
  rewrite fold_left_to_par.
  rewrite <- par_assoc.
  rewrite <- fold_left_to_par.
  apply trimmed_par.
  3: apply IHL ; [ now apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq (s :: I)) in H0 | apply H1 ].
  2: apply H1.
  1: now apply idents_interface_foreach_disjoint_same.
Qed.

Lemma trimmed_pairs_cons :
  forall a b c d,
    trimmed_pairs (a :: b) (c :: d)
    <-> (trimmed a c /\ trimmed_pairs b d).
Proof. now intros ? [] ? []. Qed.

Lemma trimmed_pairs_map :
  forall {A : Type} (f : A -> Interface) g l,
    (forall a, trimmed (f a) (g a)) ->
    trimmed_pairs
      (List.map f l)
      (List.map g l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold List.map ; fold (List.map f l); fold (List.map g l).
    simpl.
    destruct l.
    + apply H.
    + simpl.
      split ; [ apply H | apply IHl ].
Qed.

Lemma trimmed_pairs_map_with_in :
  forall {A : eqType} (l : list A) (f : forall (a : A), (a \in l) -> Interface) g,
    (forall a (H : a \in l), trimmed (f a H) (g a H)) ->
    trimmed_pairs
      (map_with_in l f)
      (map_with_in l g).
Proof.
  induction l ; intros.
  - reflexivity.
  - rewrite map_with_in_eta.
    rewrite map_with_in_eta.
    destruct l.
    + apply H.
    + now split ; [ apply H | apply IHl ].
Qed.

Lemma trimmed_pairs_map_with_in_rel :
  forall {A : eqType} (l l' : list A) H_in (f : forall (a : A), (a \in l) -> Interface) g,
    (forall a (H : a \in l), trimmed (f a H) (g a H)) ->
    trimmed_pairs
      (map_with_in_rel l l' (H_in := H_in) f)
      (map_with_in_rel l l' (H_in := H_in) g).
Proof.
  induction l' ; intros.
  - reflexivity.
  - rewrite map_with_in_rel_eta.
    rewrite map_with_in_rel_eta.
    destruct l'.
    + apply H.
    + now split ; [ apply H | apply IHl' ].
Qed.

Lemma trimmed_trim : forall I p, trimmed I (trim I p).
Proof.
  intros. unfold trimmed. now rewrite trim_idemp.
Qed.

(** * Valid pairs *)

Fixpoint valid_pairs L I E P :=
  match I, E, P with
  | [], [], [] => True
  | [i], [e], [p] => valid_package L i e p
  | (i :: I'), (e :: E'), (p :: P') => valid_package L i e p /\ valid_pairs L I' E' P'
  | _, _, _ => False
  end.

Lemma valid_pairs_cons :
  forall L a b c d e f,
    valid_pairs L (a :: b) (c :: d) (e :: f)
    <-> (valid_package L a c e /\ valid_pairs L b d f).
Proof. now intros ? ? [] ? [] ? []. Qed.

Lemma valid_pairs_map :
  forall {A : Type} L i (f : A -> Interface) g l,
    (forall a, valid_package L (i a) (f a) (g a)) ->
    valid_pairs L (List.map i l)
      (List.map f l)
      (List.map g l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - destruct l ; [ apply H | ].
    split ; [ apply H | apply IHl ].
Qed.

Lemma valid_pairs_map_with_in_rel :
  forall {A : eqType} L l l' H_in i (f : forall (a : A), (a \in l) -> Interface) g,
    (forall a (H : a \in l), valid_package L (i a H) (f a H) (g a H)) ->
    valid_pairs L
      (map_with_in_rel l l' (H_in := H_in) i)
      (map_with_in_rel l l' (H_in := H_in) f)
      (map_with_in_rel l l' (H_in := H_in) g).
Proof.
  intros.
  induction l'.
  - reflexivity.
  - destruct l' ; [ apply H | ].
    split ; [ apply H | apply IHl' ].
Qed.

Lemma valid_pairs_map_with_in_rel_map :
  forall {A : eqType} L l l' H_in i (f : forall (a : A), (a \in l) -> Interface) g,
    (forall a (H : a \in l), valid_package L (i a) (f a H) (g a H)) ->
    valid_pairs L
      (List.map i l')
      (map_with_in_rel l l' (H_in := H_in) f)
      (map_with_in_rel l l' (H_in := H_in) g).
Proof.
  intros.
  induction l'.
  - reflexivity.
  - destruct l' ; [ apply H | ].
    split ; [ apply H | apply IHl' ].
Qed.

(** * All idents disjoint *)

Fixpoint all_idents_disjoint {A} f I :=
  match I with
  | [] | [_] => True
  | (x :: xs) =>
      idents (f x) :#: idents (interface_foreach (A := A) f xs)
      /\ all_idents_disjoint f xs
  end.

Lemma all_idents_disjoint_foreach :
  (forall {A : eqType} f (L : list A),
      (forall x y, x <> y -> idents (f x) :#: idents (f y)) ->
      uniq L ->
      all_idents_disjoint f L).
Proof.
  intros.
  induction L ; [ easy | ].
  destruct L ; [ easy | ].
  split ; [ | apply IHL ].
  2: apply (ssrbool.elimT andP) in H0 as [] ; apply H1.
  apply idents_interface_foreach_disjoint_same.
  2: easy.
  apply H.
Qed.

Theorem valid_parable :
  forall {N : eqType} (P : list raw_package) f g L I E,
    (∀ x y, x ≠ y → idents (f x) :#: idents (f y)) -> uniq E ->
    trimmed_pairs (List.map f E) P ->
    valid_pairs L (List.map g I) (List.map f E) P ->
    valid_package L
      (interface_foreach (A := N) g I)
      (interface_foreach (A := N) f E)
      (parallel_raw P).
Proof.
  intros.
  simpl in *.
  generalize dependent I.
  generalize dependent E.
  induction P, E ; [  | try destruct E ; contradiction.. | ].
  {
    simpl.
    constructor.
    intros ? ?.
    rewrite in_fset in H3.
    inversion H3.
  }
  intros.
  rewrite interface_foreach_cons.
  rewrite <- (fsetUid L).
  destruct I ; [ contradiction | ].
  rewrite interface_foreach_cons.
  rewrite parallel_raw_cons.

  apply valid_par.
  3:{
    destruct I, E , P ; [ | destruct H2 ; try destruct I ; try destruct E ; contradiction .. | ].
    {
      simpl.
      constructor.
      intros ? ?.
      rewrite <- fset0E in H3.
      inversion H3.
    }
    apply IHP ;[ now apply (ssrbool.elimT andP) in H0 as [] | apply H1 | apply H2 ].
  }
  2:{
    simpl in H2.
    destruct (List.map g I), (List.map f E), P in H2 ; apply H2.
  }
  {
    clear -H H1 H0.
    generalize dependent E.
    generalize dependent s.
    generalize dependent a.
    induction P as [ | p ] ; intros a s E ? ?.
    {
      simpl.
      unfold Parable.
      rewrite domm0.
      apply fdisjoints0.
    }
    {
      generalize dependent a.
      generalize dependent s.
      destruct E as [ | e ] ; intros s ? a ?.
      {
        destruct H1 ; contradiction.
      }
      {
        specialize (IHP a s E).

        assert (uniq (s :: E)).
        {
          clear -H0.
          apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq (s :: E)) in H0.
          apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq E) in H1.
          simpl.
          rewrite notin_cons in H.
          apply (ssrbool.elimT andP) in H as [].
          apply /andP => //.
        }
        specialize (IHP H2).

        assert (trimmed_pairs (List.map f [:: s & E]) (a :: P)).
        {
          clear -H1.
          now simpl in * ; destruct (List.map f E), P.
        }
        specialize (IHP H3).

        rewrite parallel_raw_cons.
        unfold Parable.
        rewrite domm_union.
        rewrite fdisjointUr.
        apply /andP.
        split ; apply @parable.
        {
          destruct H1.
          rewrite <- H1.
          destruct E, P ; [ | destruct H4 ; try destruct E ; contradiction.. |  ] ; [ | destruct H4] ; rewrite <- H4 ; solve_Parable ; apply H ; apply (ssrbool.elimT andP) in H0 as [? _] ; rewrite notin_cons in H0 ; apply (ssrbool.elimT andP) in H0 as [] ; now apply /eqP.
        }
        {
          apply IHP.
        }
      }
    }
  }
Qed.

Definition parallel_package
  {A : eqType} (d : nat) {L} {f : A -> _} {g} Names
  (i : forall (a : A), package L (f a) (g a))
  (H : ∀ x y : A, x ≠ y → idents (g x) :#: idents (g y))
  (H1 : ∀ a : A, trimmed (g a) (i a))
  (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_foreach g Names) :=
  {package
     parallel_raw _ #with
    valid_parable _ _ _ _ _ _
    (H)
    H3
    (trimmed_pairs_map _ _ _ H1)
    (valid_pairs_map _ _ _ _ _ (fun m => pack_valid (i m))) }.

Theorem valid_parable_map_with_in_rel :
  forall {N : eqType} (P : list raw_package) L I E2 E1 H_in f g,
    (∀ (x y : N) Hx Hy, x ≠ y → idents (f x Hx) :#: idents (f y Hy)) ->
    uniq E1 ->
    trimmed_pairs (map_with_in_rel E2 E1 (H_in := H_in) f) P ->
    valid_pairs L (List.map g I) (map_with_in_rel E2 E1 (H_in := H_in) f) P ->
    valid_package L
      (interface_foreach (A := N) g I)
      (interface_foreach_in_rel E2 E1 (H_in := H_in) f)
      (parallel_raw P).
Proof.
  intros.
  simpl in *.
  generalize dependent I.
  generalize dependent E1.
  induction P, E1 ; [  | try (destruct E1 ; contradiction).. | ].
  {
    simpl.
    constructor.
    intros ? ?.
    rewrite in_fset in H3.
    inversion H3.
  }
  {
    simpl.
    constructor.
    intros ? ?.
    rewrite in_fset in H3.
    inversion H3.
  }
  {
    intros.
    rewrite interface_foreach_in_rel_cons.
    (* unfold interface_foreach_in_rel ; fold @interface_foreach_in_rel. *)
    (* rewrite map_with_in_rel_eta. *)
    (* rewrite interface_foreach_cons. *)
    rewrite <- (fsetUid L).
    destruct I ; [ contradiction | ].
    rewrite interface_foreach_cons.
    rewrite parallel_raw_cons.

    apply valid_par.
    3:{
      move: H0; rewrite cons_uniq => /andP [ _ H0 ] ; intros.
      apply (IHP _ _ H0).
      - rewrite map_with_in_rel_eta in H1.
        now rewrite trimmed_pairs_cons in H1.
      - rewrite map_with_in_rel_eta in H2.
        rewrite map_eta in H2.
        now rewrite valid_pairs_cons in H2.
    }
    2:{
      simpl in H2.
      destruct (List.map g I), (map_with_in_rel E2 E1 f), P in H2 ; apply H2.
    }
    {
      clear -H H1 H0.
      generalize dependent E1.
      generalize dependent s.
      generalize dependent a.
      induction P as [ | p ] ; intros a s E1 ? ? ?.
      {
        simpl.
        unfold Parable.
        rewrite domm0.
        apply fdisjoints0.
      }
      {
        generalize dependent a.
        generalize dependent s.
        destruct E1 as [ | e ] ; intros s ? ? a ?.
        {
          destruct H1 ; contradiction.
        }
        {
          specialize (IHP a s E1).

          specialize (IHP (fun a H => H_in a (in_remove_middle H))).

          specialize (IHP (uniq_middle H0)).

          assert (trimmed_pairs (map_with_in_rel E2 (s :: E1) (H_in := fun a H => H_in a (in_remove_middle H)) f) (a :: P)).
          {
            clear -H1.
            rewrite !map_with_in_rel_eta in H1 |- *.
            rewrite !trimmed_pairs_cons in H1 |- *.
            destruct H1 as [? []].
            replace (in_remove_middle _) with (mem_head s (e :: E1)) by easy.
            split.
            - assumption.
            - assert (forall {A : eqType} (x s e : A) E H,
                         in_remove_middle (x := x) (mem_tail s E H)
                         = (mem_tail s (e :: E) (mem_tail e E H))) by easy.

              set (map_with_in_rel _ _ _) in H1.
              set (map_with_in_rel _ _ _).
              now replace (l0) with l ; [ | subst l l0 ; f_equal ].
          }
          specialize (IHP H2).

          do 2 rewrite map_with_in_rel_eta in H1.
          do 2 rewrite trimmed_pairs_cons in H1.
          destruct H1 as [? []].

          rewrite parallel_raw_cons.
          unfold Parable.
          rewrite domm_union.
          rewrite fdisjointUr.
          apply /andP.
          split ; apply @parable.
          {
            rewrite <- H1.
            rewrite <- H3.
            solve_Parable.
            apply H ; apply (ssrbool.elimT andP) in H0 as [? _] ; rewrite notin_cons in H0 ; apply (ssrbool.elimT andP) in H0 as [] ; now apply /eqP.
          }
          {
            apply IHP.
          }
        }
      }
    }
  }
Qed.

Definition parallel_package_with_in_rel
  {A : eqType} (d : nat) {L} Names {f : A -> _} {g : forall (a : A), (a \in Names) -> _}
  (i : forall (a : A) (H : a \in Names), package L (f a) (g a H))
  (H : ∀ (x y : A) Hx Hy, x ≠ y → idents (g x Hx) :#: idents (g y Hy))
  (H1 : ∀ (a : A) (H : a \in Names), trimmed (g a H) (i a H))
  (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_foreach_in_rel Names Names (H_in := fun a H => H) g).
  refine ({package
             parallel_raw _ #with
             valid_parable_map_with_in_rel
             _ _ _ _ _ _
             _
             _
             _
             _
             (trimmed_pairs_map_with_in_rel _ _ _ _ _ _)
             (valid_pairs_map_with_in_rel_map _ _ _ _ _ _ _ _) }).
  - apply H.
  - apply H3.
  - apply H1.
  - intros.
    apply i.
Defined.

Theorem valid_forall : forall {A : eqType} {L} g f u Names (d ℓ : nat),
    (d >= ℓ)%nat ->
    (∀ x y : A, x ≠ y → idents (f x) :#: idents (f y)) -> uniq Names ->
    trimmed_pairs (List.map f Names) (List.map (u ℓ) Names) ->
    (valid_pairs L (List.map g Names) (List.map f Names)
       (List.map (u ℓ) Names)) ->
    ValidPackage L
      (interface_foreach g Names)
      (interface_foreach (A := A) f Names)
      (parallel_raw (List.map (u ℓ) Names)).
Proof.
  intros.
  eapply valid_package_inject_import.
  - instantiate (1 := interface_foreach g Names).

    unfold interface_hierarchy_foreach.
    unfold interface_hierarchy ; fold interface_hierarchy.

    induction d.
    + (* simpl. *)
      (* destruct ℓ ; [ | discriminate ]. *)
      apply fsubsetxx.
    + apply fsubsetxx.
  (* apply fsubsetU. fold interface_hierarchy. *)
  (* apply /orP. *)
  (* destruct (ℓ == d.+1) eqn:is_eq. *)
  (* * apply (ssrbool.elimT eqP) in is_eq. *)
  (*   subst. *)
  (*   right. *)
  (*   apply fsubsetxx. *)
  (* * apply (ssrbool.elimF eqP) in is_eq. *)
  (*   left. *)
  (*   apply IHd. *)
  (*   Lia.lia. *)
  - now apply valid_parable.
    (* + apply H0. *)
    (* + apply H1. *)
    (* + apply H2. *)
    (* + apply H3. *)
Qed.


Theorem valid_forall_map_with_in : forall {A : eqType} {L} g f Names u (d ℓ : nat),
    (d >= ℓ)%nat ->
    (∀ x y : A, x ≠ y → idents (f x) :#: idents (f y)) -> uniq Names ->
    trimmed_pairs (List.map f Names) (map_with_in Names (u ℓ)) ->
    (valid_pairs L (List.map (g^~ ℓ) Names) (List.map f Names)
       (map_with_in Names (u ℓ))) ->
    ValidPackage L
      (interface_hierarchy_foreach g Names d)
      (interface_foreach (A := A) f Names) (parallel_raw (map_with_in Names (u ℓ))).
Proof.
  intros.
  eapply valid_package_inject_import.
  - instantiate (1 := interface_foreach (g^~ ℓ) Names).

    unfold interface_hierarchy_foreach.
    unfold interface_hierarchy ; fold interface_hierarchy.

    induction d.
    + simpl.
      destruct ℓ ; [ | discriminate ].
      apply fsubsetxx.
    + apply fsubsetU. fold interface_hierarchy.
      apply /orP.
      destruct (ℓ == d.+1) eqn:is_eq.
      * apply (ssrbool.elimT eqP) in is_eq.
        subst.
        right.
        apply fsubsetxx.
      * apply (ssrbool.elimF eqP) in is_eq.
        left.
        apply IHd.
        Lia.lia.
  - now apply valid_parable.
    (* + apply H0. *)
    (* + apply H1. *)
    (* + apply H2. *)
    (* + apply H3. *)
Qed.

Theorem valid_forall_map_with_in_rel :
  forall {A : eqType} {L} Names l (d : nat) {g f} ℓ
         (H_le : (ℓ <= d)%nat) (u : forall a (H : a \in Names), raw_package) H_in,
    (∀ (x y : A), x ≠ y → idents (f x) :#: idents (f y)) ->
    uniq l ->
    (trimmed_pairs (List.map f l) (map_with_in_rel Names l (H_in := H_in) u)) ->
    (valid_pairs L
       (List.map g l)
       (List.map (f) l)
       (map_with_in_rel Names l (H_in := H_in) u)) ->
    ValidPackage L
      (interface_foreach g l)
      (interface_foreach f l)
      (parallel_raw (map_with_in_rel Names l (H_in := H_in) u)).
Proof.
  intros.
  eapply valid_package_inject_import.
  - instantiate (1 := interface_foreach g l).

    unfold interface_hierarchy_foreach.
    unfold interface_hierarchy ; fold interface_hierarchy.

    induction d.
    + simpl.
      (* destruct ℓ ; [ | discriminate ]. *)
      apply fsubsetxx.
    + (* apply fsubsetU. fold interface_hierarchy. *)
      (* apply /orP. *)
      (* right. *)
      apply fsubsetxx.
  - now apply valid_parable.
    (* + apply H. *)
    (* + apply H0. *)
    (* + apply H1. *)
    (* + apply H2. *)
    (*   epose (H1 ℓ H_le). *)
Qed.

Lemma forall_valid_from_packages :
  forall {A : eqType} {L} {g f} Names l (ℓ : nat)
         (u : forall a (H : a \in Names), package L (g a ℓ) (f a)) H_in,
    valid_pairs L
      (List.map (g^~ ℓ) l)
      (List.map f l)
      (map_with_in_rel Names l
         (H_in := H_in)
         (λ (a : A) (H3 : (a \in Names) = true), pack (u a H3))).
Proof.
  intros.
  induction l.
  - reflexivity.
  - rewrite !map_eta.
    rewrite map_with_in_rel_eta.
    rewrite valid_pairs_cons.
    split.
    + apply u.
    + apply IHl.
Qed.

Definition ℓ_raw_packages (d : nat)
  (p : forall (n : nat), (n <= d)%nat ->  raw_package)
  : raw_package :=
  map_with_in_num_upper d d (H_le := leqnn d) p.

Theorem ℓ_raw_package_trimmed :
  forall (* {L I} *)
    (d : nat)
    {f : nat -> Interface}
    (p : forall (ℓ : nat) , (ℓ <= d)%N → raw_package (* L I (f ℓ) *))
    (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le))
    (Hdisj : ∀ (n ℓ : nat) ,
        (n > ℓ)%nat ->
        (d >= n)%nat ->
        idents (f ℓ) :#: idents (f n)),
    trimmed (interface_hierarchy f d) (ℓ_raw_packages d p).
Proof.
  intros.
  unfold map_with_in_num_upper ; fold map_with_in_num_upper.
  now apply map_with_in_num_upper_trimmed.
Qed.

Definition ℓ_packages {L}
  (d : nat)
  {g : nat -> Interface}
  {f : nat -> Interface}
  (p : forall (n : nat), (d >= n)%nat → package L (g n) (f n))
  (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge))
  (Hdisj : ∀ (n ℓ : nat) ,
      (n > ℓ)%nat ->
      (d >= n)%nat ->
      idents (f ℓ) :#: idents (f n))
  : package L (interface_hierarchy g d) (interface_hierarchy f d).
Proof.
  refine {package ℓ_raw_packages d p}.
  unfold ℓ_raw_packages.
  set (leqnn d).
  set d in i at 2 |- * at 1 2 4.
  generalize dependent i.
  generalize dependent n.
  induction n ; intros.
  - simpl.
    apply p.
  - simpl.
    rewrite <- (fsetUid L).
    (* rewrite <- (fsetUid I). *)

    apply valid_par.
    + (* epose ℓ_raw_level_Parable. *)
      rewrite <- H_trim_p.
      rewrite <- map_with_in_num_upper_trimmed.
      2:{
        intros.
        apply H_trim_p.
      }
      2:{
        intros.
        apply Hdisj.
        - apply H.
        - Lia.lia.
      }
      solve_Parable.

      apply idents_interface_hierachy.
      2: intros ; now apply Hdisj.
      Lia.lia.
    + fold map_with_in_num_upper.
      apply IHn.
    + apply p.
Defined.

Definition trimmed_ℓ_packages {L}
  (d : nat)
  {g : nat -> Interface}
  {f : nat -> Interface}
  (p : forall (n : nat), (d >= n)%nat → package L (g n) (f n))
  (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge))
  (Hdisj : ∀ (n ℓ : nat) ,
      (n > ℓ)%nat ->
      (d >= n)%nat ->
      idents (f ℓ) :#: idents (f n))
  : trimmed (interface_hierarchy f d) (ℓ_packages d p H_trim_p Hdisj).
Proof.
  induction d ; intros.
  - apply H_trim_p.
  - simpl.
    apply trimmed_par.
    2:{
      apply map_with_in_num_upper_trimmed.
      - intros ; apply H_trim_p.
      - now intros ; apply Hdisj.
    }
    2:{
      apply H_trim_p.
    }
    apply idents_interface_hierachy ; eauto.
Qed.

Definition combined
  (A : eqType) (d : nat) L (f : A -> _) g Names
  (i : forall (n : nat), (n <= d)%nat -> forall (a : A), package L (f a) (g a n))
  (H : forall n, (n <= d)%nat -> ∀ x y : A, x ≠ y → idents (g x n) :#: idents (g y n))
  (H0 : forall n ℓ,
      (ℓ < n)%nat ->
      (n <= d)%nat ->
      ∀ x y : A,
        idents (g x ℓ) :#: idents (g y n))
  (H1 : forall n (H_le : (n <= d)%nat), ∀ a : A, trimmed (g a n) (i n H_le a))
  (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_hierarchy_foreach g Names d).
Proof.
  rewrite (interface_hierarchy_trivial (interface_foreach f (Names)) d).
  apply (ℓ_packages
           d
           (fun n H_le =>
              parallel_package d (Names) (i n H_le) (H n H_le) (H1 n H_le) H3
           )
           (fun n H_le =>
              trimmed_parallel_raw
                (H n H_le)
                H3
                (trimmed_pairs_map _ _ _ (H1 n H_le)))
           (fun n ℓ i0 i1 => idents_foreach_disjoint_foreach _ _ (Names) (H0 n ℓ i0 i1))
        ).
Defined.

Definition parallel_package_with_in_rel_hierarchy
  {A : eqType} {L} {g f} Names l  (d : nat)
  (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names),
      package L (g a ℓ) (f a ℓ))
  H_in :
  (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) ->
  uniq l ->
  (forall ℓ H_le,
      trimmed_pairs
        (List.map (f^~ℓ) l)
        (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) ->
  forall ℓ H_le,
    package L (interface_foreach (g^~ ℓ) l) (interface_foreach (f^~ ℓ) l) :=
  (fun H H0 H1 ℓ H_le =>
     {package (parallel_raw
                 (map_with_in_rel Names l
                    (H_in := H_in)
                    (fun a H => pack (u ℓ H_le a H))))
        #with
       valid_forall_map_with_in_rel
       (f := (f^~ℓ))
       Names l d _ H_le (u _ _) H_in
       (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq))
       H0 (H1 _ _)
       (forall_valid_from_packages Names l _ (u ℓ H_le) H_in)}).

Definition ℓ_parallel
  {A : eqType} {L} {g f} Names l  (d : nat)
  (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names), package L (g a ℓ) (f a ℓ))
  H_in :
  (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) ->
  uniq l ->
  (forall ℓ H_le,
      trimmed_pairs
        (List.map (f^~ℓ) l)
        (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) ->
  package L
    (interface_hierarchy_foreach g l d)
    (interface_hierarchy_foreach f l d) :=
  (fun H H0 H1 =>
     ℓ_packages d
       (λ ℓ H_le,
         parallel_package_with_in_rel_hierarchy Names l d u H_in H H0 H1 ℓ H_le)
       (fun a H_le =>
          trimmed_parallel_raw
            (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq))
            H0 (H1 _ _))
       (fun n ℓ H_le H_ge =>
          idents_foreach_disjoint_foreach _ _ _
            (fun _ _ =>
               H _ _ _ _
                 (or_intror
                    ((eq_ind_r
                        (λ ℓ0 : nat, (ℓ0 < n)%N → False)
                        (λ H_le0 : (n < n)%N,
                            (eq_ind_r
                               (λ b : bool, b → False)
                               (λ H_le1 : false,
                                   False_ind False
                                     (eq_ind
                                        false
                                        (λ e : bool, if e then False else True)
                                        I true H_le1))
                               (ltnn n))
                              H_le0)
                        (y:=ℓ))^~ H_le)
  )))).


(*** Ltac Tactics *)

Definition parallel_ID d (L : seq name) (f : name -> Interface) :
  (∀ x y, x ≠ y → idents (f x) :#: idents (f y)) ->
  (uniq L) ->
  (forall x, flat (f x)) ->
  package fset0 (interface_foreach f L) (interface_foreach f L) :=
  fun H H0 H1 =>
    parallel_package d L
      (fun x => {package ID (f x) #with valid_ID _ _ (H1 x)}) H
      (fun x => trimmed_ID _) H0.

Definition combined_ID (d : nat) (L : seq name) (f : name -> nat -> Interface) :
  (forall n x y, x ≠ y → idents (f x n) :#: idents (f y n)) ->
  (uniq L) ->
  (forall n x, flat (f x n)) ->
  (forall n ℓ,
      (ℓ < n)%nat ->
      (n <= d)%nat ->
      ∀ x y, idents (f x ℓ) :#: idents (f y n)) ->
  package
    fset0
    (interface_hierarchy_foreach f L d)
    (interface_hierarchy_foreach f L d).
Proof.
  intros.
  refine (ℓ_packages d (fun x _ => parallel_ID d L (f^~ x) _ _ _) _ _).
  - intros.
    unfold parallel_ID.
    apply trimmed_parallel_raw.
    + apply H.
    + apply H0.
    + apply trimmed_pairs_map.
      intros.
      unfold pack.
      apply trimmed_ID.
  - intros.
    apply idents_foreach_disjoint_foreach.
    intros.
    now apply H2.

    Unshelve.
    + intros.
      now apply H.
    + apply H0.
    + apply H1.
Defined.

Ltac solve_direct_in :=
  rewrite !fsubUset
  ; repeat (apply /andP ; split)
  ; repeat (apply fsubsetxx
            || (apply fsubsetU
               ; apply /orP ;
               ((right ; apply fsubsetxx) || left))).


Ltac solve_idents :=
  repeat match goal with
    | |- context [ idents ?a :#: idents (?b :|: ?c) ] =>
        unfold idents at 2
        ; rewrite (imfsetU _ b c)
        ; fold (idents b) ; fold (idents c)
        ; rewrite fdisjointUr
        ; apply /andP ; split
    | |- context [ idents (?a :|: ?b) :#: idents ?c ] =>
        unfold idents at 1
        ; rewrite (imfsetU _ a b)
        ; fold (idents a) ; fold (idents b)
        ; rewrite fdisjointUl
        ; apply /andP ; split
    | |- context [ idents (fset (?a :: ?b :: _)) ] => rewrite (fset_cons a)
    | |- context [ ?K :#: idents (interface_hierarchy ?f ?d) ] =>
        apply idents_interface_hierachy3 ; intros
    | |- context [ idents (interface_hierarchy ?f ?d) :#: ?K ] =>
        rewrite fdisjointC ; apply idents_interface_hierachy3 ; intros
    | |- context [ idents (interface_foreach ?f ?L)
                    :#:
                    idents (interface_foreach ?g ?K) ] =>
        apply idents_foreach_disjoint_foreach_in
        ; let H := fresh in
          intros ? H
          ; now repeat (move: H => /orP [ /eqP ? | H ]) ; subst
    | |- context [ idents ?K :#: idents (interface_foreach ?f ?L) ] =>
        let H := fresh in
        apply idents_disjoint_foreach_in
        ; intros ? H
    (* ; rewrite in_cons in H *)
    (* ; repeat (move: H => /orP [ /eqP ? | H ]) ; subst *)
    | |- context [ idents (interface_foreach ?f ?L) :#: ?K ] =>
        rewrite fdisjointC
    end ; unfold idents ; solve_imfset_disjoint.

Ltac solve_trimmed2 :=
  repeat match goal with
    | |- context [ trimmed _ (trim _ _) ] =>
        apply trimmed_trim
    | |- context [ trimmed ?E (parallel_raw _) ] =>
        eapply trimmed_parallel_raw
        ; [ | | apply trimmed_pairs_map ; intros  ]
        ; [ | reflexivity | ]
        ; [ | solve_trimmed2 ]
        ; [ intros ; unfold idents ; solve_imfset_disjoint ]
    | |- context [ trimmed _ (pack (ℓ_packages _ _ _ _)) ] =>
        apply trimmed_ℓ_packages
    | |- context [ trimmed ?E (par ?a ?b) ] =>
        eapply trimmed_par ; [ | solve_trimmed2..] ; solve_idents
    | |- context [ trimmed ?E (pack {| pack := _; |}) ] =>
        unfold pack
    | |- context [ trimmed ?E (mkfmap (cons ?a ?b)) ] =>
        apply trimmed_package_cons
    | |- context [ trimmed ?E (mkfmap nil) ] =>
        apply trimmed_empty_package
    | |- context [ trimmed ?E (ID _) ] =>
        apply trimmed_ID
    end.
