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

From KeyScheduleTheorem Require Import BasePackages.

From KeyScheduleTheorem Require Import ssp_helper.

(** Extra imports *)
From SMTCoq Require Import SMTCoq.

(*** Helper definitions *)

Fixpoint interface_hierarchy (f : nat -> Interface) (ℓ : nat) : Interface :=
  match ℓ with
  | O => [interface]
  | S n => f n :|: interface_hierarchy f n
  end.

Fixpoint ℓ_raw_packages
  (p : forall (n : nat), raw_package)
  (d : nat)
  {struct d}:
  raw_package :=
  match d with
  | O => emptym
  | S d' =>
      par (p d') (@ℓ_raw_packages p d')
  end.

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
    (Hdisj : domm (p1) :#: domm (p2))
    (H_trim_p1 : trimmed E1 p1) (H_trim_p2 : trimmed E2 p2),
    trimmed (E1 :|: E2) (par p1 p2).
Proof.
  intros.
  (* rewrite <- H_trim_p1. *)
  (* rewrite <- H_trim_p2. *)

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
    2: apply Hdisj.
    (* 2:{ *)
    (*   epose (domm_trimmed E1 p1 H_trim_p1). *)
    (*   epose (domm_trimmed E2 p2 H_trim_p2). *)

    (*   epose proof (fdisjoint_trans i Hdisj). *)
    (*   rewrite fdisjointC in H. *)
    (*   epose proof (fdisjoint_trans i0 H). *)
    (*   rewrite fdisjointC in H0. *)
    (*   apply H0. *)
    (* } *)
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

Theorem ℓ_raw_package_trimmed :
  forall {L I}
    {f : nat -> Interface}
    (p : forall (n : nat), package L I (f n))
    (H_trim_p : forall d, trimmed (f d) (p d))
    (Hdisj : forall d, domm (pack (p d)) :#: domm (ℓ_raw_packages (λ n : nat, p n) d))
    (d : nat),
    trimmed (interface_hierarchy f d) (ℓ_raw_packages (λ n : nat, p n) d).
Proof.
  intros.
  induction d.
  - unfold trimmed ; now setoid_rewrite filterm0.
  - simpl.
    apply (trimmed_par (p d) (ℓ_raw_packages (λ n : nat, p n) d)).
    {
      apply Hdisj.
    }
    {
      apply H_trim_p.
    }
    {
      apply IHd.
    }
Qed.

Lemma ℓ_raw_level_Parable (ℓ : nat) (f : nat -> _) :
  (forall (n ℓ : nat), n >= ℓ.+1 -> Parable (f n) (f ℓ)) ->
  Parable (f ℓ) (ℓ_raw_packages (λ n : nat, f n) ℓ).
Proof.
  set ℓ at 1.
  assert (n >= ℓ) by Lia.lia.
  generalize dependent n.
  unfold Parable.
  induction ℓ; intros.
  {
    unfold domm.
    rewrite <- fset0E.
    now rewrite fdisjoints0.
  }
  {
    unfold ℓ_raw_packages ; fold ℓ_raw_packages.
    rewrite (domm_union).
    rewrite fdisjointUr.
    rewrite IHℓ ; [ | Lia.lia | apply H0 ].
    rewrite Bool.andb_true_r.
    apply (H0 n ℓ H).
  }
Qed.

Program Definition ℓ_packages {L I}
  {f : nat -> Interface}
  (p : forall (n : nat), package L I (f n))
  (H : ∀ n ℓ : nat, n >= ℓ.+1 → Parable (p n) (p ℓ))
  (H_trim_p : forall d, trimmed (f d) (p d))
  (Hdisj : forall (n d : nat), n > d -> (@fdisjoint Datatypes_nat__canonical__Ord_Ord
          (@imfset
             (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
                (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                   choice_type_choice_type__canonical__Ord_Ord)) Datatypes_nat__canonical__Ord_Ord
             (fun pat : prod nat (prod choice_type choice_type) =>
              match pat return nat with
              | pair n0 _ => n0
              end) (f n))
          (@imfset
             (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
                (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                   choice_type_choice_type__canonical__Ord_Ord)) Datatypes_nat__canonical__Ord_Ord
             (fun pat : prod nat (prod choice_type choice_type) =>
              match pat return nat with
              | pair n0 _ => n0
              end) (f d))))
  (d : nat)
  : package L I (interface_hierarchy f d) :=
  {package ℓ_raw_packages p d}.
Next Obligation.
  simpl in Hdisj.
  induction d.
  - apply valid_empty_package.
  - simpl.
    rewrite <- (fsetUid L).
    rewrite <- (fsetUid I).
    apply valid_par.
    + clear IHd.

      rewrite <- H_trim_p.
      rewrite <- (ℓ_raw_package_trimmed) ; [ | apply H_trim_p | refine (fun d0 => ℓ_raw_level_Parable d0 p _) ; apply H ].
      solve_Parable.
      unfold idents.

      (* set d at 1. *)
      (* generalize dependent n. *)

      destruct d ; intros.
      {
        rewrite imfset_fset.
        rewrite <- fset0E.
        now rewrite fdisjoints0.
      }
      {
        simpl.
        rewrite imfsetU.
        rewrite fdisjointUr.

        rewrite (Hdisj d.+1 d (ltac:(easy))) ; simpl.

        set (d.+1) at 1.
        assert (n > d) by easy.
        generalize dependent n.

        induction d ; intros.
        {
          rewrite imfset_fset.
          rewrite <- fset0E.
          now rewrite fdisjoints0.
        }
        {
          simpl.
          rewrite imfsetU.
          rewrite fdisjointUr.
          rewrite IHd.
          {
            rewrite Bool.andb_true_r.
            simpl.
            apply Hdisj.
            easy.
          }
          {
            easy.
          }
        }
      }
    + apply (p d).
    + apply IHd.
Defined.

Definition interface_foreach (f : name -> Interface) (l : list name) :=
  match l with
  | [] => [interface]
  | (x :: xs) => List.fold_left (fun y n => y :|: f n) xs (f x)
  end.

Definition interface_hierarchy_foreach (f : name -> nat -> Interface) (l : list name) :=
  interface_hierarchy (fun ℓ => interface_foreach (fun n => f n ℓ) l).

(* Theorem trim_interface_hierarchy *)
(*   {L I} *)
(*   {f : nat -> Interface} *)
(*   (p : forall (n : nat), package L I (f n)) *)
(*   (H : forall d, Parable (p d) (ℓ_raw_packages p d)) *)
(*   (d : nat) *)
(*   : trimmed (interface_hierarchy f d) (ℓ_packages f p H d). *)

(* Taken from OVN implementation *)
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

Ltac solve_imfset_disjoint :=
  try (rewrite !imfsetU
       ; try rewrite !fdisjointUr
       ; rewrite !fdisjointUl)
  ; try (rewrite  <- !fset1E
         ; rewrite !imfset1
         ; rewrite !fdisjoints1
         ; unfold "\notin" ; rewrite !ifF ; [ reflexivity | unfold "\in"; simpl; unfold "\in"; simpl ; Lia.lia.. ]
         (* ; setoid_rewrite Bool.orb_false_r *)
         (* ; simpl *)
      (* ; Lia.lia *)
      ).

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
      assert (H : trimmed IBC (par b c)) by solve_trimmed ; rewrite <- H ; clear H ; solve_trimmed
  | |- context [ trimmed (?IAB :|: ?IB) (par (par ?a ?b) ?c) ] =>
      let H := fresh in
      assert (H : trimmed IAB (par a b)) by solve_trimmed ; rewrite <- H ; clear H ; solve_trimmed
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

Definition parallel_raw (p : list raw_package) : raw_package :=
  match p with
  | [] => emptym
  | (x :: xs) => List.fold_left par xs x
  end.

(*** XTR / XPD *)

Context (PrntN: name -> code fset0 fset0 (chName × chName)).
Context (Labels : name -> bool -> code fset0 fset0 chLabel).

(* p. 5,6 *)
Context (xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle).
Context (xtr : chKey -> chKey -> code fset0 fset0 chKey).

(* Xtr *)

Notation " 'chXTRinp' " :=
  (chHandle × chHandle)
    (in custom pack_type at level 2).
Notation " 'chXTRout' " :=
  (chHandle)
    (in custom pack_type at level 2).

Definition serialize_name  (n : name) (ℓ (* 0 .. d *) : nat) : nat :=
  let size := 19%nat in
  match n with
  | BOT => 0 + size * ℓ

  | ES => 1 + size * ℓ
  | EEM => 2 + size * ℓ
  | CET => 3 + size * ℓ
  | BIND => 4 + size * ℓ
  | BINDER => 5 + size * ℓ
  | HS => 6 + size * ℓ
  | SHT => 7 + size * ℓ
  | CHT => 8 + size * ℓ
  | HSALT => 9 + size * ℓ
  | AS => 10 + size * ℓ
  | RM => 11 + size * ℓ
  | CAT => 12 + size * ℓ
  | SAT => 13 + size * ℓ
  | EAM => 14 + size * ℓ
  | PSK => 15 + size * ℓ

  | ZERO_SALT => 16 + size * ℓ
  | ESALT => 17 + size * ℓ
  | DH => 18 + size * ℓ
  (* | ZERO_IKM => 0 + size * ℓ *)
  end%nat.

Definition XTR (n : name) (ℓ (* 0 .. d *) : nat) : nat := serialize_name n ℓ.

Definition Xtr
  (n : name) (ℓ : nat) (b : bool)
  {GET : nat} {SET : nat}
  :
  package
    fset0
    [interface
      #val #[ GET ] : chGETinp → chGETout ;
      #val #[ SET ] : chSETinp → chSETout
    ]
    [interface
       #val #[ XTR n ℓ ] : chXTRinp → chXTRout
    ].
  refine [package
     #def #[ XTR n ℓ ] ('(h1,h2) : chXTRinp) : chXTRout {
        #import {sig #[ SET ] : chSETinp → chSETout }
        as set_fn ;;
        #import {sig #[ GET ] : chGETinp → chGETout }
        as get_fn ;;
        '(n1,n2) ← PrntN n ;;
        (if Datatypes.andb (xpn_eq (nfto (alg2 h1)) BOT) (xpn_eq (nfto (alg2 h2)) BOT)
         then assert ( xpn_eq (nfto (alg2 h1)) (nfto (alg2 h2)) )
         else ret Datatypes.tt) ;;
        (* temp1 ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret _) ;; *)
        h ← xtr_angle n h1 h2 ;;
        '(k1,hon1) ← get_fn (h1) ;;
        '(k2,hon2) ← get_fn (h2) ;;
        k ← xtr k1 k2 ;;
        hon ← ret (Datatypes.orb hon1 hon2) ;;
        k ← (if Datatypes.andb b hon2
             then
               k_star ← sample (uniform #| fin_name |) ;;
               ret (tag (alg k) (k_star : chName))
             else ret k) ;;
        h ← set_fn (h, hon, k) ;;
        ret h
      }
    ].
  ssprove_valid ; ssprove_valid'_2.
Defined.
Fail Next Obligation.

Definition GET_n_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ ] : chGETinp → chGETout]) (all_names) d.

Definition SET_n_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ ] : chSETinp → chSETout]) (all_names) d.

Definition GET_XTR (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ ] : chGETinp → chGETout]) ([ES; AS; HS]) d.

Definition SET_XTR (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ ] : chSETinp → chSETout]) ([ES; AS; HS]) d.

Definition XTR_names := [ES; HS; AS].

Definition XTR_n_ℓ d :=
  interface_hierarchy_foreach (fun n d' => [interface #val #[ XTR n d' ] : chXTRinp → chXTRout]) XTR_names d.

Lemma trimmed_Xtr : forall d n,
    trimmed
      [interface #val #[XTR n d] : chXTRinp → chXTRout ]
      (Xtr n d false (GET := GET n d) (SET := SET n d)).
Proof.
  intros.
  unfold trimmed.
  trim_is_interface.
Qed.

Definition xtr_level_raw (ℓ : nat) :=
  parallel_raw (List.map (fun n => pack (Xtr n ℓ false (GET := GET n ℓ) (SET := SET n ℓ))) XTR_names).

Lemma valid_xtr_level :
  forall d ℓ,
    ValidPackage f_parameter_cursor_loc (GET_XTR d.+1 :|: SET_XTR d.+1)
      (interface_foreach (fun n => [interface #val #[XTR n ℓ] : chXTRinp → chXTRout]) XTR_names)
      (xtr_level_raw ℓ).
Proof.
  intros.
  unfold xtr_level_raw.
  eapply valid_par_upto.
  1:{
    rewrite <- (trimmed_Xtr ℓ ES).
    rewrite <- (trimmed_Xtr ℓ HS).
    rewrite <- (trimmed_Xtr ℓ AS).

    solve_Parable ; unfold idents ; solve_imfset_disjoint.
  }
  1:{
    eapply valid_par_upto.
    {
      rewrite <- (trimmed_Xtr ℓ ES).
      rewrite <- (trimmed_Xtr ℓ HS).

      solve_Parable ; unfold idents ; solve_imfset_disjoint.
    }
    1: apply Xtr.
    1: apply Xtr.
    1: rewrite fsetU0 ; apply fsubsetxx.
    1: apply fsubsetxx.
    1: apply fsubsetxx.
  }
  1: apply Xtr.
  1:{
    rewrite fsetU0.
    apply fsubsetxx.
  }
  1:{
    unfold GET_XTR.
    unfold SET_XTR.
    unfold interface_hierarchy_foreach.
    simpl.
    solve_in_fset.
  }
  unfold XTR_names, interface_foreach, List.fold_left.
  rewrite <- !fset_cat.
  simpl.
  solve_in_fset.
Qed.

Definition xtr_level d ℓ :=
  {package (xtr_level_raw ℓ) #with (valid_xtr_level d ℓ)}.

Lemma trimmed_xtr_level d ℓ :
  trimmed
    (interface_foreach (fun n => [interface #val #[XTR n ℓ] : chXTRinp → chXTRout]) XTR_names)
    (xtr_level d ℓ).
Proof.
  intros.
  
  unfold xtr_level, xtr_level_raw, parallel_raw, XTR_names, List.map, interface_foreach, List.fold_left.
  unfold pack.

  rewrite <- (trimmed_Xtr ℓ HS).
  rewrite <- (trimmed_Xtr ℓ AS).
  rewrite <- (trimmed_Xtr ℓ ES).

  solve_trimmed.
Qed.

Lemma disjoint_n_interface_hierarchy_d :
  forall (n d : nat) (L : list name),
    n >= d ->
    forall N,
      List.In N L ->
  idents [interface #val #[XTR N n] : chXTRinp → chXTRout ]
  :#: idents
        (interface_hierarchy_foreach
           (λ N (ℓ : nat), [interface #val #[XTR N ℓ] : chXTRinp → chXTRout ]) L d).
Proof.
  intros.
  {
    unfold idents.
    rewrite <- fset1E.
    rewrite !imfset1.

    assert (n >= d) by Lia.lia.
    generalize dependent n.
    induction d ; intros.
    + unfold interface_hierarchy_foreach.
      simpl.
      rewrite <- fset0E.
      rewrite imfset0.
      now rewrite fdisjoints0.
    + unfold interface_hierarchy_foreach ; fold interface_hierarchy_foreach.
      simpl.
      rewrite imfsetU.
      rewrite fdisjointUr.
      rewrite IHd ; [ | Lia.lia..].
      rewrite Bool.andb_true_r.

      (* clear. *)
      clear -H.
      (* set (fset [::]). *)
      (* assert (fset1 (T:=Datatypes_nat__canonical__Ord_Ord) (XTR N n) :#: (λ '(n0, _), n0) @: f). *)
      (* { *)
      (*   subst f. *)
      (*   rewrite <- fset0E. *)
      (*   rewrite imfset0 ; rewrite fdisjoints0. *)
      (*   reflexivity. *)
      (* } *)
      (* generalize dependent f. *)

      destruct L.
      {
        simpl.
        rewrite <- fset0E.
        rewrite imfset0.
        now rewrite fdisjoints0.
      }
      simpl.
      set ([interface #val #[XTR n0 d] : chXTRinp → chXTRout ]).
      assert (fset1 (T:=Datatypes_nat__canonical__Ord_Ord) (XTR N n) :#: (λ '(n0, _), n0) @: f).
      {
        subst f.
        rewrite <- fset1E.
        rewrite imfset1 ; rewrite fdisjoints1.
        setoid_rewrite Bool.orb_false_r.
        unfold XTR , serialize_name.
        destruct n0 , N ; Lia.lia.
      }
      generalize dependent f.

      induction L ; intros.
      * easy.
      * assert (forall (T : ordType) B (f : B -> {fset T}) L (v : {fset T}),
            List.fold_left (fun y x => y :|: f x) L v
            =
              v :|: List.fold_left (fun y x => y :|: f x) L fset0).
        {
          clear ; intros.
          generalize dependent v.
          induction L ; intros.
          - simpl.
            rewrite fsetU0.
            reflexivity.
          - simpl.
            rewrite !(IHL (_ :|: f _)).
            rewrite fset0U.
            now rewrite fsetUA.
        }

        simpl.
        rewrite H1.
        rewrite imfsetU.
        rewrite fdisjointUr.

        rewrite imfsetU.
        rewrite fdisjointUr.

        rewrite IHL ; [ | now rewrite imfset0 ; rewrite fdisjoints0].

        rewrite H0.
        simpl.

        rewrite <- fset1E.
        rewrite imfset1.
        rewrite fdisjoints1.
        setoid_rewrite Bool.orb_false_r.
        setoid_rewrite Bool.orb_false_r.
        unfold XTR , serialize_name.
        destruct a, N ; Lia.lia.
  }
Qed.

(* Lemma XTR_Parable_ℓ (d : nat) : *)
(*   Parable {package par (par (Xtr ES d false) (Xtr HS d false)) (Xtr AS d false) } *)
(*     (ℓ_raw_packages *)
(*        (λ n : nat, {package par (par (Xtr ES n false) (Xtr HS n false)) (Xtr AS n false) }) d). *)

Definition XTR_packages
  (d : nat)
  :
  package fset0 (GET_XTR (d.+1) :|: SET_XTR (d.+1)) (XTR_n_ℓ (d.+1)).
Proof.
  refine (
  ℓ_packages (xtr_level d) _ _ _ (d.+1)).
  {
    intros.
    rewrite <- (trimmed_xtr_level d n).
    rewrite <- (trimmed_xtr_level d ℓ).
    solve_Parable.
    unfold idents.
    solve_imfset_disjoint.
  }
  {
    apply trimmed_xtr_level.
  }
  intros.
  simpl.
  rewrite !fset_cons.
  rewrite <- !(fset_cons _ [::]).
  solve_imfset_disjoint.
Defined.

(* Xpd *)

Context (xpd : chKey -> (chLabel * bitvec) -> code fset0 fset0 chKey).
Context (xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle).

Notation " 'chXPDinp' " :=
  (chHandle × 'bool × bitvec)
    (in custom pack_type at level 2).
Notation " 'chXPDout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition XPD (n : name) (ℓ : nat) : nat := serialize_name n ℓ.

Definition Xpd
  (n : name) (ℓ : nat)
  {GET : nat} {SET : nat} {HASH : nat}
  :
  package
    fset0
    [interface
     #val #[ GET ] : chGETinp → chGETout ;
     #val #[ SET ] : chSETinp → chSETout ;
     #val #[ HASH ] : chHASHinp → chHASHout
    ]
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  refine [package
      #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
        #import {sig #[ SET ] : chSETinp → chSETout }
        as set_fn ;;
        #import {sig #[ GET ] : chGETinp → chGETout }
        as get_fn ;;
        #import {sig #[ HASH ] : chHASHinp → chHASHout }
        as hash_fn ;;

        '(n1,_) ← PrntN n ;;
        label ← Labels n r ;;
        h ← xpd_angle n label h1 args ;;
        '(k1,hon) ← get_fn h1 ;;
        k ← (if xpn_eq n PSK
             then
               ℓ ← ret (ℓ + 1) ;;
               xpd k1 (label, args)
             else
               d ← hash_fn args ;;
               xpd k1 (label, d) ) ;;

        h ← set_fn (h, hon, k) ;;
        ret h
      }
    ].
  ssprove_valid ; ssprove_valid'_2.
Defined.
Fail Next Obligation.

Definition XPR :=
  [PSK; ESALT] ++
    [EEM; CET; BIND; BINDER; SHT; CHT; HSALT; RM; CAT; SAT; EAM] ++ (* has a single parent *)
    [] (* or exactly on sibling of n is contained in XPR *).

Definition XPD_n_ℓ (d : nat) :=
  interface_hierarchy_foreach (fun n d' => [interface
       #val #[ XPD n d' ] : chXPDinp → chXPDout
      ]) XPR d.

Definition GET_XPD (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ ] : chGETinp → chGETout]) (XPR) d.

Definition SET_XPD (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ ] : chSETinp → chSETout]) (XPR) d.

Lemma trimmed_Xpd : forall d n,
    trimmed
      [interface #val #[XPD n d] : chXPDinp → chXPDout ]
      (Xpd n d (GET := GET n d) (SET := SET n d) (HASH := HASH)).
Proof.
  intros.
  unfold trimmed.
  trim_is_interface.
Qed.

Definition xpd_level_raw (ℓ : nat) :=
  parallel_raw (List.map (fun n => pack (Xpd n ℓ (GET := GET n ℓ) (SET := SET n ℓ) (HASH := HASH))) XPR).

Lemma valid_xpd_level :
  forall d ℓ,
  ValidPackage f_parameter_cursor_loc (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[ HASH ] : chHASHinp → chHASHout])
   (interface_foreach (fun n => [interface #val #[XPD n ℓ] : chXPDinp → chXPDout]) XPR)
   (xpd_level_raw ℓ).
Proof.
  intros.

  unfold xpd_level_raw, parallel_raw, XPR, List.map, List.fold_left, "++".
  rewrite <- (trimmed_Xpd ℓ PSK).
  rewrite <- (trimmed_Xpd ℓ ESALT).
  rewrite <- (trimmed_Xpd ℓ EEM).
  rewrite <- (trimmed_Xpd ℓ CET).
  rewrite <- (trimmed_Xpd ℓ BIND).
  rewrite <- (trimmed_Xpd ℓ BINDER).
  rewrite <- (trimmed_Xpd ℓ SHT).
  rewrite <- (trimmed_Xpd ℓ CHT).
  rewrite <- (trimmed_Xpd ℓ HSALT).
  rewrite <- (trimmed_Xpd ℓ RM).
  rewrite <- (trimmed_Xpd ℓ CAT).
  rewrite <- (trimmed_Xpd ℓ SAT).
  rewrite <- (trimmed_Xpd ℓ EAM).

  repeat eapply valid_par_upto.
  all: try solve_Parable ; unfold idents ; solve_imfset_disjoint.
  all: try (apply valid_trim ; apply Xpd).
  all: try (rewrite fsetU0 ; apply fsubsetxx).
  all: try apply fsubsetxx.
  1:{
    unfold GET_XPD.
    unfold SET_XPD.
    unfold interface_hierarchy_foreach.
    simpl.
    rewrite <- !fset_cat.
    simpl.
    solve_in_fset.
  }
Qed. (* Slow? solve_in_rewrite? Issue with all? *)

Definition xpd_level d ℓ :=
  {package (xpd_level_raw ℓ) #with (valid_xpd_level d ℓ)}.

Lemma trimmed_xpd_level d ℓ :
  trimmed
    (interface_foreach (fun n => [interface #val #[XPD n ℓ] : chXPDinp → chXPDout]) XPR)
    (xpd_level d ℓ).
Proof.
  intros.
  
  unfold xpd_level, xpd_level_raw, parallel_raw, XPR, List.map, interface_foreach, List.fold_left, "++".
  unfold pack.

  rewrite <- (trimmed_Xpd ℓ PSK).
  rewrite <- (trimmed_Xpd ℓ ESALT).
  rewrite <- (trimmed_Xpd ℓ EEM).
  rewrite <- (trimmed_Xpd ℓ CET).
  rewrite <- (trimmed_Xpd ℓ BIND).
  rewrite <- (trimmed_Xpd ℓ BINDER).
  rewrite <- (trimmed_Xpd ℓ SHT).
  rewrite <- (trimmed_Xpd ℓ CHT).
  rewrite <- (trimmed_Xpd ℓ HSALT).
  rewrite <- (trimmed_Xpd ℓ RM).
  rewrite <- (trimmed_Xpd ℓ CAT).
  rewrite <- (trimmed_Xpd ℓ SAT).
  rewrite <- (trimmed_Xpd ℓ EAM).

  solve_trimmed.
Qed.

Definition XPD_packages (d : nat)
:
package fset0 ((GET_XPD (d.+1) :|: SET_XPD (d.+1)) :|: [interface
     #val #[ HASH ] : chHASHinp → chHASHout
  ]) (XPD_n_ℓ (d.+1)).
Proof.
  refine (ℓ_packages (xpd_level d) _ _ _ d.+1).
  {
    intros.
    rewrite <- (trimmed_xpd_level d n).
    rewrite <- (trimmed_xpd_level d ℓ).
    solve_Parable.
    unfold idents.
    simpl.

    solve_imfset_disjoint. (* n^2 *)
  }
  {
    apply trimmed_xpd_level.
  }
  intros.
  simpl.
  rewrite !fset_cons.
  rewrite <- !(fset_cons _ [::]).
  solve_imfset_disjoint. (* repeated proof? *)
Defined.
