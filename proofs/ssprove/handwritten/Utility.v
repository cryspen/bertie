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

Definition nfto (x : chName) : name :=
  match (nat_of_ord (otf x)) as k return (k < 20)%nat -> _ with
  | 0 => fun _ => BOT
  | 1 => fun _ => ES
  | 2 => fun _ => EEM
  | 3 => fun _ => CET
  | 4 => fun _ => BIND
  | 5 => fun _ => BINDER
  | 6 => fun _ => HS
  | 7 => fun _ => SHT
  | 8 => fun _ => CHT
  | 9 => fun _ => HSALT
  | 10 => fun _ => AS
  | 11 => fun _ => RM
  | 12 => fun _ => CAT
  | 13 => fun _ => SAT
  | 14 => fun _ => EAM
  | 15 => fun _ => PSK

  | 16 => fun _ => ZERO_SALT
  | 17 => fun _ => ESALT
  | 18 => fun _ => DH
  | 19 => fun _ => ZERO_IKM
  | n => fun H => False_rect _ (ltac:(easy))
  end%nat (ltn_ord (otf x)).

Definition chName_to_name (n : name) : chName := fto (inord (
  match n with
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
  end)).

Definition name_to_chName (n : name) : chName := fto (inord (
  match n with
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
  end)).

Axiom len : chKey -> chNat (* TODO: should be key *).
Definition alg : chKey -> chHash := (fun x => fto (fst (otf x))). (* TODO: should be key *)
Axiom alg2 : chHandle -> chName (* TODO: should be key *).
Definition tag : chHash -> chName -> chKey (* TODO: should be key *) :=
  fun x y => fto (pair (otf x) (otf y)).

(*** Helper definitions *)

From KeyScheduleTheorem Require Import ssp_helper.

Fixpoint interface_hierarchy (f : nat -> Interface) (ℓ : nat) : Interface :=
  match ℓ with
  | O => [interface]
  | S n => f n :|: interface_hierarchy f n
  end.

Fixpoint map_with_in {A B} (l : list A) (f : forall (x : A), (List.In x l) -> B) : list B :=
  match l as k return (k = l -> _) with
  | [] => fun _ => []
  | ( x :: xs ) =>
      fun H =>
        f x (eq_ind (x :: xs) (List.In x) (or_introl erefl) _ H)
          :: map_with_in xs (fun y H0 => f y (eq_ind (x :: xs) (List.In y) (or_intror H0) _ H))
  end erefl.

Fixpoint map_with_in_num (d : nat) (f : forall (x : nat), (x <= d)%nat -> raw_package) {struct d} : raw_package
  :=
  match d as k return (k <= d)%nat -> _ with
  | O => fun _ => emptym
  | S n =>
      fun H => par (f n (leq_trans (leqnSn n) H)) (map_with_in_num n (fun y Hf => f y (leq_trans Hf (leq_trans (leqnSn n) H))))
  end (leqnn d).

Definition ℓ_raw_packages (d : nat) (p : forall (n : nat), (n <= d)%nat ->  raw_package) : raw_package :=
  map_with_in_num d p.

(* Fixpoint ℓ_raw_packages_inner *)
(*   (u : nat) (d : nat) (H : (u >= d)%nat) *)
(*   (p : forall (n : nat), (u >= n)%nat -> raw_package) *)
(*   {struct d}: *)
(*   raw_package. *)
(* Proof. *)
(*   destruct d as [ | k]. *)
(*   - apply emptym. *)
(*   - refine (par _ _). *)
(*     + refine (p k _). *)
(*       apply (leq_trans (leqnSn _) H). *)
(*     + refine (ℓ_raw_packages_inner u k _ p). *)
(*       apply (leq_trans (leqnSn _) H). *)
(* Defined. *)

  (* := *)
  (* match d as k with *)
  (* | O => fun _ => emptym *)
  (* | S d' => *)
  (*     par (p d' _) (@ℓ_raw_packages_inner u d' p) *)
  (*                (* (eq_ind_r (λ d : nat, (d' <= d)%N) (leqnSn d') H) *) *)
  (* end _. *)

(* Definition ℓ_raw_packages *)
(*   (d : nat) *)
(*   (p : forall (n : nat), (d >= n)%nat -> raw_package) : *)
(*   raw_package := (ℓ_raw_packages_inner d (leqnn _) p). *)

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

Definition interface_foreach {A : Type} (f : A -> Interface) (l : list A) :=
  match l with
  | [] => [interface]
  | (x :: xs) => List.fold_left (fun y n => y :|: f n) xs (f x)
  end.

Definition interface_hierarchy_foreach {A : Type} (f : A -> nat -> Interface) (l : list A) :=
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
  (* try rewrite !imfsetU *)
  (* ; try rewrite !fdisjointUr *)
  (* ; repeat (apply /andP ; split) *)
  (* ; try rewrite !fdisjointUl *)
  (* ; try rewrite  <- !fset1E *)
  (* ; try rewrite !imfset1 *)
  (* ; try rewrite !fdisjoints1 *)
  (* ; try unfold "\notin" ; rewrite !ifF ; [ reflexivity | unfold "\in"; simpl; unfold "\in"; simpl ; try Lia.lia.. ]. *)

try rewrite !imfsetU
; try rewrite !fdisjointUr
; try rewrite !fdisjointUl
; try rewrite  <- !fset1E
; try rewrite !imfset1
; try rewrite !fdisjoints1
; try (unfold "\notin" ; rewrite !ifF ; [ reflexivity | unfold "\in"; simpl; unfold "\in"; simpl ; Lia.lia.. ])
(* ; setoid_rewrite Bool.orb_false_r *)
(* ; simpl *)
(* ; Lia.lia *)
.


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

Lemma fold_left_to_fsetU :
  forall (T : ordType) B (f : B -> {fset T}) L (v : {fset T}),
    List.fold_left (fun y x => y :|: f x) L v
    =
      v :|: List.fold_left (fun y x => y :|: f x) L fset0.
Proof.
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
Qed.

Lemma interface_hierarchy_foreach_subset : forall {A} f L d,
    interface_hierarchy_foreach f L d :<=: interface_hierarchy_foreach (A := A) f L d.+1.
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  simpl.
  rewrite fsubsetU ; [ reflexivity | ].
  rewrite fsubsetxx.
  now rewrite Bool.orb_true_r.
Qed.

Lemma lower_level_in_interface :
  forall (f : name -> nat -> Interface) (l : list name) d ℓ (p : nat -> _),
    p ℓ \in interface_foreach (f^~ ℓ) l ->
    (ℓ < d)%nat ->
    (p ℓ) \in
    interface_hierarchy_foreach f l d.
Proof.
  intros.
  induction d.
  - easy.
  - unfold interface_hierarchy_foreach.
    simpl.
    rewrite in_fset.
    rewrite mem_cat.
    simpl.
    destruct (ℓ == d) eqn:is_eq.
    {
      apply (ssrbool.elimT eqP) in is_eq.
      subst.
      now rewrite H.
    }
    {
      apply (ssrbool.elimF eqP) in is_eq.
      rewrite IHd ; [ easy | Lia.lia ].
    }
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

(* idents (f d) :#: idents (interface_hierarchy f d) *)

Lemma idents_interface_hierachy :
  forall f n d,
    (n >= d)%nat ->
    (forall x, (d > x)%nat -> idents (f n) :#: idents (f x)) ->
    idents (f n) :#: idents (interface_hierarchy f d).
Proof.
  clear ; intros.
  unfold idents.
  induction d ; simpl.
  - rewrite <- !fset0E.
    rewrite imfset0.
    apply fdisjoints0.
  - rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHd.
    + intros.
      rewrite Bool.andb_true_r.
      apply H0.
      easy.
    + Lia.lia.
    + intros.
      apply H0.
      Lia.lia.
Qed.

Fixpoint valid_pairs L I E P :=
  match I, E, P with
  | [], [], [] => True
  | [i], [e], [p] => valid_package L i e p
  | (i :: I'), (e :: E'), (p :: P') => valid_package L i e p /\ valid_pairs L I' E' P'
  | _, _, _ => False
  end.

Fixpoint trimmed_pairs E P :=
  match E, P with
  | [], [] => True
  | [e], [p] => trimmed e p
  | (e :: E'), (p :: P') => trimmed e p /\ trimmed_pairs E' P'
  | _, _ => False
  end.

Fixpoint all_idents_disjoint {A} f I :=
  match I with
  | [] | [_] => True
  | (x :: xs) =>
      idents (f x) :#: idents (interface_foreach (A := A) f xs) /\ all_idents_disjoint f xs
  end.

Lemma trimmed_parallel_raw : forall {A} f I L,
    all_idents_disjoint f I ->
    trimmed_pairs (List.map f I) L ->
    trimmed (interface_foreach (A := A) f I) (parallel_raw L).
Proof.
  intros.
  unfold parallel_raw.

  unfold interface_foreach.
  destruct L, I ; [ apply trimmed_empty_package | destruct I ; contradiction.. | ].
  simpl.
  generalize dependent a.
  generalize dependent r.
  generalize dependent I.
  (induction L ; destruct I) ; intros ; [ apply H0 | destruct I ; destruct H0 ; contradiction.. | ].

  setoid_rewrite fold_left_to_fsetU.
  simpl.
  rewrite fold_left_to_par.
  rewrite <- par_assoc.
  rewrite <- fold_left_to_par.
  rewrite fset0U.
  apply trimmed_par.
  3: apply IHL ; [ apply H | apply H0 ].
  2: apply H0.
  1:{
    rewrite <- (IHL I _ a0) ; [ | apply H | apply H0 ].
    simpl in H0.
    rewrite <- (proj1 H0).
    apply @parable.
    solve_Parable.
    apply H.
  }
Qed.

Lemma interface_foreach_cons : forall {A} f n E,
    interface_foreach f (n :: E) = f n :|: interface_foreach (A := A) f E.
Proof.
  induction E.
  - simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    reflexivity.
  - simpl.
    rewrite fold_left_to_fsetU.
    rewrite <- fsetUA.
    rewrite <- fold_left_to_fsetU.
    reflexivity.
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

Lemma interface_foreach_idents_cons : forall {A} f n E,
    idents (interface_foreach f (n :: E)) = (idents (f n)) :|: idents (interface_foreach (A := A) f E).
Proof.
  intros.
  rewrite interface_foreach_cons.
  now setoid_rewrite imfsetU.
Qed.

Theorem valid_parable :
  forall {N} (P : list raw_package) f g L I E,
    all_idents_disjoint f E ->
    trimmed_pairs (List.map f E) P ->
    valid_pairs L (List.map g I) (List.map f E) P ->
    valid_package L (interface_foreach (A := N) g I) (interface_foreach (A := N) f E) (parallel_raw P).
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
    rewrite in_fset in H2.
    inversion H2.
  }
  intros.
  rewrite interface_foreach_cons.
  rewrite <- (fsetUid L).
  destruct I ; [ contradiction | ].
  rewrite interface_foreach_cons.
  rewrite parallel_raw_cons.

  apply valid_par.
  3:{
    destruct I, E , P ; [ | destruct H1 ; try destruct I ; try destruct E ; contradiction .. | ].
    {
      simpl.
      constructor.
      intros ? ?.
      rewrite <- fset0E in H2.
      inversion H2.
    }
    apply IHP ; [ apply H | apply H0 | apply H1 ].
  }
  2:{
    simpl in H1.
    destruct (List.map g I), (List.map f E), P in H1 ; apply H1.
  }
  {
    clear -H0 H.
    generalize dependent E.
    generalize dependent n.
    generalize dependent a.
    induction P ; intros.
    {
      simpl.
      unfold Parable.
      rewrite domm0.
      apply fdisjoints0.
    }
    {
      generalize dependent a0.
      generalize dependent n.
      destruct E ; intros.
      {
        destruct H0 ; contradiction.
      }
      {
        specialize (IHP a0 n0 E).

        assert (idents (f n0) :#: idents (f n) /\ all_idents_disjoint f (n0 :: E)).
        {
          clear -H.
          (* unfold all_idents_disjoint. *)
          (* fold all_idents_disjoint. *)
          destruct E ; [ easy | ].
          destruct H as [? []].
          rewrite interface_foreach_idents_cons in H.
          now rewrite fdisjointUr in H.
        }
        destruct H1.
        specialize (IHP H2).

        assert (trimmed_pairs (List.map f [:: n0 & E]) (a0 :: P)).
        {
          clear -H0.
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
          destruct H0.
          rewrite <- H0.
          destruct E, P ; [ | destruct H4 ; try destruct E ; contradiction.. |  ] ; [ | destruct H4] ; rewrite <- H4 ; solve_Parable ; apply H1.
        }
        {
          apply IHP.
        }
      }
    }
  }
Qed.

Lemma interface_hierarchy_foreachU : (forall {A} f g L (d : nat),
  (interface_hierarchy_foreach f L d :|: interface_hierarchy_foreach g L d)
  = interface_hierarchy_foreach (A := A) (fun n d => f n d :|: g n d) L d).
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  induction d.
  - simpl.
    rewrite <- fset0E.
    rewrite !fset0U.
    reflexivity.
  - simpl.

    rewrite fsetUA.
    rewrite (fsetUC _ (interface_foreach _ _)).
    rewrite fsetUA.
    rewrite <- fsetUA.
    rewrite IHd.
    f_equal.

    clear IHd.
    induction L.
    {
      simpl.
      rewrite <- fset0E.
      rewrite !fset0U.
      reflexivity.
    }
    {
      rewrite !interface_foreach_cons.

      rewrite fsetUA.
      rewrite (fsetUC _ (f _ _)).
      rewrite fsetUA.
      rewrite <- fsetUA.

      rewrite IHL.
      reflexivity.
    }
Qed.

Theorem valid_forall : forall {A} g f u Names (d ℓ : nat),
    (d > ℓ)%nat ->
    all_idents_disjoint f Names ->
    trimmed_pairs (List.map f Names) (List.map (u ℓ) Names) ->
    (valid_pairs f_parameter_cursor_loc (List.map (g^~ ℓ) Names) (List.map f Names)
    (List.map (u ℓ) Names)) ->
  ValidPackage f_parameter_cursor_loc
    (interface_hierarchy_foreach g Names d)
    (interface_foreach (A := A) f Names) (parallel_raw (List.map (u ℓ) Names)).
Proof.
  intros.
  eapply valid_package_inject_import.
  - instantiate (1 := interface_foreach (g^~ ℓ) Names).

    unfold interface_hierarchy_foreach.
    unfold interface_hierarchy ; fold interface_hierarchy.

    (* apply fsubsetU. *)
    (* apply /orP. *)
    (* right. *)

    induction d.
    + discriminate.
    + apply fsubsetU. fold interface_hierarchy.
      apply /orP.
      destruct (ℓ == d) eqn:is_eq.
      * apply (ssrbool.elimT eqP) in is_eq.
        subst.
        left.
        apply fsubsetxx.
      * apply (ssrbool.elimF eqP) in is_eq.
        right.
        apply IHd.
        Lia.lia.
  - apply valid_parable.
    + apply H0.
    + apply H1.
    + apply H2.
Qed.

Check ℓ_raw_packages.

(* Lemma ℓ_raw_level_Parable *)
(*   (d : nat) *)
(*   (p : forall (n : nat), (d >= n)%nat -> _) *)
(*   (Hdisj : *)
(*     ∀ (n ℓ : nat) *)
(*       (H_le : (n <= d)%N) *)
(*       (H_n_le : (ℓ <= n)%N), *)
(*       Parable (p n H_le) (p ℓ (leq_trans H_n_le H_le))) *)
(*   (H_le : (d <= d)%nat) : *)
(*   Parable (p d H_le) (ℓ_raw_packages d p). *)
(* Proof. *)
(*   (* set (leqnn _). *) *)
(* Admitted. *)
(* (*   set d in i at 3. *) *)
  
(*   generalize dependent i. *)
(*   (* generalize dependent n. *) *)
(*   unfold Parable. *)
(*   induction d; intros. *)
(*   { *)
(*     unfold domm. *)
(*     rewrite <- fset0E. *)
(*     now rewrite fdisjoints0. *)
(*   } *)
(*   { *)
(*     unfold ℓ_raw_packages ; fold ℓ_raw_packages. *)
(*     rewrite (domm_union). *)
(*     rewrite fdisjointUr. *)
(*     rewrite IHℓ ; [ | Lia.lia | apply H0 ]. *)
(*     rewrite Bool.andb_true_r. *)
(*     apply (H0 n ℓ H). *)
(*   } *)
(* Qed. *)

Theorem ℓ_raw_package_trimmed :
  forall {L I}
    (d : nat)
    {f : nat -> Interface}
    (p : forall (n : nat) , (n <= d)%N → package L I (f n))
    (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le))
    (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d > n)%nat -> idents (f n) :#: idents (f ℓ)),
    trimmed (interface_hierarchy f d) (ℓ_raw_packages d p).
Proof.
  intros.
  induction d.
  - simpl.
    unfold trimmed ; now setoid_rewrite filterm0.
  - simpl.
    apply (trimmed_par (p d _) (ℓ_raw_packages d (λ (n : nat) _, p n _))).
    {
      apply @parable.
      rewrite <- H_trim_p.
      rewrite <- IHd.
      {
        solve_Parable.
        clear -Hdisj.

        apply idents_interface_hierachy.
        - Lia.lia.
        - intros.
          now apply Hdisj.
      }
      {
        intros.
        apply H_trim_p.
      }
      {
        intros.
        now apply Hdisj.
      }
    }
    {
      apply H_trim_p.
    }
    {
      apply IHd.
      2:{
        intros.
        now apply Hdisj.
      }
      intros.
      apply H_trim_p.
    }
Qed.

Definition ℓ_packages {L I}
  (d : nat)
  {f : nat -> Interface}
  (p : forall (n : nat), (d >= n)%nat → package L I (f n))
  (H : ∀ (d : nat) H, ValidPackage L I (f d) (p d H))
  (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge))
  (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d > n)%nat -> idents (f n) :#: idents (f ℓ))
  : package L I (interface_hierarchy f d).
Proof.
  refine {package ℓ_raw_packages d p}.
  induction d.
  - simpl.
    apply valid_empty_package.
  - simpl.
    rewrite <- (fsetUid L).
    rewrite <- (fsetUid I).

    apply valid_par.
    + (* epose ℓ_raw_level_Parable. *)
      rewrite <- H_trim_p.
      rewrite <- ℓ_raw_package_trimmed.
      2:{
        intros.
        apply H_trim_p.
      }
      2:{
        intros.
        apply Hdisj.
        - apply H0.
        - Lia.lia.
      }
      solve_Parable.

      apply idents_interface_hierachy.
      2: intros ; now apply Hdisj.
      Lia.lia.
    + apply H.
    + apply IHd.
      * intros.
        apply H.
      * intros.
        apply H_trim_p.
      * intros ; now apply Hdisj.
Defined.

