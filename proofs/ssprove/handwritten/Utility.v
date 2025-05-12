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
From KeyScheduleTheorem Require Import ssp_helper.

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

Lemma nfto_name_to_chName_cancel : forall a, nfto (name_to_chName a) = a.
Proof.
  intros.
  unfold nfto, name_to_chName ; rewrite otf_fto.
  unfold inord, insubd, odflt, oapp, insub.
  destruct idP, a ; (reflexivity || Lia.lia).
Qed.

Axiom len : chKey -> chNat (* TODO: should be key *).
Definition alg : chKey -> chHash := (fun x => fto (fst (otf x))). (* TODO: should be key *)
Axiom alg2 : chHandle -> chName (* TODO: should be key *).
Definition tag : chHash -> chName -> chKey (* TODO: should be key *) :=
  fun x y => fto (pair (otf x) (otf y)).

(*** Helper definitions *)


Fixpoint map_with_in {A: eqType} {B} (l : list A) (f : forall (x : A), (x \in l) -> B) : list B :=
  match l as k return (k = l -> _) with
  | [] => fun _ => []
  | ( x :: xs ) =>
      fun H =>
        f x (eq_ind (x :: xs) (fun l => x \in l) (mem_head x xs) _ H)
          :: map_with_in xs (fun y H0 => f y (eq_ind (x :: xs)%SEQ
                                            (λ l0 : seq A, (∀ x0 : A, x0 \in l0 → B) → (y \in l0) = true)
                                            (λ f0 : ∀ x0 : A, x0 \in (x :: xs)%SEQ → B,
                                               (eq_ind_r (Logic.eq^~ true) ([eta introTF (c:=true) orP] (or_intror H0)) (in_cons (T:=A) x xs y)))
                                            l H f))
  end erefl.

Fixpoint map_with_in_rel  {A : eqType} {B} (l : list A) (l' : list A) {H_in : forall a, a \in l' -> a \in l} (f : forall (x : A), (x \in l) -> B) {struct l'} : list B :=
  match l' as k return (forall a, a \in k -> a \in l)%nat -> _ with
  | [] => fun H => [::]
  | (x :: xs) =>
      fun H => (f x (H x (mem_head x xs))) :: (map_with_in_rel l xs (H_in := fun a H0 => H a (eq_ind_r [eta is_true] ([eta introTF (c:=true) orP] (or_intror H0)) (in_cons (T:=A) x xs a))) f)
  end H_in.

Fixpoint map_with_in_num (d : nat) (f : forall (x : nat), (x <= d)%nat -> raw_package) {struct d} : raw_package
  :=
  match d as k return (k <= d)%nat -> _ with
  | O => fun H => f O H
  | S n =>
      fun H => par (map_with_in_num n (fun y Hf => f y (leq_trans Hf (leq_trans (leqnSn n) H)))) (f (S n) H)
  end (leqnn d).

Fixpoint map_with_in_num_upper (d : nat) (i : nat) {H_le : (i <= d)%nat} (f : forall (x : nat), (x <= d)%nat -> raw_package) {struct i} : raw_package :=
  match i as k return (k <= d)%nat -> _ with
  | O => fun H => f O H
  | S n =>
      fun H => par (map_with_in_num_upper d n (H_le := (leq_trans (leqnSn n) H)) f) (f (S n) H)
  end H_le.

Definition ℓ_raw_packages (d : nat) (p : forall (n : nat), (n <= d)%nat ->  raw_package) : raw_package :=
  map_with_in_num_upper d d (H_le := leqnn d) p.

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
    (H_disj : idents E1 :#: idents E2)
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

Fixpoint interface_foreach {A : Type} (f : A -> Interface) (l : list A) :=
  match l with
  | [] => [interface]
  | [x] => f x
  | (x :: xs) => f x :|: interface_foreach f xs
  end.

Definition mem_tail : forall {A : eqType} a (l : list A), forall {x}, x \in l -> x \in a :: l :=
  fun A a l x H =>
    (eq_ind_r [eta is_true] ([eta introTF (c:=true) orP] (or_intror H)) (in_cons (T:=A) a l x)).

Fixpoint interface_foreach_in_rel {A : eqType} (l : list A) (l' : list A) {H_in : forall a, a \in l' -> a \in l} (f : forall (a : A), (a \in l) -> Interface) {struct l'} : Interface :=
  (match l' as k return (forall a, a \in k -> a \in l) -> _ with
         | [] => fun _ => [interface]
         | (x :: xs) =>
             fun H_in =>
               match xs with
               | [] => f x (H_in x (mem_head x xs))
               | (y :: ys) =>
                   f x (H_in x (mem_head x xs))
                     :|: interface_foreach_in_rel l xs (H_in := fun a H => H_in a (mem_tail x xs H)) f
               end
          end H_in).

Fixpoint interface_hierarchy (f : nat -> Interface) (ℓ : nat) : Interface :=
  match ℓ with
  | O => f O
  | S n => interface_hierarchy f n :|: f (S n)
  end.
  (* interface_foreach f (iota O (S ℓ)). *)

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

Require Import Lia.

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

    (* now apply IHindex2. *)
    (* Qed. *)
Admitted.

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
      {| hasDecEq.eq_op := name_eq; hasDecEq.eqP := name_equality |}
  |}.

Lemma serialize_name_notin_all :
  forall d,
  forall (ℓ1 ℓ2 : nat),
  forall (n1 n2 : name),
  forall (index1 index2 : nat),
    (index1 = index2) /\ ((ℓ1 <> ℓ2)%N \/ (n1 <> n2)%N) \/ ((index1 <> index2)%nat /\ (ℓ1 <= d)%N /\ (ℓ2 <= d)%N) ->
     serialize_name n1 ℓ1 d index1 <> serialize_name n2 ℓ2 d index2.
Proof.
  intros.
  destruct H as [[? [ | ]] | ] ; subst.
  + now apply serialize_name_notin.
  + now apply serialize_name_notin_different_name.
  + now apply serialize_name_notin_different_index.
Qed.

Lemma serialize_name_notin_all_iff :
  forall d,
  forall (ℓ1 ℓ2 : nat),
  forall (n1 n2 : name),
  forall (index1 index2 : nat),
    (index1 = index2) /\ ((ℓ1 <> ℓ2)%N \/ (n1 <> n2)%N) \/ ((index1 <> index2)%nat /\ (ℓ1 <= d)%N /\ (ℓ2 <= d)%N) <->
     serialize_name n1 ℓ1 d index1 <> serialize_name n2 ℓ2 d index2.
Proof.
  intros.
  split ; intros.
  - destruct H as [[? [ | ]] | ] ; subst.
    + now apply serialize_name_notin.
    + now apply serialize_name_notin_different_name.
    + now apply serialize_name_notin_different_index.
  - destruct (index1 == index2) eqn:index_eq ; move: index_eq => /eqP index_eq ; subst.
    + left ; split ; [ reflexivity | ].
      destruct (ℓ1 == ℓ2) eqn:l_eq ; move: l_eq => /eqP l_eq ; subst.
      * right.
        destruct (n1 == n2) eqn:n_eq ; move: n_eq => /eqP n_eq ; subst.
        -- contradiction.
        -- assumption.
      * left.
        assumption.
    + right ; split ; [ assumption | ].

      admit.
Admitted.

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
; repeat (apply /andP ; split)
; try (rewrite (ssrbool.introF (fset1P _ _)) ; [ reflexivity | ])
; try (now apply serialize_name_notin_all ; Lia.lia || (now left ; split ; [ reflexivity | ((timeout 5 now right) || (timeout 5 now left)) ]) || (now right ; split ; [ discriminate | split ; [ Lia.lia | Lia.lia ] ]))
(* ; try (now apply serialize_name_notin ; Lia.lia) *)
(* ; try (now apply serialize_name_notin_different_name ; Lia.lia) *)
(* ; try (now apply serialize_name_notin_different_index ; Lia.lia) *)
; try (now apply serialize_name_notin_smaller_than_start ; try Lia.lia)
; try (now symmetry ; apply serialize_name_notin_smaller_than_start ; try Lia.lia)
(* ; try (idtac ; [ reflexivity | unfold "\in"; simpl; unfold "\in"; simpl ; Lia.lia.. ]) *)
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

(* (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f n) :#: idents (f ℓ)), *)

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

(*   forall f n d, *)
(*     (n > d)%nat -> *)
(*     (forall x, (d >= x)%nat -> idents (f n) :#: idents (f x)) -> *)
(*     idents (f n) :#: idents (interface_hierarchy f d). *)
(* Proof. *)
(*   clear ; intros. *)
(*   unfold idents. *)
(*   induction d ; simpl. *)
(*   - now apply H0. *)
(*   - rewrite imfsetU. *)
(*     rewrite fdisjointUr. *)
(*     rewrite IHd. *)
(*     + intros. *)
(*       now apply H0. *)
(*     + Lia.lia. *)
(*     + intros. *)
(*       apply H0. *)
(*       Lia.lia. *)
(* Qed. *)

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

Lemma interface_foreach_cons : forall {A} f n E,
    interface_foreach f (n :: E) = f n :|: interface_foreach (A := A) f E.
Proof.
  induction E.
  - simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    reflexivity.
  - simpl.
    (* rewrite fold_left_to_fsetU. *)
    (* rewrite <- fsetUA. *)
    (* rewrite <- fold_left_to_fsetU. *)
    reflexivity.
Qed.

Lemma interface_foreach_cat : forall {A} f E1 E2,
    interface_foreach f (E1 ++ E2) = interface_foreach (A := A) f E1 :|: interface_foreach (A := A) f E2.
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

Lemma interface_hierarchy_U : (forall f g ℓ,
  (interface_hierarchy f ℓ :|: interface_hierarchy g ℓ)
  = interface_hierarchy (fun n => f n :|: g n) ℓ).
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

Lemma interface_hierarchy_foreachU : (forall {A} f g L (d : nat),
  (interface_hierarchy_foreach f L d :|: interface_hierarchy_foreach g L d)
  = interface_hierarchy_foreach (A := A) (fun n d => f n d :|: g n d) L d).
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
      g @: (interface_foreach f L) = interface_foreach (fun n => g @: f n) L).
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

Lemma trimmed_parallel_raw : forall {A : eqType} {f I L},
    (∀ x y : A, x ≠ y → idents (f x) :#: idents (f y)) -> uniq I ->
    (* all_idents_disjoint f I -> *)
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

Lemma interface_foreach_in_rel_cons : forall {A : eqType} l (a : A) l' H_in f,
    interface_foreach_in_rel l (a :: l') (H_in := H_in) f = f a (H_in a (mem_head _ _)) :|: (interface_foreach_in_rel l l' (H_in := fun a H => H_in a (mem_tail _ _ H)) f).
Proof.
  intros.
  induction l'.
  - simpl.
    rewrite <- fset0E ; rewrite fsetU0.
    reflexivity.
  - unfold interface_foreach_in_rel ; fold @interface_foreach_in_rel.
    reflexivity.
Qed.

Theorem valid_parable :
  forall {N : eqType} (P : list raw_package) f g L I E,
    (∀ x y, x ≠ y → idents (f x) :#: idents (f y)) -> uniq E ->
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


  Lemma trimmed_eq_rect_r :
    forall L I1 I2 E (m : package L I1 E) (f : I2 = I1),
      trimmed E (eq_rect_r (fun I => package L I E) m f) = trimmed E m.
  Proof. now destruct f. Qed.

  Lemma trimmed_eq_rect_r2 :
    forall L I E1 E2 (m : package L I E1) (f : E2 = E1),
      trimmed E1 (eq_rect_r [eta package L I] m f) = trimmed E2 m.
  Proof. now destruct f. Qed.

  Lemma trimmed_eq_rect :
    forall L I E1 E2 (m : package L I E1) g H,
      trimmed E2 (eq_rect E1 (fun E => package L I E) m g H) = trimmed E2 m.
  Proof. now destruct H. Qed.

  Lemma trimmed_eq_rect2 :
    forall L I E1 E2 (m : package L I E1) g H,
      trimmed E2 (eq_rect E1 [eta package L I] m g H) = trimmed E2 m.
  Proof. now destruct H. Qed.

  Lemma trimmed_pairs_cons :
    forall a b c d,
      trimmed_pairs (a :: b) (c :: d) <-> (trimmed a c /\ trimmed_pairs b d).
  Proof. now intros ? [] ? []. Qed.

  Lemma valid_pairs_cons :
    forall L a b c d e f,
      valid_pairs L (a :: b) (c :: d) (e :: f) <-> (valid_package L a c e /\ valid_pairs L b d f).
  Proof. now intros ? ? [] ? [] ? []. Qed.

  Lemma map_eta : forall {A B} (f : A -> B) a l, List.map f (a :: l) = f a :: List.map f l.
  Proof. reflexivity. Qed.

  Lemma map_with_in_eta : forall {A : eqType} {B} a l (f : forall (x : A), (x \in a :: l) -> B),
      map_with_in (a :: l) f
      = f a (mem_head (T:=A) a l)
          :: map_with_in l
          (λ (y : A) (H0 : y \in l), f y (mem_tail a l H0)).
  Proof. reflexivity. Qed.

  Lemma map_with_in_rel_eta : forall {A : eqType} {B} l a l' H_in (f : forall (x : A), (x \in l) -> B),
      map_with_in_rel l (a :: l') (H_in := H_in) f
      = f a (H_in a (mem_head a l')) :: map_with_in_rel l l' (H_in := fun x H => H_in x (mem_tail a l' H)) f.
  Proof. reflexivity. Qed.

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

  Definition parallel_package
    {A : eqType} (d : nat) {L} {f : A -> _} {g} Names (i : forall (a : A), package L (f a) (g a))
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
    (* intros. *)
    (* induction Lf. *)
    (* + simpl. *)
    (*   rewrite <- fset0E. *)
    (*   unfold idents. *)
    (*   rewrite imfset0. *)
    (*   apply fdisjoint0s. *)
    (* + rewrite interface_foreach_cons. *)
    (*   unfold idents. *)
    (*   rewrite !imfsetU. *)
    (*   rewrite fdisjointUl. *)
    (*   rewrite IHLf ; clear IHLf. *)
    (*   rewrite Bool.andb_true_r. *)

    (* induction Lg. *)
    (* * simpl. *)
    (*   rewrite <- fset0E. *)
    (*   unfold idents. *)
    (*   rewrite imfset0. *)
    (*   apply fdisjoints0. *)
    (* * rewrite interface_foreach_cons. *)
    (*   unfold idents. *)
    (*   rewrite !imfsetU. *)
    (*   rewrite fdisjointUr. *)
    (*   rewrite IHLg ; clear IHLg. *)
    (*   rewrite Bool.andb_true_r. *)
    (*   apply H. *)

    intros.
    apply idents_disjoint_foreach ; intros.
    rewrite fdisjointC.
    apply idents_disjoint_foreach ; intros.
    rewrite fdisjointC.
    apply H.
  Qed.

  Theorem valid_parable_map_with_in_rel :
    forall {N : eqType} (P : list raw_package) L I E2 E1 H_in f g,
      (∀ (x y : N) Hx Hy, x ≠ y → idents (f x Hx) :#: idents (f y Hy)) -> uniq E1 ->
      trimmed_pairs (map_with_in_rel E2 E1 (H_in := H_in) f) P ->
      valid_pairs L (List.map g I) (map_with_in_rel E2 E1 (H_in := H_in) f) P ->
      valid_package L (interface_foreach (A := N) g I) (interface_foreach_in_rel E2 E1 (H_in := H_in) f) (parallel_raw P).
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
    {A : eqType} (d : nat) {L} Names {f : A -> _} {g : forall (a : A), (a \in Names) -> _} (i : forall (a : A) (H : a \in Names), package L (f a) (g a H))
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

Theorem valid_forall_map_with_in_rel : forall {A : eqType} {L} Names l (d : nat) {g f} ℓ (H_le : (ℓ <= d)%nat) (u : forall a (H : a \in Names), raw_package) H_in,
    (∀ (x y : A), x ≠ y → idents (f x) :#: idents (f y)) -> uniq l ->
    (trimmed_pairs (List.map f l) (map_with_in_rel Names l (H_in := H_in) u)) ->
    (valid_pairs L (List.map g l) (List.map (f) l)
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
  forall {A : eqType} {L} {g f} Names l (ℓ : nat) (u : forall a (H : a \in Names), package L (g a ℓ) (f a)) H_in,
  valid_pairs L (List.map (g^~ ℓ) l) (List.map f l)
    (map_with_in_rel Names l (H_in := H_in) (λ (a : A) (H3 : (a \in Names) = true), pack (u a H3))).
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

Theorem map_with_in_num_upper_trimmed :
  forall (* {L I} *)
    (d : nat)
    {f : nat -> Interface}
    (p : forall (ℓ : nat) , (ℓ <= d)%N → raw_package (* L I (f ℓ) *))
    (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le))
    (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f ℓ) :#: idents (f n)),
    forall k (K_le : (k <= d)%nat),
    trimmed (interface_hierarchy f k) (map_with_in_num_upper d k (H_le := K_le) p).
Proof.
  intros.
  induction k ; intros.
  - simpl.
    (* destruct k ; [ | discriminate ]. *)
    apply H_trim_p.
  - unfold ℓ_raw_packages.
    unfold interface_hierarchy ; fold interface_hierarchy.

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

Theorem ℓ_raw_package_trimmed :
  forall (* {L I} *)
    (d : nat)
    {f : nat -> Interface}
    (p : forall (ℓ : nat) , (ℓ <= d)%N → raw_package (* L I (f ℓ) *))
    (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le))
    (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f ℓ) :#: idents (f n)),
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
  (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f ℓ) :#: idents (f n))
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

Definition combined (A : eqType) (d : nat) L (f : A -> _) g Names (i : forall (n : nat), (n <= d)%nat -> forall (a : A), package L (f a) (g a n))
    (H : forall n, (n <= d)%nat -> ∀ x y : A, x ≠ y → idents (g x n) :#: idents (g y n))
    (H0 : forall n ℓ, (ℓ < n)%nat -> (n <= d)%nat -> ∀ x y : A, idents (g x ℓ) :#: idents (g y n))
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

Definition parallel_package_with_in_rel_hierarchy {A : eqType} {L} {g f} Names l  (d : nat) (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names), package L (g a ℓ) (f a ℓ)) H_in :
  (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) ->
  uniq l ->
  (forall ℓ H_le, trimmed_pairs (List.map (f^~ℓ) l) (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) ->
  forall ℓ H_le,
  package L (interface_foreach (g^~ ℓ) l) (interface_foreach (f^~ ℓ) l) :=
  (fun H H0 H1 ℓ H_le =>
     {package (parallel_raw (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H))))
            #with
           valid_forall_map_with_in_rel
           (f := (f^~ℓ))
           Names l d _ H_le (u _ _) H_in (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq)) H0 (H1 _ _)
           (forall_valid_from_packages Names l _ (u ℓ H_le) H_in)}).

Definition ℓ_parallel {A : eqType} {L} {g f} Names l  (d : nat) (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names), package L (g a ℓ) (f a ℓ)) H_in :
  (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) ->
  uniq l ->
  (forall ℓ H_le, trimmed_pairs (List.map (f^~ℓ) l) (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) ->
  package L
    (interface_hierarchy_foreach g l d)
    (interface_hierarchy_foreach f l d) :=
  (fun H H0 H1 =>
     ℓ_packages d
       (λ ℓ H_le, parallel_package_with_in_rel_hierarchy Names l d u H_in H H0 H1 ℓ H_le)
       (fun a H_le => trimmed_parallel_raw (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq)) H0 (H1 _ _))
       (fun n ℓ H_le H_ge =>
          idents_foreach_disjoint_foreach _ _ _
            (fun _ _ =>
               H _ _ _ _
                 (or_intror
                    ((eq_ind_r
                        (λ ℓ0 : nat, (ℓ0 < n)%N → False)
                        (λ H_le0 : (n < n)%N,
                            (eq_ind_r (λ b : bool, b → False) (λ H_le1 : false, False_ind False (eq_ind false (λ e : bool, if e then False else True) I true H_le1)) (ltnn n)) H_le0) (y:=ℓ))^~ H_le)
         )))).

Definition trimmed_ℓ_packages {L}
  (d : nat)
  {g : nat -> Interface}
  {f : nat -> Interface}
  (p : forall (n : nat), (d >= n)%nat → package L (g n) (f n))
  (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge))
  (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f ℓ) :#: idents (f n))
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

Lemma idents_interface_hierachy3 :
  forall g f d,
    (forall x, (x <= d)%nat -> idents g :#: idents (f x)) ->
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


(*** Ltac Tactics *)

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
      idents (interface_foreach (fun a => fset [(serialize_name a x k index, T1)]) Lf)
        :#: idents (interface_foreach (fun a => fset [(serialize_name a y k index, T2)]) Lg).
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
    interface_hierarchy_foreach (fun n ℓ => (fset [(serialize_name n ℓ k index, p)])) L d.+1 =
      interface_foreach (fun n => fset [(serialize_name n O k index, p)]) L
        :|: interface_hierarchy_foreach (fun n ℓ => fset [(serialize_name n (ℓ.+1) k index,p ) ]) L d
  .
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

  Lemma interface_foreach_subset_pairs : forall {A: eqType} f g (L : seq A),
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

  Lemma interface_hierarchy_subset_pairs : forall f g d,
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

  Lemma interface_hierarchy_foreach_subset_pairs : forall {A: eqType} f g (L : seq A) d,
      (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: g x ℓ) ->
      interface_hierarchy_foreach f L d :<=: interface_hierarchy_foreach (A := A) g L d.
  Proof.
    intros.
    unfold interface_hierarchy_foreach.
    apply interface_hierarchy_subset_pairs.
    intros.
    apply interface_foreach_subset_pairs ; eauto.
  Qed.

  Lemma interface_foreach_subset : forall {A: eqType} f (L : seq A) K,
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

  Lemma interface_foreach_subsetR : forall {A: eqType} f (L : seq A) K,
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

  Lemma interface_hierarchy_foreach_subset : forall {A: eqType} f (L : seq A) d K,
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

  Lemma interface_hierarchy_foreach_subsetR : forall {A: eqType} f (L : seq A) d K,
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
    (forall n ℓ, (ℓ < n)%nat -> (n <= d)%nat -> ∀ x y, idents (f x ℓ) :#: idents (f y n)) ->
    package fset0 (interface_hierarchy_foreach f L d) (interface_hierarchy_foreach f L d).

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

  Lemma interface_foreach_swap :
    (forall {A} (a b : A) l f, interface_foreach f (a :: b :: l) = interface_foreach f (b :: a :: l)).
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

  Lemma interface_hierarchy_foreach_cons : (forall {A} f a L (d : nat),
    interface_hierarchy_foreach f (a :: L) d
    = interface_hierarchy (f a) d :|: interface_hierarchy_foreach (A := A) f L d).
  Proof.
    intros.
    unfold interface_hierarchy_foreach.
    rewrite interface_hierarchy_U.
    f_equal.
    setoid_rewrite interface_foreach_cons.
    reflexivity.
  Qed.

  Lemma interface_hierarchy_foreach_cat : forall {A} f L1 L2 d,
      interface_hierarchy_foreach f (L1 ++ L2) d =
      interface_hierarchy_foreach (A := A) f L1 d :|: interface_hierarchy_foreach (A := A) f L2 d.
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
            interface_foreach (fun x => if x \in L2 then f x else fset [::]) L1).
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
      (if a \in L1 then f a else fset [::]) :|:
      interface_foreach (λ x : A, if x \in L2%SEQ then f x else fset [::]) L1.
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
      interface_foreach (A := A) (fun x => if x \in L1 then f x else [interface]) L2.
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

  Lemma trimmed_trim : forall I p, trimmed I (trim I p).
  Proof.
    intros. unfold trimmed. now rewrite trim_idemp.
  Qed.

  Ltac solve_direct_in := rewrite !fsubUset ; repeat (apply /andP ; split) ; repeat (apply fsubsetxx || (apply fsubsetU ; apply /orP ; ((right ; apply fsubsetxx) || left))).


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
    | |- context [ idents (interface_foreach ?f ?L) :#: idents (interface_foreach ?g ?K) ] =>
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

  Lemma function_fset_cons_l :
    forall {A : eqType} {T} x xs K, (fun (n : A) => fset (x n :: xs n) :|: K) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n) :|: K).
  Proof. now intros ; setoid_rewrite <- (fset_cat). Qed.

  Lemma function_fset_cat_l :
    forall {A : eqType} {T} ys xs K, (fun (n : A) => fset (ys n ++ xs n) :|: K) = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n) :|: K).
  Proof. now intros ; setoid_rewrite <- (fset_cat). Qed.

  Lemma function_fset_cat_middle :
    forall {A : eqType} {T} ys xs L R, (fun (n : A) => L :|: fset (ys n ++ xs n) :|: R) = (fun (n : A) => L :|: fset (T := T) (ys n) :|: fset (xs n) :|: R).
  Proof.
    intros.
    setoid_rewrite fsetUC.
    setoid_rewrite <- fsetUA.
    setoid_rewrite <- (fset_cat).
    reflexivity.
  Qed.

  Lemma function_fset_cat :
    forall {A : eqType} {T} ys xs, (fun (n : A) => fset (ys n ++ xs n)) = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n)).
  Proof. now setoid_rewrite <- (fset_cat). Qed.

  Lemma function_fset_cons :
    forall {A : eqType} {T} x xs, (fun (n : A) => fset (x n :: xs n)) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n)).
  Proof. now setoid_rewrite <- (fset_cat). Qed.

  Lemma function2_fset_cat :
    forall {A B : eqType} {T} x xs, (fun (a : A) (b : B) => fset (x a b :: xs a b)) = (fun (a : A) (b : B) => fset (T := T) ([x a b]) :|: fset (xs a b)).
  Proof. now setoid_rewrite <- (fset_cat). Qed.

  Lemma advantage_reflexivity :
    forall P A, AdvantageE P P A = 0%R.
  Proof.
    unfold AdvantageE.
    intros.
    rewrite subrr.
    rewrite Num.Theory.normr0.
    reflexivity.
  Qed.


