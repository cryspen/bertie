From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve Require Import choice_type Package Prelude.
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

From SSProve Require Import jasmin_word.

From SSProve Require Import Schnorr SigmaProtocol.

From SSProve Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve Require Import SPropBase.

From SSProve Require Import Axioms ChoiceAsOrd SubDistr Couplings
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
  k ← get (n , chOption ('fin #| T |)) ;;
  match k with
  | None =>
      fn
  | Some x =>
      fnSucc x
  end.

Definition get_or_fn (n : nat) (T : finType) `{Positive #|T|} (fn : raw_code ('fin #|T|)) : raw_code ('fin #|T|) :=
  k ← get ( n , chOption ('fin #| T |) ) ;;
  match k with
  | None =>
      fn
  | Some x =>
      ret x
  end.

Definition get_or_fail (n : nat) (T : finType) `{Positive #|T|} : raw_code ('fin #|T|) :=
  k ← get ( n , chOption ('fin #| T |) ) ;;
  match k with
  | None =>
      @fail ('fin #|T|) ;;
      ret (chCanonical 'fin #|T|)
  | Some x =>
      ret x
  end.

Definition get_has (n : nat) (T : finType) `{Positive #|T|} : raw_code 'bool :=
  k ← get ( n , chOption ('fin #| T |) ) ;;
  ret match k with
    | None =>
        false
    | Some x =>
        true
    end.

Definition set_at (n : nat) (T : finType) `{Positive #|T|} (x : T)
  : raw_code 'unit :=
  #put ( n , chOption ('fin #| T |) ) := Some (fto x) ;; ret Datatypes.tt.

Definition get_or_sample (n : nat) (T : finType) `{Positive #|T|} : raw_code ('fin #|T|) :=
  get_or_fn n T (
      x ← sample uniform #| T | ;;
      #put ( n , chOption ('fin #| T |) ) := Some x ;;
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

Fixpoint interface_foreach {A : Type} {B : ordType} {C} (f : A -> {fmap B → C}) (l : list A) :=
  match l with
  | [] => emptym
  | [x] => f x
  | (x :: xs) => unionm (f x) (interface_foreach f xs)
  end.

Definition mem_tail : forall {A : eqType} a (l : list A), forall {x}, x \in l -> x \in a :: l :=
  fun A a l x H =>
    (eq_ind_r [eta is_true] ([eta introTF (c:=true) orP] (or_intror H)) (in_cons (T:=A) a l x)).

Fixpoint interface_foreach_in_rel {A : eqType} {B : ordType} {C} (l : list A) (l' : list A) {H_in : forall a, a \in l' -> a \in l} (f : forall (a : A), (a \in l) -> {fmap B -> C}) {struct l'} : {fmap B -> C} :=
  (match l' as k return (forall a, a \in k -> a \in l) -> _ with
         | [] => fun _ => [interface]
         | (x :: xs) =>
             fun H_in =>
               match xs with
               | [] => f x (H_in x (mem_head x xs))
               | (y :: ys) =>
                   unionm (f x (H_in x (mem_head x xs)))
                     (interface_foreach_in_rel l xs (H_in := fun a H => H_in a (mem_tail x xs H)) f)
               end
          end H_in).

Fixpoint interface_hierarchy {B : ordType} {C} (f : nat -> {fmap B -> C}) (ℓ : nat) : {fmap B -> C} :=
  match ℓ with
  | O => f O
  | S n => unionm (interface_hierarchy f n) (f (S n))
  end.
  (* interface_foreach f (iota O (S ℓ)). *)

Fixpoint interface_hierarchy_in_num_upper {B : ordType} {C} (ℓ' : nat) (ℓ : nat) (H_lt : (ℓ <= ℓ')%nat) (f : forall (n : nat), (n <= ℓ')%nat -> {fmap B -> C}) : {fmap B -> C} :=
  match ℓ return (ℓ <= ℓ')%nat -> _ with
  | O => f O
  | S n => fun H_lt => unionm (interface_hierarchy_in_num_upper ℓ' n (leq_trans (leqnSn n) H_lt) f) (f (S n) H_lt)
  end H_lt.
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
(* Ltac solve_Parable := *)
(*   match goal with *)
(*   | [ |- context [ Parable (trim _ ?a) (trim _ ?b) ] ] => *)
(*       apply parable_trim *)
(*       ; try (unfold idents *)
(*              ; rewrite <- !fset1E *)
(*              ; rewrite !imfset1 *)
(*              ; now rewrite fdisjoint1s) *)
(*   | Ha : trimmed ?Ea ?a , *)
(*       Hb : trimmed ?Eb ?b *)
(*     |- context [ Parable ?a ?b ] => *)
(*       rewrite <- Ha ; rewrite <- Hb ; solve_Parable *)
(*   | Ha : trimmed ?Ea ?a , *)
(*       Hb : trimmed ?Eb ?b *)
(*     |- context [ Parable ?a (?b ∘ ?c) ] => *)
(*       rewrite <- Ha ; *)
(*       rewrite <- Hb ; *)
(*       erewrite !link_trim_commut ; *)
(*       solve_Parable *)
(*   | Ha : trimmed ?Ea ?a , *)
(*       Hb : trimmed ?Eb ?b *)
(*     |- context [ Parable (?b ∘ ?c) ?a ] => *)
(*       rewrite <- Ha ; *)
(*       rewrite <- Hb ; *)
(*       erewrite !link_trim_commut ; *)
(*       solve_Parable *)
(*   | |- context [ Parable ?a (par ?b ?c) ] => *)
(*       apply parable_par_r ; solve_Parable *)
(*   | |- context [ Parable (par ?a ?b) ?c ] => *)
(*       apply parable_par_l ; solve_Parable *)
(*   end. *)

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

    now apply IHindex2.
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
; try (now apply serialize_name_notin_all ; (now left ; split ; [ reflexivity | ((timeout 5 now right) || (timeout 5 now left)) ]) || (now right ; split ; [ discriminate | split ; [ Lia.lia | Lia.lia ] ]))
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

Ltac trim_is_interface :=
  setoid_rewrite filterm_set ; fold chElement ;
  rewrite <- fset1E ;
  setoid_rewrite in_fset1 ;
  (* simpl ; *)
  rewrite eqxx ;
  rewrite filterm0 ;
  reflexivity.

(* Ltac trimmed_package p := *)
(*   match type of p with *)
(*   | package ?L ?I ?E => *)
(*       assert (trimmed E p) by now unfold trimmed ; trim_is_interface *)
(*   end. *)

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
    getm (interface_foreach (f^~ ℓ) l) (p ℓ) ->
    (ℓ <= d)%nat ->
    getm (interface_hierarchy_foreach f l d) (p ℓ).
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  simpl.

  induction d.
  - destruct ℓ ; [ apply H | discriminate ].
  - simpl.
    rewrite unionmE.
    destruct (ℓ == d.+1) eqn:is_eq.
    {
      destruct (isSome (interface_hierarchy _ _ _)) eqn:H_ ; [ apply H_ | ].

      apply (ssrbool.elimT eqP) in is_eq.
      subst.
      apply H.
    }
    {
      apply (ssrbool.elimF eqP) in is_eq.
      simpl.
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

Lemma valid_None_in :
  ∀ {L I E p n},
    ValidPackage L I E p →
    p n = None →
    E n = None.
Proof.
  intros L I E p n hv e.
  epose (valid_domm hv).
  apply /dommPn.
  rewrite (valid_domm hv).
  now move: e => /dommPn.
Qed.

Theorem valid_parable_cons :
  forall (a : raw_package) (P : list raw_package) L I E1 E2,
    fseparate E1 E2 ->
    valid_package L I E1 a ->
    valid_package L I E2 (parallel_raw P) ->
    valid_package L I (unionm E1 E2) (parallel_raw (a :: P)).
Proof.
  intros.
  simpl in *.
  unfold parallel_raw in H0.
  generalize dependent a.

  destruct P.
  {
    intros.
    assert (E2 = emptym).
    {
      apply eq_fmap.
      intros ?.
      rewrite emptymE.
      apply (valid_None_in H1).
      reflexivity.
    }
    rewrite H2.
    rewrite unionm0.
    apply H0.
  }

  simpl.
  generalize dependent r.
  induction P.
  {
    intros.
    rewrite <- (unionmI L).
    rewrite <- (unionmI I).
    simpl.
    by apply valid_par.
  }
  simpl.
  intros.

  rewrite fold_left_to_par.
  rewrite <- par_assoc.
  rewrite <- par_assoc.
  rewrite (par_assoc r).
  rewrite <- fold_left_to_par.

  rewrite <- (unionmI L).
  rewrite <- (unionmI I).
  by apply valid_par.
Qed.

(* idents (f d) :#: idents (interface_hierarchy f d) *)

(* (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f n) :#: idents (f ℓ)), *)

Lemma interface_hierachy_separate :
  forall {B : ordType} {C},
  ∀ (f : _ -> {fmap B -> C}) (a : {fmap B -> C}) n,
    (forall (ℓ : nat) , fseparate (f ℓ) a) ->
     fseparate (interface_hierarchy f n) a.
Proof.
  clear ; intros.
  induction n ; simpl.
  - easy.
  - apply fseparateUl.
    + apply IHn.
    + simpl.
      now apply H.
Qed.

Lemma idents_interface_hierarchy :
  ∀ (f : _ -> Interface) n ℓ,
    (n > ℓ)%nat ->
    (forall (ℓ : nat) , (n > ℓ)%nat -> fseparate (f ℓ) (f n)) ->
     fseparate (interface_hierarchy f ℓ) (f n).
Proof.
  clear ; intros.
  induction ℓ ; simpl.
  - easy.
  - apply fseparateUl.
    + apply IHℓ. Lia.lia.
    + simpl.
      now apply H0.
Qed.

Fixpoint valid_pairs L I E (P : list raw_package) :=
  match L, I, E, P with
  | [], [], [], [] => True
  | [l], [i], [e], [p] => valid_package l i e p
  | (l :: L'), (i :: I'), (e :: E'), (p :: P') => valid_package l i e p /\ valid_pairs L' I' E' P'
  | _, _, _, _ => False
  end.

Fixpoint all_idents_disjoint {A B C} f I :=
  match I with
  | [] | [_] => True
  | (x :: xs) =>
      fseparate (f x) (interface_foreach (A := A) (B := B) (C := C) f xs) /\ all_idents_disjoint f xs
  end.

Lemma interface_foreach_cons : forall {A B C} f n E,
    interface_foreach f (n :: E) = unionm (f n) (interface_foreach (A := A) (B := B) (C := C) f E).
Proof.
  induction E.
  - now rewrite unionm0.
  - reflexivity.
Qed.

Lemma interface_foreach_cat : forall {A B C} f E1 E2,
    interface_foreach f (E1 ++ E2) = unionm (interface_foreach (A := A) (B := B) (C := C) f E1) (interface_foreach (A := A) (B := B) (C := C) f E2).
Proof.
  induction E1; intros.
  - simpl.
    rewrite union0m.
    reflexivity.
  - rewrite interface_foreach_cons.
    rewrite <- List.app_comm_cons.
    rewrite interface_foreach_cons.
    rewrite IHE1.
    rewrite unionmA.
    reflexivity.
Qed.

Lemma interface_foreach_disjoint :
  forall {A} {B : ordType} {C} (f : {fmap B -> C}) (g : A -> {fmap B -> C}) (L : list A),
    (forall m, fseparate f (g m)) ->
    fseparate f (interface_foreach (A := A) (B := B) (C := C) g L).
Proof.
  clear ; intros.
  induction L.
  - simpl.
    apply fseparatem0.
  - rewrite interface_foreach_cons.
    by apply fseparateUr.
Qed.

Lemma foreach_disjoint_foreach :
  (forall {A} {B : ordType} {C} (f g : _ -> {fmap B -> C}) (L : list A),
      (forall n m, fseparate (f n) (g m)) ->
      fseparate (interface_foreach f L) (interface_foreach g L)).
Proof.
  intros.
  induction L.
  - simpl.
    apply fseparatem0.
  - rewrite interface_foreach_cons.
    rewrite interface_foreach_cons.
    apply fseparateUl.
    + apply fseparateUr.
      * apply H.
      * now apply interface_foreach_disjoint.
    + apply fseparateUr.
      * apply fseparateC.
        apply interface_foreach_disjoint.
        intros.
        now apply fseparateC.
      * apply IHL.
Qed.

Lemma interface_foreach_disjoint_same :
  forall {A : eqType} {B : ordType} {C} (f : A -> {fmap B -> C}) (L : list A),
    (forall n m, (n <> m) -> fseparate (f n) (f m)) ->
    forall a, uniq (a :: L) ->
    fseparate (f a) (interface_foreach f L).
Proof.
  clear ; intros.
  induction L.
  - simpl.
    apply fseparatem0.
  - rewrite interface_foreach_cons.
    apply fseparateUr.
    2:{
      apply IHL.
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
    apply H.
    red ; intros.
    subst.
    apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq L) in *.
    rewrite notin_cons in H0.
    apply (ssrbool.elimT andP) in H0 as [].
    now apply (ssrbool.elimN eqP) in H0.
Qed.

Lemma interface_foreach_U : forall {A B C} f g E,
    (forall n m, fseparate (f n) (g m)) ->
    unionm (interface_foreach f E) (interface_foreach g E)
    = interface_foreach (A := A) (B := B) (C := C)(fun n => unionm (f n) (g n)) E.
Proof.
  intros.
  induction E.
  - simpl.
    rewrite unionm0.
    reflexivity.
  - rewrite !interface_foreach_cons.
    rewrite <- unionmA.
    rewrite <- unionmA.
    f_equal.
    rewrite unionmC.
    2:{
      apply fseparateE.
      apply fseparateUr.
      - apply fseparateC.
        apply interface_foreach_disjoint.
        intros.
        apply fseparateC.
        apply H.
      - by apply foreach_disjoint_foreach.
    }
    rewrite <- unionmA.
    f_equal.
    rewrite unionmC.
    2:{
      apply fseparateE.
      apply foreach_disjoint_foreach.
      intros.
      apply fseparateC.
      apply H.
    }
    rewrite IHE.
    reflexivity.
Qed.

Lemma interface_hierarchy_U : forall {B C}, (forall f g ℓ,
    (forall n m, fseparate (f n) (g m)) ->
  (unionm (interface_hierarchy f ℓ) (interface_hierarchy g ℓ))
  = interface_hierarchy (B := B) (C := C) (fun n => unionm (f n) (g n)) ℓ).
Proof.
  intros.
  induction ℓ.
  - reflexivity.
  - simpl.
    rewrite <- IHℓ.
    rewrite unionmA.
    rewrite unionmA.
    f_equal.
    rewrite unionmC.
    2:{
      apply fseparateE.
      apply fseparateUl.
      - apply interface_hierachy_separate => ?.
        apply fseparateC.
        apply interface_hierachy_separate => ?.
        apply fseparateC.
        apply H.
      - apply fseparateC.
        apply interface_hierachy_separate => ?.
        apply fseparateC.
        apply H.
    }
    rewrite unionmA.
    f_equal.
    rewrite unionmC.
    2:{
      apply fseparateE.
      apply interface_hierachy_separate => ?.
      apply fseparateC.
      apply interface_hierachy_separate => ?.
      apply H.
    }
    reflexivity.
Qed.

Lemma interface_hierarchy_foreachU : (forall {A} f g L (d : nat),
  (forall n m i j, fseparate (f n i) (g m j)) ->
  (unionm (interface_hierarchy_foreach f L d) (interface_hierarchy_foreach g L d))
  = interface_hierarchy_foreach (A := A) (fun n d => unionm (f n d) (g n d)) L d).
Proof.
  intros.
  unfold interface_hierarchy_foreach.
  rewrite interface_hierarchy_U.
  2:{
    intros.
    apply foreach_disjoint_foreach.
    intros.
    apply H.
  }
  f_equal.
  setoid_rewrite interface_foreach_U.
  2:{ intros. apply H. }
  reflexivity.
Defined.

(* Lemma foreach_imfset : *)
(*   (forall {A} g f (L : list A), *)
(*       g @: (interface_foreach f L) = interface_foreach (fun n => g @: f n) L). *)
(* Proof. *)
(*   intros. *)
(*   induction L. *)
(*   - simpl. *)
(*     rewrite <- fset0E. *)
(*     rewrite imfset0. *)
(*     reflexivity. *)
(*   - rewrite interface_foreach_cons. *)
(*     rewrite interface_foreach_cons. *)
(*     rewrite !imfsetU. *)
(*     rewrite IHL. *)
(*     reflexivity. *)
(* Qed. *)

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

Lemma interface_foreach_in_rel_cons : forall {A : eqType} {B : ordType} {C} l (a : A) l' H_in f,
    interface_foreach_in_rel l (a :: l') (H_in := H_in) f = unionm (f a (H_in a (mem_head _ _)))(interface_foreach_in_rel (B := B) (C := C) l l' (H_in := fun a H => H_in a (mem_tail _ _ H)) f).
Proof.
  intros.
  induction l'.
  - simpl.
    rewrite unionm0.
    reflexivity.
  - unfold interface_foreach_in_rel ; fold @interface_foreach_in_rel.
    reflexivity.
Qed.

Theorem valid_parable :
  forall {N : eqType} (P : list raw_package) l f g L I E,
    (∀ x y, x ≠ y → fseparate (f x) (f y)) -> uniq E ->
    (∀ x y, x ≠ y → fseparate (g x) (g y)) -> uniq I ->
    (∀ x y, x ≠ y → fseparate (l x) (l y)) -> uniq L ->
    valid_pairs (List.map l L) (List.map g I) (List.map f E) P ->
    valid_package (interface_foreach (A := N) l L) (interface_foreach (A := N) g I) (interface_foreach (A := N) f E) (parallel_raw P).
Proof.
  intros.
  simpl in *.
  generalize dependent L.
  generalize dependent I.
  generalize dependent E.
  induction P, E ; [  | try destruct E ; intros ; destruct L, I ; try contradiction ; destruct L, I ; contradiction .. | ].
  {
    intros.
    simpl.
    apply valid_empty_package.
  }
  intros.
  rewrite interface_foreach_cons.
  (* rewrite <- (unionmI L). *)
  destruct L,I ; [ try destruct L ; contradiction .. | ].
  rewrite interface_foreach_cons.
  rewrite parallel_raw_cons.

  rewrite interface_foreach_cons.
  apply valid_par.
  2:{
    destruct L, I, E , P ; [ | destruct H5 ; try destruct L ; try destruct I ; try destruct E ; contradiction .. | ].
    { apply valid_empty_package. }
    apply IHP ;[ now apply (ssrbool.elimT andP) in H0 as [] | now apply (ssrbool.elimT andP) in H2 as [] | now apply (ssrbool.elimT andP) in H4 as [] | apply H5 ].
  }
  1:{
    simpl in H5.
    destruct (List.map l L), (List.map g I), (List.map f E), P in H5 ; apply H5.
  }
  all: try apply fseparate_compat.
  all: by apply interface_foreach_disjoint_same.
Qed.

  Lemma valid_pairs_cons :
    forall Lx Lxs a b c d e f,
      valid_pairs (Lx :: Lxs) (a :: b) (c :: d) (e :: f) <-> (valid_package Lx a c e /\ valid_pairs Lxs b d f).
  Proof. now intros ? [] ? [] ? [] ? []. Qed.

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

  Lemma valid_pairs_map :
    forall {A : Type} i (f : A -> Interface) (g : forall (a : A), package (i a) (f a)) l,
      (forall a, valid_package (locs (g a)) (i a) (f a) (g a)) ->
      valid_pairs (List.map (fun x => locs (g x)) l) (List.map i l)
        (List.map f l)
        (List.map (fun x => pack (g x)) l).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - rewrite valid_pairs_cons.
      split.
      + apply H.
      + apply IHl.
  Qed.

  (* Lemma valid_pairs_map_with_in_rel : *)
  (*   forall {A : eqType} L l l' H_in i (f : forall (a : A), (a \in l) -> Interface) g, *)
  (*     (forall a (H : a \in l), valid_package (g a H) (i a H) (f a H) (g a H)) -> *)
  (*     valid_pairs _ *)
  (*       (map_with_in_rel l l' (H_in := H_in) i) *)
  (*       (map_with_in_rel l l' (H_in := H_in) f) *)
  (*       (map_with_in_rel l l' (H_in := H_in) g). *)
  (* Proof. *)
  (*   intros. *)
  (*   induction l'. *)
  (*   - reflexivity. *)
  (*   - destruct l' ; [ apply H | ]. *)
  (*     split ; [ apply H | apply IHl' ]. *)
  (* Qed. *)

  (* Lemma valid_pairs_map_with_in_rel_map : *)
  (*   forall {A : eqType} L l l' H_in i (f : forall (a : A), (a \in l) -> Interface) g, *)
  (*     (forall a (H : a \in l), valid_package L (i a) (f a H) (g a H)) -> *)
  (*     valid_pairs L *)
  (*       (List.map i l') *)
  (*       (map_with_in_rel l l' (H_in := H_in) f) *)
  (*       (map_with_in_rel l l' (H_in := H_in) g). *)
  (* Proof. *)
  (*   intros. *)
  (*   induction l'. *)
  (*   - reflexivity. *)
  (*   - destruct l' ; [ apply H | ]. *)
  (*     split ; [ apply H | apply IHl' ]. *)
  (* Qed. *)

  Definition parallel_package
    {A : eqType} (d : nat) {f : A -> _} {g} Names (i : forall (a : A), package (f a) (g a))
    (H : ∀ x y : A, x ≠ y → fseparate (g x) (g y))
    (Hf : ∀ x y : A, x ≠ y → fseparate (f x) (f y))
    (Hl : ∀ x y : A, x ≠ y → fseparate (locs (i x)) (locs (i y)))
    (H3 : uniq Names) :
    package
      (interface_foreach f Names)
      (interface_foreach g Names).
    refine ({package _ #with (parallel_raw _)
             } _).
    refine (valid_parable _ _ _ _ _ _ _ H H3 Hf H3 Hl H3 (valid_pairs_map _ _ _ _ (fun m => pack_valid (i m)))).
  Qed.

  Lemma in_remove_middle :
    forall {A : eqType} {x a b} {l : list A},
      x \in a :: l ->
            x \in a :: b :: l.
  Proof. now intros ; rewrite !in_cons in H |- *. Defined.

  Lemma idents_foreach_disjoint_foreach_different :
    (forall {A} {B : ordType} {C} f g (Lf Lg : list A),
        (forall n m, fseparate (f n) (g m)) ->
        fseparate
          (interface_foreach (A := A) (B := B) (C := C) f Lf)
          (interface_foreach (A := A) (B := B) (C := C) g Lg)).
  Proof.
    intros.
    apply interface_foreach_disjoint ; intros.
    apply fseparateC.
    apply interface_foreach_disjoint ; intros.
    apply fseparateC.
    apply H.
  Qed.

  Lemma interface_foreach_in_rel_disjoint_same :
    forall {A : eqType} {B : ordType} {C} (L L' : list A) (f : forall a : A, a \in L -> {fmap B -> C}),
      (forall n m, (n <> m) -> forall (H_n_in_L : n \in L) (H_m_in_L : m \in L), fseparate (f n H_n_in_L) (f m H_m_in_L)) ->
      forall (H_in : forall a : A, a \in L' -> a \in L),
      forall a, uniq (a :: L') ->
      forall H_a_in_L : a \in L,
       fseparate (f a H_a_in_L) (interface_foreach_in_rel (H_in := H_in) L L' f).
  Proof.
    clear ; intros.
    induction L'.
    - simpl.
      apply fseparatem0.
    - rewrite interface_foreach_in_rel_cons.
      apply fseparateUr.
      2:{
        apply IHL'.
        rewrite cons_uniq.
        rewrite cons_uniq in H0.
        move: H0 => /andP [H0].
        rewrite notin_cons in H0.
        move: H0 => /andP [? ? H0].
        rewrite cons_uniq in H0.
        now move: H0 => /andP.
      }
      apply H.
      red ; intros.
      subst.
      apply (ssrbool.elimT andP) in H0 as [] ; fold (uniq L) in *.
      rewrite notin_cons in H0.
      apply (ssrbool.elimT andP) in H0 as [].
      now apply (ssrbool.elimN eqP) in H0.
  Qed.

  Theorem valid_parable_map_with_in_rel :
    forall {N : eqType} (P : list raw_package) L I E2 E1 H_in l f g,
      (∀ (x y : N) Hx Hy, x ≠ y → fseparate (f x Hx) (f y Hy)) -> uniq E1 ->
      (* trimmed_pairs (map_with_in_rel E2 E1 (H_in := H_in) f) P -> *)
      valid_pairs (List.map l L) (List.map g I) (map_with_in_rel E2 E1 (H_in := H_in) f) P ->
      (∀ x y, x ≠ y → fseparate (g x) (g y)) -> uniq I ->
      (∀ x y, x ≠ y → fseparate (l x) (l y)) -> uniq L ->
      valid_package (interface_foreach (A := N) l L) (interface_foreach (A := N) g I) (interface_foreach_in_rel E2 E1 (H_in := H_in) f) (parallel_raw P).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? H_sep_g H_uniq_I.
    simpl in *.
    generalize dependent L.
    generalize dependent I.
    generalize dependent E1.
    induction P, E1 ; [  | destruct L, I ; try contradiction ; destruct L, I ; try destruct E2, E1 ; contradiction .. | ].
    {
      intros.
      apply valid_empty_package.
    }
    {
      intros.
      rewrite interface_foreach_in_rel_cons.
      (* unfold interface_foreach_in_rel ; fold @interface_foreach_in_rel. *)
      (* rewrite map_with_in_rel_eta. *)
      (* rewrite interface_foreach_cons. *)
      (* rewrite <- (unionmI L). *)
      destruct L, I ; [ try destruct L ; contradiction .. | ].
      rewrite interface_foreach_cons.
      rewrite interface_foreach_cons.
      rewrite parallel_raw_cons.

      apply valid_par.
      2:{
        move: H0; rewrite cons_uniq => /andP [ _ H0 ] ; intros.
        apply (IHP _ _ H0).
        - rewrite cons_uniq in H_uniq_I.
          now move: H_uniq_I => /andP.
        - now rewrite valid_pairs_cons in H1.
        - apply H2.
        - rewrite cons_uniq in H3.
          now move: H3 => /andP.
      }
      1:{
        simpl in H1.
        destruct  (List.map l L), (List.map g I), (map_with_in_rel E2 E1 f), P in H1 ; apply H1.
      }
      all: try apply fseparate_compat.
      2-3: try by apply interface_foreach_disjoint_same.
      now apply interface_foreach_in_rel_disjoint_same.
    }
  Qed.

  (* Definition parallel_package_with_in_rel *)
  (*   {A : eqType} (d : nat) {L} Names {f : A -> _} {g : forall (a : A), (a \in Names) -> _} (i : forall (a : A) (H : a \in Names), package L (f a) (g a H)) *)
  (*   (H : ∀ (x y : A) Hx Hy, x ≠ y → fseparate (g x Hx) (g y Hy)) *)
  (*   (Hf : ∀ (x y : A), x ≠ y → fseparate (f x) (f y)) *)
  (*   (* (H1 : ∀ (a : A) (H : a \in Names), trimmed (g a H) (i a H)) *) *)
  (*   (H3 : uniq Names) : *)
  (*   package L *)
  (*     (interface_foreach f Names) *)
  (*     (interface_foreach_in_rel Names Names (H_in := fun a H => H) g). *)
  (*   refine ({package *)
  (*      parallel_raw _ #with *)
  (*     valid_parable_map_with_in_rel *)
  (*     _ _ _ _ _ _ *)
  (*     _ *)
  (*     _ *)
  (*     _ *)
  (*     _ *)
  (*     (trimmed_pairs_map_with_in_rel _ _ _ _ _ _) *)
  (*     (valid_pairs_map_with_in_rel_map _ _ _ _ _ _ _ _) *)
  (*     _ *)
  (*     _}). *)
  (*   - apply H. *)
  (*   - apply H3. *)
  (*   - apply H1. *)
  (*   - intros. *)
  (*     apply i. *)
  (*   - apply Hf. *)
  (*   - apply H3. *)
  (* Defined. *)

(* Lemma all_idents_disjoint_foreach : *)
(*   (forall {A : eqType} f (L : list A), *)
(*       (forall x y, x <> y -> fseparate (f x) (f y)) -> *)
(*       uniq L -> *)
(*       all_idents_disjoint f L). *)
(* Proof. *)
(*   intros. *)
(*   induction L ; [ easy | ]. *)
(*   destruct L ; [ easy | ]. *)
(*   split ; [ | apply IHL ]. *)
(*   2: apply (ssrbool.elimT andP) in H0 as [] ; apply H1. *)
(*   apply interface_foreach_disjoint_same. *)
(*   2: easy. *)
(*   apply H. *)
(* Qed. *)

(* Theorem valid_forall : forall {A : eqType} {L} g f u Names (d ℓ : nat), *)
(*     (d >= ℓ)%nat -> *)
(*     (∀ x y : A, x ≠ y → fseparate (f x) (f y)) -> uniq Names -> *)
(*     (∀ x y : A, x ≠ y → fseparate (g x) (g y)) ->  *)
(*     trimmed_pairs (List.map f Names) (List.map (u ℓ) Names) -> *)
(*     (valid_pairs L (List.map g Names) (List.map f Names) *)
(*     (List.map (u ℓ) Names)) -> *)
(*   ValidPackage L *)
(*     (interface_foreach g Names) *)
(*     (interface_foreach (A := A) f Names) *)
(*     (parallel_raw (List.map (u ℓ) Names)). *)
(* Proof. *)
(*   intros. *)
(*   eapply valid_package_inject_import. *)
(*   - instantiate (1 := interface_foreach g Names). *)

(*     unfold interface_hierarchy_foreach. *)
(*     unfold interface_hierarchy ; fold interface_hierarchy. *)

(*     induction d. *)
(*     + (* simpl. *) *)
(*       (* destruct ℓ ; [ | discriminate ]. *) *)
(*       apply fsubmapxx. *)
(*     + apply fsubmapxx. *)
(*       (* apply fsubsetU. fold interface_hierarchy. *) *)
(*       (* apply /orP. *) *)
(*       (* destruct (ℓ == d.+1) eqn:is_eq. *) *)
(*       (* * apply (ssrbool.elimT eqP) in is_eq. *) *)
(*       (*   subst. *) *)
(*       (*   right. *) *)
(*       (*   apply fsubsetxx. *) *)
(*       (* * apply (ssrbool.elimF eqP) in is_eq. *) *)
(*       (*   left. *) *)
(*       (*   apply IHd. *) *)
(*       (*   Lia.lia. *) *)
(*   - now apply valid_parable. *)
    
(*     (* + apply H0. *) *)
(*     (* + apply H1. *) *)
(*     (* + apply H2. *) *)
(*     (* + apply H3. *) *)
(* Qed. *)


(* Theorem valid_forall_map_with_in : forall {A : eqType} {L} g f Names u (d ℓ : nat), *)
(*     (d >= ℓ)%nat -> *)
(*     (∀ x y : A, x ≠ y → fseparate (f x) (f y)) -> uniq Names -> *)
(*     (∀ x y : A, forall i j, (i < j)%nat → fseparate (g^~ i x) (g^~ j y)) -> *)
(*     (∀ x y : A, x <> y -> fseparate (g^~ ℓ x) (g^~ ℓ y)) -> *)
(*     trimmed_pairs (List.map f Names) (map_with_in Names (u ℓ)) -> *)
(*     (valid_pairs L (List.map (g^~ ℓ) Names) (List.map f Names) *)
(*     (map_with_in Names (u ℓ))) -> *)
(*   ValidPackage L *)
(*     (interface_hierarchy_foreach g Names d) *)
(*     (interface_foreach (A := A) f Names) (parallel_raw (map_with_in Names (u ℓ))). *)
(* Proof. *)
(*   intros. *)
(*   eapply valid_package_inject_import. *)
(*   - instantiate (1 := interface_foreach (g^~ ℓ) Names). *)

(*     unfold interface_hierarchy_foreach. *)
(*     unfold interface_hierarchy ; fold interface_hierarchy. *)

(*     induction d. *)
(*     + simpl. *)
(*       destruct ℓ ; [ | discriminate ]. *)
(*       apply fsubmapxx. *)
(*     + destruct (ℓ == d.+1) eqn:is_eq. *)
(*       * apply (ssrbool.elimT eqP) in is_eq. *)
(*         subst. *)
(*         simpl. *)
(*         apply fsubmapUr. *)
(*         apply fseparate_compat. *)
(*         apply (@idents_interface_hierachy (fun n => interface_foreach (g^~ n) Names) d.+1 d H). *)
(*         intros. *)
(*         apply foreach_disjoint_foreach. *)
(*         intros. *)
(*         by apply H2. *)
        
(*       * apply (ssrbool.elimF eqP) in is_eq. *)
(*         simpl. *)
(*         apply fsubmapUl_trans. *)
(*         apply IHd. *)
(*         Lia.lia. *)
(*   - by apply valid_parable. *)
(* Qed. *)

(* Theorem valid_forall_map_with_in_rel : forall {A : eqType} {L} Names l (d : nat) {g f} ℓ (H_le : (ℓ <= d)%nat) (u : forall a (H : a \in Names), raw_package) H_in, *)
(*     (∀ (x y : A), x ≠ y → fseparate (f x) (f y)) -> uniq l -> *)
(*     (∀ x y : A, x ≠ y → fseparate (g x) (g y)) -> *)
(*     (trimmed_pairs (List.map f l) (map_with_in_rel Names l (H_in := H_in) u)) -> *)
(*     (valid_pairs L (List.map g l) (List.map (f) l) *)
(*                  (map_with_in_rel Names l (H_in := H_in) u)) -> *)
(*   ValidPackage L *)
(*     (interface_foreach g l) *)
(*     (interface_foreach f l) *)
(*     (parallel_raw (map_with_in_rel Names l (H_in := H_in) u)). *)
(* Proof. *)
(*   intros. *)
(*   eapply valid_package_inject_import. *)
(*   - instantiate (1 := interface_foreach g l). *)

(*     unfold interface_hierarchy_foreach. *)
(*     unfold interface_hierarchy ; fold interface_hierarchy. *)

(*     induction d. *)
(*     + simpl. *)
(*       (* destruct ℓ ; [ | discriminate ]. *) *)
(*       apply fsubmapxx. *)
(*     + (* apply fsubsetU. fold interface_hierarchy. *) *)
(*       (* apply /orP. *) *)
(*       (* right. *) *)
(*       apply fsubmapxx. *)
(*   - by apply valid_parable. *)
(* Qed. *)

(* Lemma forall_valid_from_packages : *)
(*   forall {A : eqType} {L} {g f} Names l (ℓ : nat) (u : forall a (H : a \in Names), package L (g a ℓ) (f a)) H_in, *)
(*   valid_pairs L (List.map (g^~ ℓ) l) (List.map f l) *)
(*     (map_with_in_rel Names l (H_in := H_in) (λ (a : A) (H3 : (a \in Names) = true), pack (u a H3))). *)
(* Proof. *)
(*   intros. *)
(*   induction l. *)
(*   - reflexivity. *)
(*   - rewrite !map_eta. *)
(*     rewrite map_with_in_rel_eta. *)
(*     rewrite valid_pairs_cons. *)
(*     split. *)
(*     + apply u. *)
(*     + apply IHl. *)
(* Qed. *)

(* Theorem map_with_in_num_upper_trimmed : *)
(*   forall (* {L I} *) *)
(*     (d : nat) *)
(*     {f : nat -> Interface} *)
(*     (p : forall (ℓ : nat) , (ℓ <= d)%N → raw_package (* L I (f ℓ) *)) *)
(*     (H_trim_p : forall ℓ (H_le : (ℓ <= d)%N), trimmed (f ℓ) (p ℓ H_le)) *)
(*     (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> fseparate (f ℓ) (f n)), *)
(*     forall k (K_le : (k <= d)%nat), *)
(*     trimmed (interface_hierarchy f k) (map_with_in_num_upper d k (H_le := K_le) p). *)
(* Proof. *)
(*   intros. *)
(*   induction k ; intros. *)
(*   - simpl. *)
(*     (* destruct k ; [ | discriminate ]. *) *)
(*     apply H_trim_p. *)
(*   - unfold ℓ_raw_packages. *)
(*     unfold interface_hierarchy ; fold interface_hierarchy. *)

(*     apply trimmed_par. *)
(*     { *)
(*       apply (idents_interface_hierachy). *)
(*       - Lia.lia. *)
(*       - intros. *)
(*         now apply Hdisj. *)
(*     } *)
(*     { *)
(*       apply IHk ; auto. *)
(*     } *)
(*     { *)
(*       apply H_trim_p. *)
(*     } *)
(* Qed. *)

  Lemma idents_interface_hierarchy_in_num_upper :
    forall {B : ordType} {C},
  ∀ n ℓ d (f : forall ℓ : nat, (ℓ <= n)%nat -> {fmap B -> C}),
  forall (H_n_lt_d : (d <= n)%nat),
  forall (H_ℓ_lt_n : (ℓ <= n)%nat),
    (forall (ℓ : nat), forall (H_lt : (n >= ℓ)%nat),fseparate (f ℓ H_lt) (f d H_n_lt_d)) ->
     fseparate (interface_hierarchy_in_num_upper n ℓ H_ℓ_lt_n (fun x y => f x y)) (f d H_n_lt_d).
Proof.
  clear ; intros.
  induction ℓ ; simpl.
  - easy.
  - apply fseparateUl.
    + apply IHℓ.
    + apply H.
Qed.

Definition ℓ_packages 
  (d : nat)
  {g : nat -> Interface}
  {f : nat -> Interface}
  (p : forall (n : nat), (d >= n)%nat → package (g n) (f n))
  (* (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge)) *)
  (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> fseparate (f ℓ) (f n))
  (Hdisj_g : ∀ n ℓ : nat, (ℓ < n)%N → fseparate (g ℓ) (g n))
  (Hdisj_p : ∀ (n ℓ : nat) (H_le_d : (ℓ <= d)%N) (H_n_le_d : (n <= d)%N), fseparate (locs (p ℓ H_le_d)) (locs (p n H_n_le_d)))
  : package (interface_hierarchy g d) (interface_hierarchy f d).
Proof.
  refine ({package (interface_hierarchy_in_num_upper d d (leqnn d) (fun n x => locs (p n x))) #with ℓ_raw_packages d p} _).

  unfold ℓ_raw_packages.
  set (leqnn d).
  set d in i at 2 |- * at 2 4 5 7.
  generalize dependent i.
  generalize dependent n.
  induction n ; intros.
  - simpl.
    apply p.
  - simpl.
    (* rewrite <- (unionmI L). *)
    (* rewrite <- (fsetUid I). *)

    apply valid_par.
    + fold map_with_in_num_upper.
      apply IHn.
    + apply p.
    (* + (* epose ℓ_raw_level_Parable. *) *)
    (*   (* rewrite <- H_trim_p. *) *)
    (*   rewrite <- map_with_in_num_upper_trimmed. *)
    (*   2:{ *)
    (*     intros. *)
    (*     apply H_trim_p. *)
    (*   } *)
    (*   2:{ *)
    (*     intros. *)
    (*     apply Hdisj. *)
    (*     - apply H. *)
    (*     - Lia.lia. *)
    (*   } *)
    (*   (* solve_Parable. *) *)
    (*   apply parable_trim. *)

    (*   apply idents_interface_hierachy. *)
    (*   2: intros ; now apply Hdisj. *)
    (*   Lia.lia. *)
    + by apply idents_interface_hierarchy ; [ |  by intros ; apply Hdisj ].
    + apply fseparate_compat.
      (* apply idents_interface_hierarchy_in_num_upper. *)
      epose (idents_interface_hierarchy_in_num_upper d n n.+1 (λ (n0 : nat) (x : (n0 <= d)%N), locs (p n0 x)) _ (leq_trans (n:=n.+1) (m:=n) (p:=d) (leqnSn n) i)).
      hnf in f0.
      apply f0.
      intros.
      apply Hdisj_p.
    + {
        apply fseparate_compat.
        apply idents_interface_hierarchy.
        2:{
          intros.
          apply Hdisj_g.
          assumption.
        }
        easy.
      }
Defined.

(* Lemma interface_foreach_trivial : forall {A} i L (* d *), *)
(*     L <> [] -> *)
(*     i = (interface_foreach (λ (n : A), i) L ). *)
(* Proof. *)
(*   intros. *)
(*   destruct L ; [ easy | ]. *)
(*   clear H. *)
(*   generalize dependent a. *)
(*   induction L ; intros. *)
(*   { *)
(*     rewrite interface_foreach_cons. *)
(*     simpl. *)
(*     now rewrite unionm0. *)
(*   } *)
(*   { *)
(*     rewrite interface_foreach_cons. *)
(*     rewrite <- IHL. *)
(*     now rewrite unionmI. *)
(*   } *)
(* Qed. *)

(* Lemma interface_hierarchy_empty : forall d, *)
(*     (interface_hierarchy (λ (n : nat), [interface]) d ) = [interface]. *)
(* Proof. *)
(*   intros. *)
(*   induction d. *)
(*   - reflexivity. *)
(*   - simpl. rewrite unionm0. rewrite IHd. reflexivity. *)
(* Qed. *)

(* Lemma interface_hierarchy_trivial : forall i d, *)
(*     i = (interface_hierarchy (λ (_ : nat), i) d ). *)
(* Proof. *)
(*   intros. *)
(*   induction d. *)
(*   { *)
(*     reflexivity. *)
(*   } *)
(*   { *)
(*     simpl. *)
(*     rewrite <- IHd. *)
(*     now rewrite unionmI. *)
(*   } *)
(* Defined. *)

(* Lemma interface_hierarchy_foreach_trivial : forall {A} i L d, *)
(*     L <> [] -> *)
(*     i = (interface_hierarchy_foreach (λ (_ : A) (_ : nat), i) L d ). *)
(* Proof. *)
(*   intros. *)
(*   unfold interface_hierarchy_foreach. *)
(*   rewrite <- interface_hierarchy_trivial. *)
(*   now apply interface_foreach_trivial. *)
(* Defined. *)

(* Definition combined (A : eqType) (d : nat) L (f : A -> _) g Names (i : forall (n : nat), (n <= d)%nat -> forall (a : A), package L (f a) (g a n)) *)
(*     (H : forall n, (n <= d)%nat -> ∀ x y : A, x ≠ y → fseparate (g x n) (g y n)) *)
(*     (H0 : forall n ℓ, (ℓ < n)%nat -> (n <= d)%nat -> ∀ x y : A, fseparate (g x ℓ) (g y n)) *)
(*     (Hf : forall x y : A, x ≠ y → fseparate (f x) (f y)) *)
(*     (H1 : forall n (H_le : (n <= d)%nat), ∀ a : A, trimmed (g a n) (i n H_le a)) *)
(*     (H3 : uniq Names) : *)
(*   package L *)
(*     (interface_foreach f Names) *)
(*     (interface_hierarchy_foreach g Names d). *)
(* Proof. *)
(*   rewrite (interface_hierarchy_trivial (interface_foreach f (Names)) d). *)
(*   refine (ℓ_packages *)
(*            d *)
(*            (fun n H_le => *)
(*               parallel_package d (Names) (i n H_le) (H n H_le) (Hf) (H1 n H_le) H3 *)
(*            ) *)
(*            (fun n H_le => *)
(*               trimmed_parallel_raw *)
(*                 (H n H_le) *)
(*                 H3 *)
(*                 (trimmed_pairs_map _ _ _ (H1 n H_le))) *)
(*            (fun n ℓ i0 i1 => foreach_disjoint_foreach _ _ (Names) (H0 n ℓ i0 i1)) *)
(*            (fun n ℓ => _) *)
(*         ). *)
(*   intros. *)
(* Defined. *)

(* Definition parallel_package_with_in_rel_hierarchy {A : eqType} {L} {g f} Names l  (d : nat) (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names), package L (g a ℓ) (f a ℓ)) H_in : *)
(*   (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) -> *)
(*   uniq l -> *)
(*   (forall ℓ H_le, trimmed_pairs (List.map (f^~ℓ) l) (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) -> *)
(*   forall ℓ H_le, *)
(*   package L (interface_foreach (g^~ ℓ) l) (interface_foreach (f^~ ℓ) l) := *)
(*   (fun H H0 H1 ℓ H_le => *)
(*      {package (parallel_raw (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) *)
(*             #with *)
(*            valid_forall_map_with_in_rel *)
(*            (f := (f^~ℓ)) *)
(*            Names l d _ H_le (u _ _) H_in (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq)) H0 (H1 _ _) *)
(*            (forall_valid_from_packages Names l _ (u ℓ H_le) H_in)}). *)

(* Definition ℓ_parallel {A : eqType} {L} {g f} Names l  (d : nat) (u : forall ℓ (H_le : (ℓ <= d)%nat) a (H : a \in Names), package L (g a ℓ) (f a ℓ)) H_in : *)
(*   (∀ ℓ n, ∀ x y : A, (x ≠ y \/ ℓ ≠ n) → idents (f x ℓ) :#: idents (f y n)) -> *)
(*   uniq l -> *)
(*   (forall ℓ H_le, trimmed_pairs (List.map (f^~ℓ) l) (map_with_in_rel Names l (H_in := H_in) (fun a H => pack (u ℓ H_le a H)))) -> *)
(*   package L *)
(*     (interface_hierarchy_foreach g l d) *)
(*     (interface_hierarchy_foreach f l d) := *)
(*   (fun H H0 H1 => *)
(*      ℓ_packages d *)
(*        (λ ℓ H_le, parallel_package_with_in_rel_hierarchy Names l d u H_in H H0 H1 ℓ H_le) *)
(*        (fun a H_le => trimmed_parallel_raw (fun _ _ H_neq => H _ _ _ _ (or_introl H_neq)) H0 (H1 _ _)) *)
(*        (fun n ℓ H_le H_ge => *)
(*           idents_foreach_disjoint_foreach _ _ _ *)
(*             (fun _ _ => *)
(*                H _ _ _ _ *)
(*                  (or_intror *)
(*                     ((eq_ind_r *)
(*                         (λ ℓ0 : nat, (ℓ0 < n)%N → False) *)
(*                         (λ H_le0 : (n < n)%N, *)
(*                             (eq_ind_r (λ b : bool, b → False) (λ H_le1 : false, False_ind False (eq_ind false (λ e : bool, if e then False else True) I true H_le1)) (ltnn n)) H_le0) (y:=ℓ))^~ H_le) *)
(*          )))). *)

(* Definition trimmed_ℓ_packages {L} *)
(*   (d : nat) *)
(*   {g : nat -> Interface} *)
(*   {f : nat -> Interface} *)
(*   (p : forall (n : nat), (d >= n)%nat → package L (g n) (f n)) *)
(*   (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f n) (p n H_ge)) *)
(*   (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f ℓ) :#: idents (f n)) *)
(*   : trimmed (interface_hierarchy f d) (ℓ_packages d p H_trim_p Hdisj). *)
(* Proof. *)
(*   induction d ; intros. *)
(*   - apply H_trim_p. *)
(*   - simpl. *)
(*     apply trimmed_par. *)
(*     2:{ *)
(*       apply map_with_in_num_upper_trimmed. *)
(*       - intros ; apply H_trim_p. *)
(*       - now intros ; apply Hdisj. *)
(*     } *)
(*     2:{ *)
(*       apply H_trim_p. *)
(*     } *)
(*     now apply idents_interface_hierachy. *)
(* Qed. *)

(* Lemma idents_interface_hierachy3 : *)
(*   forall g f d, *)
(*     (forall x, (x <= d)%nat -> idents g :#: idents (f x)) -> *)
(*     idents g :#: idents (interface_hierarchy f d). *)
(* Proof. *)
(*   clear ; intros. *)
(*   unfold idents. *)
(*   induction d ; simpl. *)
(*   - apply H. *)
(*     reflexivity. *)
(*   - rewrite imfsetU. *)
(*     rewrite fdisjointUr. *)
(*     rewrite IHd. *)
(*     + apply H. *)
(*       easy. *)
(*     + intros. apply H. *)
(*       Lia.lia. *)
(* Qed. *)


(* (*** Ltac Tactics *) *)

(*   Lemma idents_disjoint_foreach_in : *)
(*     (forall {A: eqType} f g (L : list A), *)
(*         (forall m, (m \in L) -> idents f :#: idents (g m)) -> *)
(*         idents f :#: idents (interface_foreach g L)). *)
(*   Proof. *)
(*     intros. *)
(*     induction L. *)
(*     + simpl. *)
(*       rewrite <- fset0E. *)
(*       unfold idents. *)
(*       rewrite imfset0. *)
(*       apply fdisjoints0. *)
(*     + rewrite interface_foreach_cons. *)
(*       unfold idents. *)
(*       rewrite !imfsetU. *)
(*       rewrite fdisjointUr. *)
(*       rewrite IHL ; clear IHL. *)
(*       * rewrite Bool.andb_true_r. *)
(*         apply H. *)
(*         apply mem_head. *)
(*       * intros. *)
(*         apply H. *)
(*         rewrite in_cons. *)
(*         apply /orP. *)
(*         now right. *)
(*   Qed. *)

(*   Definition idents_foreach_disjoint_foreach_in : *)
(*     forall x y k index T1 T2 (Lf Lg : list name), *)
(*       (forall x, x \in Lf -> x \notin Lg) -> *)
(*       idents (interface_foreach (fun a => fset [(serialize_name a x k index, T1)]) Lf) *)
(*         :#: idents (interface_foreach (fun a => fset [(serialize_name a y k index, T2)]) Lg). *)
(*   Proof. *)
(*     clear ; intros. *)
(*     rewrite fdisjointC. *)
(*     apply idents_disjoint_foreach_in. *)
(*     intros. *)
(*     rewrite fdisjointC. *)
(*     apply idents_disjoint_foreach_in. *)
(*     intros. *)
(*     unfold idents. *)
(*     solve_imfset_disjoint. *)
(*     apply serialize_name_notin_all. *)
(*     left ; split ; [ reflexivity | right ]. *)
(*     red ; intros ; subst. *)
(*     specialize (H m H0). *)
(*     now rewrite H1 in H. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_shift : *)
(*     forall d k {index p} L, *)
(*     interface_hierarchy_foreach (fun n ℓ => (fset [(serialize_name n ℓ k index, p)])) L d.+1 = *)
(*       interface_foreach (fun n => fset [(serialize_name n O k index, p)]) L *)
(*         :|: interface_hierarchy_foreach (fun n ℓ => fset [(serialize_name n (ℓ.+1) k index,p ) ]) L d *)
(*   . *)
(*   Proof. *)
(*     intros. *)
(*     induction d. *)
(*     - simpl. reflexivity. *)
(*     - unfold interface_hierarchy_foreach at 2. *)
(*       unfold interface_hierarchy ; fold interface_hierarchy. *)
(*       fold (interface_hierarchy_foreach (λ n ℓ, fset [(serialize_name n ℓ.+1 k index, p)]) L). *)
(*       rewrite fsetUA. *)
(*       rewrite fsetUC. *)
(*       rewrite <- IHd. *)
(*       rewrite fsetUC. *)
(*       reflexivity. *)
(*   Qed. *)

(*   Lemma subset_pair : forall {A : ordType} (x : {fset A}) y Lx Ly, *)
(*       x :<=: y -> *)
(*       Lx :<=: Ly -> *)
(*       x :|: Lx :<=: y :|: Ly. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite fsubUset ; apply /andP ; split. *)
(*     * rewrite fsubsetU ; [ easy | ]. *)
(*       apply /orP ; left. *)
(*       apply H. *)
(*     * rewrite fsubsetU ; [ easy | ]. *)
(*       apply /orP ; right. *)
(*       apply H0. *)
(*   Qed. *)

(*   Lemma interface_foreach_subset_pairs : forall {A: eqType} f g (L : seq A), *)
(*       (forall (x : A), (x \in L) -> f x :<=: g x) -> *)
(*       interface_foreach f L :<=: interface_foreach g L. *)
(*   Proof. *)
(*     intros. *)
(*     induction L. *)
(*     + apply fsubsetxx. *)
(*     + rewrite !interface_foreach_cons. *)
(*       apply subset_pair. *)
(*       * apply H. *)
(*         apply mem_head. *)
(*       * apply IHL. *)
(*         intros. *)
(*         apply H. *)
(*         rewrite in_cons. *)
(*         now apply /orP ; right. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_subset_pairs : forall f g d, *)
(*       (forall ℓ, (ℓ <= d)%nat -> f ℓ :<=: g ℓ) -> *)
(*       interface_hierarchy f d :<=: interface_hierarchy g d. *)
(*   Proof. *)
(*     intros. *)
(*     induction d. *)
(*     + now apply H. *)
(*     + simpl. *)
(*       apply subset_pair. *)
(*       * apply IHd. *)
(*         now intros ; apply H. *)
(*       * now apply H. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_subset_pairs : forall {A: eqType} f g (L : seq A) d, *)
(*       (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: g x ℓ) -> *)
(*       interface_hierarchy_foreach f L d :<=: interface_hierarchy_foreach (A := A) g L d. *)
(*   Proof. *)
(*     intros. *)
(*     unfold interface_hierarchy_foreach. *)
(*     apply interface_hierarchy_subset_pairs. *)
(*     intros. *)
(*     now apply interface_foreach_subset_pairs. *)
(*   Qed. *)

(*   Lemma interface_foreach_subset : forall {A: eqType} f (L : seq A) K, *)
(*       (forall (x : A), (x \in L) -> f x :<=: K) -> *)
(*       interface_foreach f L :<=: K. *)
(*   Proof. *)
(*     intros. *)
(*     induction L. *)
(*     + simpl. rewrite <- fset0E. apply fsub0set. *)
(*     + rewrite interface_foreach_cons. *)
(*       rewrite fsubUset. *)
(*       apply /andP ; split. *)
(*       * apply H. *)
(*         apply mem_head. *)
(*       * apply IHL. *)
(*         intros. *)
(*         apply H. *)
(*         rewrite in_cons. *)
(*         now apply /orP ; right. *)
(*   Qed. *)

(*   Lemma interface_foreach_subsetR : forall {A: eqType} f (L : seq A) K, *)
(*       (exists (x : A) (H_in : x \in L), K :<=: f x) -> *)
(*       L <> [] -> *)
(*       K :<=: interface_foreach f L. *)
(*   Proof. *)
(*     intros. *)
(*     induction L ; [ easy | ]. *)
(*       unfold interface_hierarchy. *)
(*       rewrite interface_foreach_cons. *)
(*       rewrite fsubsetU ; [ easy | ]. *)
(*       apply /orP. *)

(*       destruct H as [? []]. *)
(*       rewrite in_cons in x0. *)
(*       move: x0 => /orP [/eqP ? | x0 ] ; subst. *)
(*       + now left. *)
(*       + right. *)
(*         apply IHL. *)
(*         2: destruct L ; easy. *)
(*         exists x, x0. *)
(*         apply H. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_subset : forall {A: eqType} f (L : seq A) d K, *)
(*       (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: K) -> *)
(*       interface_hierarchy_foreach f L d :<=: K. *)
(*   Proof. *)
(*     intros. *)
(*     unfold interface_hierarchy_foreach. *)
(*     induction d in H |- * at 1. *)
(*     - now apply interface_foreach_subset. *)
(*     - simpl. *)
(*       rewrite fsubUset. *)
(*       apply /andP ; split. *)
(*       + now apply IHn. *)
(*       + now apply interface_foreach_subset. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_subsetR : forall {A: eqType} f (L : seq A) d K, *)
(*       (exists (x : A) (H_in : x \in L) ℓ (H_le : (ℓ <= d)%nat), K :<=: f x ℓ) -> *)
(*       L <> [] -> *)
(*       K :<=: interface_hierarchy_foreach f L d. *)
(*   Proof. *)
(*     intros. *)
(*     unfold interface_hierarchy_foreach. *)
(*     induction d in H |- * at 1. *)
(*     - destruct H as [? [? [? []]]]. *)
(*       apply interface_foreach_subsetR. *)
(*       2: easy. *)
(*       exists x, x0. *)
(*       destruct x1 ; [ | easy ]. *)
(*       apply H. *)
(*     - simpl. *)
(*       rewrite fsubsetU ; [ easy | ]. *)
(*       apply /orP. *)

(*       destruct H as [? [? [? []]]]. *)
(*       destruct (x1 == n.+1) eqn:x_eq ; move: x_eq => /eqP x_eq ; subst. *)
(*       + right. *)
(*         clear IHn. *)
(*         apply interface_foreach_subsetR. *)
(*         2: easy. *)
(*         exists x, x0. *)
(*         apply H. *)
(*       + left. *)
(*         apply IHn. *)
(*         exists x, x0, x1. *)
(*         eexists ; [ Lia.lia | ]. *)
(*         apply H. *)
(*   Qed. *)

(*   Lemma idents_interface_hierachy2 : *)
(*     forall g f d, *)
(*       (forall x, idents g :#: idents (f x)) -> *)
(*       idents g :#: idents (interface_hierarchy f d). *)
(*   Proof. *)
(*     clear ; intros. *)
(*     unfold idents. *)
(*     induction d ; simpl. *)
(*     - apply H. *)
(*     - rewrite imfsetU. *)
(*       rewrite fdisjointUr. *)
(*       rewrite IHd. *)
(*       apply H. *)
(*   Qed. *)

(*   Definition parallel_ID d (L : seq name) (f : name -> Interface) : *)
(*     (∀ x y, x ≠ y → idents (f x) :#: idents (f y)) -> *)
(*     (uniq L) -> *)
(*     (forall x, flat (f x)) -> *)
(*     package fset0 (interface_foreach f L) (interface_foreach f L) := *)
(*     fun H H0 H1 => *)
(*       parallel_package d L *)
(*         (fun x => {package ID (f x) #with valid_ID _ _ (H1 x)}) H *)
(*         (fun x => trimmed_ID _) H0. *)

(*   Definition combined_ID (d : nat) (L : seq name) (f : name -> nat -> Interface) : *)
(*     (forall n x y, x ≠ y → idents (f x n) :#: idents (f y n)) -> *)
(*     (uniq L) -> *)
(*     (forall n x, flat (f x n)) -> *)
(*     (forall n ℓ, (ℓ < n)%nat -> (n <= d)%nat -> ∀ x y, idents (f x ℓ) :#: idents (f y n)) -> *)
(*     package fset0 (interface_hierarchy_foreach f L d) (interface_hierarchy_foreach f L d). *)

(*     intros. *)
(*     refine (ℓ_packages d (fun x _ => parallel_ID d L (f^~ x) _ _ _) _ _). *)
(*     - intros. *)
(*       unfold parallel_ID. *)
(*       apply trimmed_parallel_raw. *)
(*       + apply H. *)
(*       + apply H0. *)
(*       + apply trimmed_pairs_map. *)
(*         intros. *)
(*         unfold pack. *)
(*         apply trimmed_ID. *)
(*     - intros. *)
(*       apply idents_foreach_disjoint_foreach. *)
(*       intros. *)
(*       now apply H2. *)

(*       Unshelve. *)
(*       + intros. *)
(*         now apply H. *)
(*       + apply H0. *)
(*       + apply H1. *)
(*   Defined. *)

(*   Lemma interface_foreach_swap : *)
(*     (forall {A} (a b : A) l f, interface_foreach f (a :: b :: l) = interface_foreach f (b :: a :: l)). *)
(*   Proof. *)
(*     intros. *)
(*     induction l. *)
(*     - simpl. *)
(*       now rewrite fsetUC. *)
(*     - simpl. *)
(*       rewrite fsetUA. *)
(*       rewrite (fsetUC (f a)). *)
(*       rewrite <- fsetUA. *)
(*       reflexivity. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_cons : (forall {A} f a L (d : nat), *)
(*     interface_hierarchy_foreach f (a :: L) d *)
(*     = interface_hierarchy (f a) d :|: interface_hierarchy_foreach (A := A) f L d). *)
(*   Proof. *)
(*     intros. *)
(*     unfold interface_hierarchy_foreach. *)
(*     rewrite interface_hierarchy_U. *)
(*     f_equal. *)
(*     setoid_rewrite interface_foreach_cons. *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_foreach_cat : forall {A} f L1 L2 d, *)
(*       interface_hierarchy_foreach f (L1 ++ L2) d = *)
(*       interface_hierarchy_foreach (A := A) f L1 d :|: interface_hierarchy_foreach (A := A) f L2 d. *)
(*   Proof. *)
(*     induction L1 ; intros. *)
(*     - unfold interface_hierarchy_foreach. *)
(*       simpl. *)
(*       rewrite <- interface_hierarchy_trivial. *)
(*       simpl. *)
(*       rewrite <- fset0E. *)
(*       rewrite fset0U. *)
(*       reflexivity. *)
(*     - rewrite interface_hierarchy_foreach_cons. *)
(*       rewrite <- fsetUA. *)
(*       rewrite <- IHL1. *)
(*       now rewrite <- interface_hierarchy_foreach_cons. *)
(*   Qed. *)

(*   Lemma interface_foreach_condition : *)
(*       (forall {A : eqType} f (L1 L2 : list A), *)
(*         (forall x, x \in L1 -> x \in L2) -> *)
(*           interface_foreach f L1 = *)
(*             interface_foreach (fun x => if x \in L2 then f x else fset [::]) L1). *)
(*   Proof. *)
(*     clear ; intros. *)
(*     induction L1. *)
(*     - reflexivity. *)
(*     - rewrite interface_foreach_cons. *)
(*       rewrite IHL1. *)
(*       2:{ *)
(*         intros. *)
(*         apply H. *)
(*         apply mem_tail. *)
(*         apply H0. *)
(*       } *)
(*       rewrite interface_foreach_cons. *)
(*       rewrite H. *)
(*       2: apply mem_head. *)
(*       reflexivity. *)
(*   Qed. *)

(*   Lemma interface_foreach_func_if_cons : *)
(*     forall {A : eqType} a (L1 L2 : seq A) f, *)
(*       interface_foreach (λ x : A, if x \in (a :: L2)%SEQ then f x else fset [::]) L1 *)
(*       = *)
(*       (if a \in L1 then f a else fset [::]) :|: *)
(*       interface_foreach (λ x : A, if x \in L2%SEQ then f x else fset [::]) L1. *)
(*   Proof. *)
(*     induction L1 ; intros. *)
(*     + now rewrite fsetUid. *)
(*     + rewrite interface_foreach_cons. *)
(*       rewrite interface_foreach_cons. *)

(*       rewrite IHL1. *)
(*       rewrite fsetUA. *)
(*       rewrite fsetUA. *)
(*       f_equal. *)
(*       rewrite <- fset0E. *)

(*       rewrite !in_cons. *)
(*       rewrite (eq_sym a). *)
(*       destruct (a0 == a) eqn:a0a. *)
(*       * move: a0a => /eqP ? ; subst. *)
(*         simpl. *)
(*         destruct (a \in L1), (a \in L2) ; now try rewrite fsetUid ; try rewrite fsetU0. *)
(*       * simpl. *)
(*         rewrite fsetUC. *)
(*         reflexivity. *)
(*   Qed. *)

(*   Lemma interface_foreach_sub_list : forall {A : eqType} f L1 L2, *)
(*       uniq L1 -> *)
(*       (forall x, x \in L1 -> x \in L2) -> *)
(*       interface_foreach f L1 = *)
(*       interface_foreach (A := A) (fun x => if x \in L1 then f x else [interface]) L2. *)
(*   Proof. *)
(*     intros. *)

(*     rewrite (interface_foreach_condition f L1 L1 (fun _ H => H)). *)
(*     induction L1 ; intros. *)
(*     - simpl. *)
(*       destruct L2 ; [ easy | ]. *)
(*       now rewrite <- interface_foreach_trivial. *)
(*     - rewrite interface_foreach_func_if_cons. *)
(*       rewrite interface_foreach_func_if_cons. *)
(*       rewrite mem_head. *)
(*       rewrite H0. *)
(*       2: apply mem_head. *)
(*       rewrite interface_foreach_cons. *)
(*       (* destruct (a \in _) ; [  ] *) *)
(*       rewrite IHL1. *)
(*       2:{ *)
(*         rewrite cons_uniq in H. *)
(*         now move: H => /andP [? ?] ; subst. *)
(*       } *)
(*       2:{ *)
(*         intros. *)
(*         apply H0. *)
(*         now apply mem_tail. *)
(*       } *)
(*       destruct (_ \in _). *)
(*       { *)
(*         rewrite fsetUA. *)
(*         rewrite fsetUid. *)
(*         reflexivity. *)
(*       } *)
(*       { *)
(*         rewrite <- fset0E. *)
(*         rewrite fset0U. *)
(*         reflexivity. *)
(*       } *)
(*   Qed. *)


(*   Lemma interface_foreach_trivial2 : forall {A} i L (* d *), *)
(*       (L <> [] \/ i = [interface]) -> *)
(*       i = (interface_foreach (λ (n : A), i) L ). *)
(*   Proof. *)
(*     intros. *)
(*     destruct H. *)
(*     - destruct L ; [ easy | ]. *)
(*       clear H. *)
(*       generalize dependent a. *)
(*       induction L ; intros. *)
(*       { *)
(*         rewrite interface_foreach_cons. *)
(*         simpl. *)
(*         rewrite <- fset0E. *)
(*         rewrite fsetU0. *)
(*         reflexivity. *)
(*       } *)
(*       { *)
(*         rewrite interface_foreach_cons. *)
(*         rewrite <- IHL. *)
(*         now rewrite fsetUid. *)
(*       } *)
(*     - rewrite H. *)
(*       induction L. *)
(*       + reflexivity. *)
(*       + rewrite interface_foreach_cons. *)
(*         rewrite <- IHL. *)
(*         now rewrite fsetUid. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_subset : forall f d K, *)
(*       (forall (x : nat) (H : (x <= d)%nat), f x :<=: K) -> *)
(*       interface_hierarchy f d :<=: K. *)
(*   Proof. *)
(*     intros. *)
(*     induction d. *)
(*     - now apply H. *)
(*     - simpl. *)
(*       rewrite fsubUset. *)
(*       now rewrite H ; [ rewrite IHd | ]. *)
(*   Qed. *)

(*   Lemma interface_hierarchy_subsetR : forall f d K, *)
(*       (exists (x : nat) (H : (x <= d)%nat), K :<=: f x) -> *)
(*       K :<=: interface_hierarchy f d. *)
(*   Proof. *)
(*     intros. *)
(*     induction d. *)
(*     - simpl. destruct H as [? []]. destruct x ; [ | easy ]. apply H. *)
(*     - simpl. *)
(*       destruct H as [? []]. *)
(*       destruct (x == d.+1) eqn:x_is_d ; move: x_is_d => /eqP ? ; subst. *)
(*       + apply fsubsetU. *)
(*         now rewrite H. *)
(*       + apply fsubsetU. *)
(*         rewrite IHd ; [ easy | ]. *)
(*         exists x. *)
(*         eexists. *)
(*         * Lia.lia. *)
(*         * apply H. *)
(*   Qed. *)

(*   Lemma trimmed_trim : forall I p, trimmed I (trim I p). *)
(*   Proof. *)
(*     intros. unfold trimmed. now rewrite trim_idemp. *)
(*   Qed. *)

(*   Ltac solve_direct_in := rewrite !fsubUset ; repeat (apply /andP ; split) ; repeat (apply fsubsetxx || (apply fsubsetU ; apply /orP ; ((right ; apply fsubsetxx) || left))). *)


(* Ltac solve_idents := *)
(*   repeat match goal with *)
(*     | |- context [ idents ?a :#: idents (?b :|: ?c) ] => *)
(*         unfold idents at 2 *)
(*         ; rewrite (imfsetU _ b c) *)
(*         ; fold (idents b) ; fold (idents c) *)
(*         ; rewrite fdisjointUr *)
(*         ; apply /andP ; split *)
(*     | |- context [ idents (?a :|: ?b) :#: idents ?c ] => *)
(*         unfold idents at 1 *)
(*         ; rewrite (imfsetU _ a b) *)
(*         ; fold (idents a) ; fold (idents b) *)
(*         ; rewrite fdisjointUl *)
(*         ; apply /andP ; split *)
(*     | |- context [ idents (fset (?a :: ?b :: _)) ] => rewrite (fset_cons a) *)
(*     | |- context [ ?K :#: idents (interface_hierarchy ?f ?d) ] => *)
(*         apply idents_interface_hierachy3 ; intros *)
(*     | |- context [ idents (interface_hierarchy ?f ?d) :#: ?K ] => *)
(*         rewrite fdisjointC ; apply idents_interface_hierachy3 ; intros *)
(*     | |- context [ idents (interface_foreach ?f ?L) :#: idents (interface_foreach ?g ?K) ] => *)
(*         apply idents_foreach_disjoint_foreach_in *)
(*         ; let H := fresh in *)
(*           intros ? H *)
(*           ; now repeat (move: H => /orP [ /eqP ? | H ]) ; subst *)
(*     | |- context [ idents ?K :#: idents (interface_foreach ?f ?L) ] => *)
(*         let H := fresh in *)
(*         apply idents_disjoint_foreach_in *)
(*         ; intros ? H *)
(*     (* ; rewrite in_cons in H *) *)
(*     (* ; repeat (move: H => /orP [ /eqP ? | H ]) ; subst *) *)
(*     | |- context [ idents (interface_foreach ?f ?L) :#: ?K ] => *)
(*         rewrite fdisjointC *)
(*     end ; unfold idents ; solve_imfset_disjoint. *)

(* Ltac solve_trimmed2 := *)
(*   repeat match goal with *)
(*     | |- context [ trimmed _ (trim _ _) ] => *)
(*         apply trimmed_trim *)
(*     | |- context [ trimmed ?E (parallel_raw _) ] => *)
(*         eapply trimmed_parallel_raw *)
(*         ; [ | | apply trimmed_pairs_map ; intros  ] *)
(*         ; [ | reflexivity | ] *)
(*         ; [ | solve_trimmed2 ] *)
(*         ; [ intros ; unfold idents ; solve_imfset_disjoint ] *)
(*     | |- context [ trimmed _ (pack (ℓ_packages _ _ _ _)) ] => *)
(*         apply trimmed_ℓ_packages *)
(*     | |- context [ trimmed ?E (par ?a ?b) ] => *)
(*         eapply trimmed_par ; [ | solve_trimmed2..] ; solve_idents *)
(*     | |- context [ trimmed ?E (pack {| pack := _; |}) ] => *)
(*         unfold pack *)
(*     | |- context [ trimmed ?E (mkfmap (cons ?a ?b)) ] => *)
(*         apply trimmed_package_cons *)
(*     | |- context [ trimmed ?E (mkfmap nil) ] => *)
(*         apply trimmed_empty_package *)
(*     | |- context [ trimmed ?E (ID _) ] => *)
(*         apply trimmed_ID *)
(*     end. *)

(*   Lemma domm_trim_disjoint_is_ident : *)
(*     forall E1 E2 p1 p2, idents E1 :#: idents E2 -> domm (trim E1 p1) :#: domm (trim E2 p2). *)
(*   Proof. *)
(*     intros. *)
(*     eapply fdisjoint_trans. *)
(*     1: apply domm_trim. *)
(*     rewrite fdisjointC. *)
(*     eapply fdisjoint_trans. *)
(*     1: apply domm_trim. *)
(*     rewrite fdisjointC. *)
(*     apply H. *)
(*   Qed. *)

(*   Lemma function_fset_cons_l : *)
(*     forall {A : eqType} {T} x xs K, (fun (n : A) => fset (x n :: xs n) :|: K) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n) :|: K). *)
(*   Proof. now intros ; setoid_rewrite <- (fset_cat). Qed. *)

(*   Lemma function_fset_cat_l : *)
(*     forall {A : eqType} {T} ys xs K, (fun (n : A) => fset (ys n ++ xs n) :|: K) = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n) :|: K). *)
(*   Proof. now intros ; setoid_rewrite <- (fset_cat). Qed. *)

(*   Lemma function_fset_cat_middle : *)
(*     forall {A : eqType} {T} ys xs L R, (fun (n : A) => L :|: fset (ys n ++ xs n) :|: R) = (fun (n : A) => L :|: fset (T := T) (ys n) :|: fset (xs n) :|: R). *)
(*   Proof. *)
(*     intros. *)
(*     setoid_rewrite fsetUC. *)
(*     setoid_rewrite <- fsetUA. *)
(*     setoid_rewrite <- (fset_cat). *)
(*     reflexivity. *)
(*   Qed. *)

(*   Lemma function_fset_cat : *)
(*     forall {A : eqType} {T} ys xs, (fun (n : A) => fset (ys n ++ xs n)) = (fun (n : A) => fset (T := T) (ys n) :|: fset (xs n)). *)
(*   Proof. now setoid_rewrite <- (fset_cat). Qed. *)

(*   Lemma function_fset_cons : *)
(*     forall {A : eqType} {T} x xs, (fun (n : A) => fset (x n :: xs n)) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n)). *)
(*   Proof. now setoid_rewrite <- (fset_cat). Qed. *)

(*   Lemma function2_fset_cat : *)
(*     forall {A B : eqType} {T} x xs, (fun (a : A) (b : B) => fset (x a b :: xs a b)) = (fun (a : A) (b : B) => fset (T := T) ([x a b]) :|: fset (xs a b)). *)
(*   Proof. now setoid_rewrite <- (fset_cat). Qed. *)

(*   Lemma advantage_reflexivity : *)
(*     forall P A, AdvantageE P P A = 0%R. *)
(*   Proof. *)
(*     unfold AdvantageE. *)
(*     intros. *)
(*     rewrite subrr. *)
(*     rewrite Num.Theory.normr0. *)
(*     reflexivity. *)
(*   Qed. *)


