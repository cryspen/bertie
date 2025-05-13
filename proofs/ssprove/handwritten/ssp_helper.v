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
  forall a b c,
    Parable a c ->
    Parable b c ->
    Parable (par a b) c.
Proof.
  clear ; intros.
  unfold Parable.
  rewrite domm_union.
  rewrite fdisjointUl.
  rewrite H H0.
  reflexivity.
Qed.

Lemma parable_par_r :
  forall a b c,
    Parable c a ->
    Parable c b ->
    Parable c (par a b).
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

Definition mem_tail : forall {A : eqType} a (l : list A), forall {x}, x \in l -> x \in a :: l :=
  fun A a l x H =>
    (eq_ind_r [eta is_true] ([eta introTF (c:=true) orP] (or_intror H)) (in_cons (T:=A) a l x)).

(* Definition sumR : forall (l u : nat), (l <= u)%nat -> (nat -> R) -> R := *)
(*   (fun l u H f => \sum_(l <= i < u) (f i)). *)
(*   (* (fun l u H f => bigop.body GRing.zero (iota l (u - l)) (fun i : nat => BigBody i GRing.add true (f i))). *) *)

(* Definition sumR : forall (l u : nat), (l <= u)%nat -> (nat -> R) -> R := *)
(*   (fun l u H f => bigop.body GRing.zero (iota l (u - l)) (fun i : nat => BigBody i GRing.add true (f i))). *)

Definition sumR : forall (l u : nat), (l <= u)%nat -> (nat -> R) -> R :=
  (fun l u H f => (List.fold_left (fun y x => y + f x) (iota l (u - l)) 0)%R).

Definition sumR_H_fuel start fuel (f : forall (ℓ : nat), (start <= ℓ)%nat -> (ℓ <= start + fuel)%nat -> R) (* {struct fuel} *) : R.
  assert (((start + fuel.-1)%R <= start + fuel)%N).
  {
    rewrite leq_add2l. apply leq_pred. (* apply leqnSn. *)
  }
  generalize dependent start.
  generalize dependent fuel.
  induction fuel ; intros.
  - refine 0.
  - refine ((f (start + fuel) (leq_addr _ _) H) + IHfuel start (fun ℓ Hstart Hend => f ℓ Hstart (leq_trans Hend H)) _).
    + rewrite leq_add2l. apply leq_pred.
Defined.

  (* match fuel as k return (k <= fuel)%nat -> _ with *)
  (* | O => fun _ => 0 *)
  (* | S n => *)
  (*     fun H => *)
  (*       let Ht := *)
  (*         (eq_ind_r *)
  (*            (λ ℓ, (ℓ <= start + fuel)%N) *)
  (*            (eq_ind_r [eta is_true] (leq_trans (n:=n.+1) (m:=n) (p:=fuel) (leqnSn n) H) (leq_add2l start n fuel)) *)
  (*            (natrDE start n)) in *)
  (*       f (start + n) (leq_addr _ _) Ht + sumR_H_fuel start n (fun ℓ Hstart Hend => f ℓ Hstart (leq_trans Hend Ht)) *)
  (* end (leqnn fuel). *)

(* Definition sumR_H *)
(*   (l u : nat) (H_ul : (u >= l)%nat) *)
(*   (f : forall (ℓ : nat), (ℓ <= u)%nat -> R) : R. *)
(*   (* refine (\sum_(l <= i < u | (i <=? u)%nat) (f i _)). *) *)

(*   (* map_with_in *) *)
(*   (* epose Tagged. *) *)
(*   (* Check @tagged. *) *)
(*   (* (* (index_iota l u; _) *) *) *)
(*   (* (* (@tagged (seq R) _ _) *) *) *)
(*   (* (GRing.zero ; leq0n) *) *)
(*   refine (bigop.body (GRing.zero; _) (map_with_in (index_iota l u) (fun x H => (x; H))) _ (* (fun (i : ∑ y : nat, (y <= u)%nat) => BigBody _ _ true (f (i.π1) _; _)) *)).π1. *)
(*   2:{ *)
(*     intros i. *)
(*     refine (BigBody i _ true (f (i.π1) _ ; _)). *)
(*     2:{ *)
(*       Bertie *)
(*     - intros [] []. *)
(*       econstructor. *)
(*       + apply (GRing.add x y). *)
(*     - hnf. *)
(*       apply GRing.add. *)
(*     -  *)
  
(*   refine (\sum_(l <= i < u) (f i _)). *)
(*   Unset Printing Notations. *)
(*   Show Proof. *)
  

(*   eapply reducebig. *)
(*   3:{ *)
(*     refine (fun i => BigBody i (f _ (i \in index_iota l u) 0). *)
(*   } *)
(*   1:{ *)
(*     refine 0. *)
(*   } *)
(*   refine (index_iota l u). *)
(* Qed. *)
  
(*   refine (List.map). *)
  
(*   (* foldr op idx r *) *)
(*   (* refine \big[op/idx]_(x <- r) x *) *)
  
  
    
  
(*   refine (projT1 (bigop.body _ _ _)). *)
(*   3:{ *)
(*     intros. *)
(*     eapply reducebig. *)
    
    
(*     unfold bigbody. *)
  
(*   2:{ *)
(*     intros. *)
    
(* (* projT1 (bigop.body ?idx (index_iota l u) (fun i : nat => BigBody i ?Goal true ?Goal0)) *) *)
(*   epose ((\big[_/_]_(l <= i < u) _).π1). *)
(*   Unset Printing Notations. *)

  
(*   (0; leq0n _) *)
  
(*   refine (\big[(fun x => GRing.add x.1)/(0; leq0n _)]_(l <= i < u) _). *)
(*   refine (\big[GRing.add/0]_(l <= i < u) _). *)
(*   assert (0 <= i). *)
  
(*   Unset Printing Notations. *)
(*   Show Proof. *)

(*   Check (BIG_F _). *)

(*   (f i _)). *)
(*   refine (f i _). *)

  
(*   (fun l u H f => \sum_(l <= i < u) (f _ i)). *)

(*   (* big_geq *) *)
(* (* leq_bigmax *) *)
(* (* leq_sum *) *)


Definition sumR_H
  (l u : nat) (H_ul : (u >= l)%nat)
  (f : forall (ℓ : nat), (ℓ <= u)%nat -> R) : R.
Proof.
  apply (sumR_H_fuel l (u - l)).
  rewrite subnKC.
  - refine (fun ℓ _ H_le => f ℓ H_le).
  - apply H_ul.
Defined.

Lemma iota_succ : forall l f, (iota l f.+1) = iota l f ++ [(l+f)].
Proof.
  intros.
  generalize dependent l.
  induction f ; intros.
  - simpl.
    rewrite addr0.
    reflexivity.
  - simpl.
    specialize (IHf (l.+1)).
    setoid_rewrite IHf.
    rewrite !natrDE.
    rewrite addSn.
    rewrite addnS.
    reflexivity.
Qed.

(* H_Sul = (leq_trans H_ul (leqnSn u)) *)
Lemma sumR_succ : forall l u H_ul H_Sul f, sumR l u.+1 H_Sul f = f u + sumR l u H_ul f.
Proof.
  intros.
  unfold sumR.

  replace (u.+1 - l)%nat with ((u - l).+1)%nat by Lia.lia. (* by easy. *)
  rewrite iota_succ.
  rewrite List.fold_left_app.
  simpl.
  rewrite addrC.
  f_equal.
  f_equal.
  now apply subnKC.
Qed.

Lemma sumR_H_succ : forall l u H_ul H_Sul f, sumR_H l u.+1 H_Sul f = f u (leqnSn u) + sumR_H l u H_ul (fun ℓ H_le => f ℓ (leq_trans H_le (leqnSn u))).
Proof.
  intros.
  unfold sumR_H.

  unfold eq_rect_r.
  unfold eq_rect.

  unfold Logic.eq_sym.
  set (subnKC _).
  set (subnKC _).

  (* eassert (forall l u f, sumR_H_fuel l (u.+1 - l) f = sumR_H_fuel l (u - l).+1 _). *)
  (* { *)
  (*   clear l u H_ul H_Sul f e e0. *)
  (*   intros. *)

Admitted.

Lemma inequality :
  forall l l0 d, (l <= l0 + (d - l0))%N -> (l <= l0 + (d.+1 - l0))%N.
Proof. Lia.lia. Qed.

Lemma sumR_to_H : forall l u H_ul f, sumR l u H_ul f = sumR_H l u H_ul (fun n _ => f n).
Proof.
  intros.
  induction u.
  {
    reflexivity.
  }
  {
    destruct (l == u.+1) eqn:leqSu ; move: leqSu => /eqP leqSu ; subst.
    - unfold sumR, sumR_H.
      unfold eq_rect_r, eq_rect.
      destruct subnKC.
      rewrite subnn.
      rewrite subnn.
      reflexivity.
    - rewrite sumR_succ ; [ Lia.lia (* easy *) | ].
      intros.
      rewrite IHu.

      unfold sumR_H.
      unfold eq_rect_r.
      unfold eq_rect.
      simpl.
      destruct subnKC.
      simpl.
      destruct subnKC.
      simpl.

      rewrite subSn ; [ | easy ].
      simpl.
      reflexivity.
  }
Qed.

Lemma sumR_le : forall l u H_ul f g, (forall v Hf Hg, (f v Hf <= g v Hg))%R -> (sumR_H l u H_ul f  <= sumR_H l u H_ul g)%R.
Proof.
  intros.
  induction u.
  - unfold sumR_H.
    simpl.
    easy.
  - unfold sumR_H.
    destruct l.
    + simpl.
      unfold eq_rect_r.
      unfold eq_rect.
      unfold sumR_H_fuel.
      simpl.
    
Admitted.
(*     destruct subnKC. *)
(*     simpl. *)
(*     rewrite <- sumR_to_H. *)
(* Qed. *)

Fixpoint sumR_l {T : Type} (l : list T) (f : T -> R) : R :=
  match l with
  | [] => 0%R
  | (x :: xs) => f x + sumR_l xs f
  end.
(* Definition sum (l u : nat) (f : nat -> nat) : nat := sum_accum (u - l) l f 0%R. *)

Fixpoint sumR_l_in_rel {T : eqType} (l : list T) (l' : list T) (H_in : forall x, x \in l' -> x \in l) (f : forall (a : T), (a \in l)  -> R) : R :=
  match l' return (forall x, x \in l' -> x \in l) -> _ with
  | [] => fun _ => 0%R
  | (x :: xs) =>
      fun H_in => f x (H_in x (mem_head x xs)) + sumR_l_in_rel l xs (fun a H => H_in a (mem_tail x xs H)) f
  end H_in.
(* Definition sum (l u : nat) (f : nat -> nat) : nat := sum_accum (u - l) l f 0%R. *)

Definition maxR (f : bool -> R) : R := Order.max (f false) (f true).

Lemma max_leq : forall f g, (forall b, f b <= g b)%R -> (maxR f <= maxR g)%R.
Proof.
  intros.
  unfold maxR.
  unfold Num.max at 1.
  destruct (f _ < f _) eqn:f_largest.
  - refine (Order.le_trans (H true) _).
    unfold Num.max.
    destruct (g false < g true)%R eqn:g_largest.
    + easy.
    + destruct (Order.POrderTheory.comparable_leP (Num.Theory.real_comparable (Num.Theory.num_real (g true)) (Num.Theory.num_real (g false)))).
      * apply i.
      * now rewrite i in g_largest.
  - refine (Order.le_trans (H false) _).
    unfold Num.max.
    destruct (g false < g true)%R eqn:g_largest.
    + eauto.
    + easy.
Qed.
