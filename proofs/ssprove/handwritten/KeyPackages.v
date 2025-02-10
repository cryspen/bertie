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

From KeyScheduleTheorem Require Import Dependencies.

From KeyScheduleTheorem Require Import BasePackages.

(*** Helper *)


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

  Lemma valid_pairs_cons :
    forall {A : Type} L i (f : A -> Interface) g l,
      (forall a, valid_package L (i a) (f a) (g a)) ->
      valid_pairs L (List.map i l)
        (List.map f l)
        (List.map g l).
  Proof.
    intros.
    induction l.
    - 
      reflexivity.
    - unfold List.map ; fold (List.map f l); fold (List.map g l).
      simpl.
      destruct l.
      + apply H.
      + simpl.
        split ; [ apply H | apply IHl ].
  Qed.

(*** Key packages *)

Section KeyPackages.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  Definition UNQ_O_star d : Interface :=
    interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (O_star).

  Definition SET_O_star_ℓ d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (O_star) d.

  Definition GET_O_star_ℓ d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (O_star) d.

  (* Fig 13-14. K key and log *)

  (* Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit. *)
  Inductive ZAF := | Z | A | F.

  (* Axiom level : chHandle -> nat. *)

  (* Fig 13 *)
  Definition L_package d (n : name) (P : ZAF) :
    package
      (* (fset_Log_table Log_table) *)
      L_L
      [interface]
      [interface
         #val #[ UNQ n d ] : chUNQinp → chUNQout
      ].
  Proof.
    refine [package
      #def #[ UNQ n d (* n ℓ *) ] ('(h,hon,k) : chUNQinp) : chUNQout {
         (* (exists_h_star (fun h_star =>  *)
         (*   '(h',hon',k) ← get_or_fn (Log_table h_star) (chHandle × 'bool × chKey) (@fail _ ;; ret (chCanonical (chHandle × 'bool × chKey))) ;; *)
         (*   r ← ret (level h) ;; *)
         (*   r' ← ret (level h_star) ;; *)
         (*   match P with *)
         (*   | Z => ret Datatypes.tt *)
         (*   | A => if Datatypes.andb (hon == hon' == false) (r == r' == false) *)
         (*         then @fail _ ;; ret Datatypes.tt *)
         (*         else ret Datatypes.tt *)
         (*   | F => @fail _ ;; ret Datatypes.tt *)
         (*   end)) ;; *)
         set_at (L_table h) fin_L_table (otf h, hon, otf k) ;;
         ret h
      }
    ].

    unfold set_at.
    ssprove_valid ; apply (in_L_table _).
  Defined.
  Fail Next Obligation.

  (* Fig 14 *)

  (* Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool. *)
  (* Definition chK_table := chFin (mkpos #|fin_K_table|). *)

  Definition K_package d (n : name) (ℓ : nat) (* (d : nat) *) (_ : (ℓ <= d)%nat) (b : bool) :
    package
      L_K
      [interface
         #val #[ UNQ n d ] : chUNQinp → chUNQout
      ]
      [interface
         #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
      ].
  Proof.
    refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k_star) : chSETinp) : chSETout {
        #import {sig #[ UNQ n d ] : chUNQinp → chUNQout }
        as unq_fn ;;
        (* #import {sig #[ GET ] : chGETinp → chGETout } *)
        get_or_case_fn (H := _) (K_table h) fin_K_table chHandle (
            k ← ret (untag k_star) ;;
            k ←
              (if Datatypes.andb b hon
               then
                 x ← sample (uniform (H := pos_key) #|fin_key|) ;;
                 ret x
               else
                 ret k) ;;
            unq_fn (h, hon, k) ;;
            set_at (H := pos_prod pos_key pos_bool) (K_table h) fin_K_table (otf k, hon) ;;
            ret h
          )
          (fun _ => ret h)
      } ;
      #def #[ GET n ℓ d ] (h : chGETinp) : chGETout {
        p ← get_or_fn (H := pos_prod pos_key pos_bool) (K_table h) fin_K_table
          (@fail _ ;; ret (chCanonical chK_table)) ;;
        let (k_star, hon) := (fto (fst (otf p)) , snd (otf p) : 'bool) : (chProd chKey 'bool) in
        k ← ret (tag (chHandle_to_chHash h) (chKey_to_chName k_star)) ;;
        ret (k, hon)
      }
    ].

    unfold get_or_fn.
    unfold get_or_case_fn.
    unfold set_at.

    ssprove_valid ; try apply (in_K_table _).
    simpl.
    unfold SET.
    unfold GET.
    rewrite notin_cons. rewrite Bool.andb_true_r.
    apply /eqP.
    now apply serialize_name_notin_different_index.

    Unshelve.
    apply 'unit.
  Defined.
  Fail Next Obligation.

Definition Ls d (Names : list name) (P : ZAF) :
  uniq Names ->
  package
    (L_L)
    [interface]
    (interface_foreach (fun n =>[interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ]) Names).
Proof.
  intros.
  epose ({package parallel_raw (List.map (fun y => pack (L_package d y P)) Names)
           #with
            valid_parable _ (λ n : name, [interface #val #[UNQ n d] : chUNQinp → chDHEXPout ]) (fun x => [interface]) _ Names Names _ H _ _}).
  destruct Names ; [ refine {package _ #with valid_empty_package _ _} | ].
  rewrite <- interface_foreach_trivial in p ; [ | easy ].
  apply p.
  Unshelve.
  - intros.
    unfold idents.
    solve_imfset_disjoint.
  - apply trimmed_pairs_cons.
    intros.
    apply trimmed_package_cons.
    apply trimmed_empty_package.
  - apply valid_pairs_cons.
    intros.
    apply L_package.
Defined.

Lemma trimmed_Ls d (Names : _) :
  forall (H : uniq Names),
  trimmed (interface_foreach (fun n =>[interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
                                         ]) Names) (Ls d Names F H).
Proof.
  intros.
  unfold Ls.
  destruct Names ; [ intros ; apply trimmed_empty_package | ].
  rewrite trimmed_eq_rect_r.
  unfold pack.
  set (s :: Names) in *. replace (s :: _) with l by reflexivity.

  apply trimmed_parallel_raw.
  - intros.
    unfold idents.
    solve_imfset_disjoint.
  - apply H.
  - apply trimmed_pairs_cons.
    intros.
    apply trimmed_package_cons.
    apply trimmed_empty_package.
Qed.

Definition combined (A : eqType) (d : nat) L (f : A -> _) g Names (i : forall (n : nat), (n <= d)%nat -> forall (a : A), package L (f a) (g a n))
    (H : forall n, (n <= d)%nat -> ∀ x y : A, x ≠ y → idents (g x n) :#: idents (g y n))
    (H0 : forall n ℓ, (ℓ < n)%nat -> (n <= d)%nat -> ∀ x y : A, idents (g x ℓ) :#: idents (g y n))
    (H1 : forall n (H_le : (n <= d)%nat), ∀ a : A, trimmed (g a n) (i n H_le a))
    (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_hierarchy_foreach g Names d) :=
  ℓ_packages
    d
    (fun n H_le =>
       {package
          parallel_raw _ #with
         valid_parable _ _ _ _ _ _
           (H n H_le)
           H3
           (trimmed_pairs_cons _ _ _ (H1 n H_le))
           (valid_pairs_cons _ _ _ _ _ (fun m => pack_valid (i n H_le m)))
    })
    (fun n H_le =>
       trimmed_parallel_raw
         (g^~ n)
         Names
         _
         (H n H_le)
         H3
         (trimmed_pairs_cons _ _ _ (H1 n H_le)))
    (fun n ℓ i0 i1 => idents_foreach_disjoint_foreach _ _ Names (H0 n ℓ i0 i1)).

Lemma function_fset_cat :
  forall {A : eqType} {T} x xs, (fun (n : A) => fset (x n :: xs n)) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n)).
Proof. now setoid_rewrite <- (fset_cat). Qed.

Lemma function2_fset_cat :
  forall {A B : eqType} {T} x xs, (fun (a : A) (b : B) => fset (x a b :: xs a b)) = (fun (a : A) (b : B) => fset (T := T) ([x a b]) :|: fset (xs a b)).
Proof. now setoid_rewrite <- (fset_cat). Qed.

Definition Ks (d : nat) (Names : list name) (b : bool) :
  uniq Names ->
  package
  (L_K)
  (interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) Names)
  (interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (Names) d
     :|: interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (Names) d
  ).
Proof.
  intros.
  rewrite interface_hierarchy_foreachU.

  rewrite <- function2_fset_cat.
  refine (combined _ d L_K
            (λ n : name, [interface #val #[UNQ n d] : chUNQinp → chUNQout ])
            (λ (n : name) (ℓ : nat),
             [interface #val #[SET n ℓ d] : chUNQinp → chDHEXPout
              ; #val #[GET n ℓ d] : chDHEXPout → chGETout])
            Names (fun n H0 y => K_package d y n H0 b) _ _ _ H).
  - intros.
    rewrite fset_cons.
    rewrite fdisjointC.
    rewrite fset_cons.
    unfold idents.
    solve_imfset_disjoint.
  - intros.
    rewrite fset_cons.
    rewrite fdisjointC.
    rewrite fset_cons.
    unfold idents.
    solve_imfset_disjoint.
  - intros.
    apply trimmed_package_cons.
    apply trimmed_package_cons.
    apply trimmed_empty_package.
Defined.
Fail Next Obligation.

Lemma trimmed_Ks d (Names : _) b :
  forall (H : uniq Names),
  trimmed (interface_hierarchy_foreach
             (λ (n : name) (ℓ : nat),
            [interface
               #val #[SET n ℓ d] : chSETinp → chSETout ;
               #val #[GET n ℓ d] : chGETinp → chGETout ]) Names d) (Ks d Names b H).
Proof.
  intros.
  unfold Ks.
  unfold combined.
  set (ℓ_packages _ _ _ _).
  rewrite trimmed_eq_rect.
  destruct (function2_fset_cat _ _).
  refine (trimmed_ℓ_packages d (λ (n : nat) (H0 : (n <= d)%N), {package parallel_raw (List.map (λ y : name, _) Names) }) _ _).
Qed.

(* Fig 15 *)

Definition Nk_package (n : name) (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) :
  package
    L_K
    [interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ UNQ n d ] : chUNQinp → chUNQout }
        as unq_fn ;;
        get_or_case_fn (K_table h) fin_K_table chHandle (
            unq_fn (h, hon, k) ;;
            set_at (K_table h) fin_K_table (otf k, hon) ;;
            ret h
          ) (fun _ => ret h)
      } ;
      #def #[ GET n ℓ d ] (h : chGETinp) : chGETout {
        p ← get_or_fail (K_table h) fin_K_table ;;
        let (k, hon) :=
          (fto (fst (otf p)) , snd (otf p) : 'bool) : (chProd chKey 'bool)
        in
        ret (k, hon)
      }
    ].

  unfold get_or_fn.
  unfold get_or_case_fn.
  unfold get_or_fail.
  unfold set_at.

  ssprove_valid ; try apply (in_K_table _).
  solve_imfset_disjoint.
Defined.
Fail Next Obligation.

(* R-M-Pr-io^xpd - Interesting Fig 45., Fig.51-55 *)

Notation " 'chKinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chKout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition K (n : chName) (ℓ : nat) := 10%nat.

(**** *)

Definition K_psk_1_0 d := K_package d PSK 0 (ltac:(Lia.lia)) true.
Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition K_psk_0_d d :
  package (L_K) [interface #val #[UNQ PSK d] : chKinp → chKout ]
       (interface_hierarchy
          (λ n : nat,
             [interface #val #[SET PSK n d] : chKinp → chKout ; #val #[GET PSK n d] : chKout → chGETout ])
          d) :=
  (ℓ_packages d (fun n H => K_package d PSK n H false) _ _).
Next Obligation.
  intros.
  repeat (apply trimmed_empty_package || apply trimmed_package_cons).
Qed.
Next Obligation.
  intros.
  unfold idents.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  solve_imfset_disjoint.
Qed.
Fail Next Obligation.

End KeyPackages.
