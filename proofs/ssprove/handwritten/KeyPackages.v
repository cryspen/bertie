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
From KeyScheduleTheorem Require Import Utility.

From KeyScheduleTheorem Require Import Dependencies.

From KeyScheduleTheorem Require Import BasePackages.

(*** Helper *)

(*** Key packages *)

Section KeyPackages.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  Definition UNQ_O_star d : Interface :=
    interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (O_star).

  Definition SET_O_star d k : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ k ] : chSETinp → chSETout]) (O_star) d.

  Definition SET_O_star_ℓ d ℓ : Interface :=
    interface_foreach (fun n => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (O_star).

  Definition GET_O_star d k : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout]) (O_star) d.

  Definition GET_O_star_ℓ d ℓ : Interface :=
    interface_foreach (fun n => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (O_star).

  (* Fig 13-14. K key and log *)

  Axiom exists_h_star : (chHandle -> raw_code 'unit) -> code L_L [interface] 'unit.
  Inductive ZAF := | Z | A | F | D | R.

  Axiom level : chHandle -> nat.

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
         (exists_h_star (fun h_star =>
           temp ← get_or_fail (L_table h_star) fin_L_table ;;
           let '(h',hon',k) := (fto (fst (fst (otf temp))) , snd (fst (otf temp)) , snd (otf temp)) : _ in
           r ← ret (level h) ;;
           r' ← ret (level h_star) ;;
           match P with
           | Z => ret Datatypes.tt
           | A => if Datatypes.andb (hon == hon' == false) (r == r' == false)
                 then @fail _ ;; ret Datatypes.tt
                 else ret Datatypes.tt
           | F => @fail _ ;; ret Datatypes.tt
           | D => if hon == hon' == false then @fail _ ;; ret Datatypes.tt else ret Datatypes.tt
           | R => if hon == hon' == false
                 then @fail _ ;; ret Datatypes.tt (* abort *)
                 else @fail _ ;; ret Datatypes.tt (* win *)
           end)) ;;
         set_at (L_table h) fin_L_table (otf h, hon, otf k) ;;
         ret h
      }
    ].

    unfold set_at.
    ssprove_valid ; try apply (in_L_table _).
    - apply prog_valid.
    - apply valid_putr.
      + apply in_L_table.
      + apply valid_ret.

        Unshelve.
    1: apply DepInstance.
    1:{
      apply pos_prod ; [ | apply pos_key ].
      apply pos_prod ; [ | apply pos_bool ].
      apply pos_handle.
    }
    all: apply 'unit.
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
    intros.
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
    1:{
      apply valid_getr ; [ apply in_K_table | intros [] ; ssprove_valid ].
      - apply valid_ret.
      - apply valid_bind ; intros ; ssprove_valid.
    }
    1:{
      apply valid_getr ; [ apply in_K_table | intros [] ; ssprove_valid ].
      - apply valid_ret.
      - apply valid_bind ; intros ; ssprove_valid.
        apply valid_putr ; [ apply in_K_table | ssprove_valid ].
        apply valid_ret.
    }

    Unshelve.
    apply 'unit.
  Defined.
  Fail Next Obligation.

  Definition Ls d (Names : list name) (P : name -> ZAF) :
    uniq Names ->
    package
      (L_L)
      [interface]
      (interface_foreach (fun n => [interface
         #val #[ UNQ n d ] : chUNQinp → chUNQout
       ]) Names).
  Proof.
    intros.
    destruct Names.
    - exact ({package emptym #with valid_empty_package L_L [interface]}).
    - rewrite (interface_foreach_trivial [interface] (n :: Names)) ; [ | easy ].
      refine (parallel_package d (n :: Names) (fun a => L_package _ _ (P a)) _ _ _ H).
      + intros.
        solve_imfset_disjoint.
        simpl.
        apply fseparate_set1.
        * solve_imfset_disjoint.
        * apply fseparatem0.
      + intros.
        apply fseparate0m.
      + intros.
        apply trimmed_package_cons.
        apply trimmed_empty_package.
  Defined.

  Lemma trimmed_Ls d (Names : _) P :
    forall (H : uniq Names),
      trimmed (interface_foreach (fun n =>[interface
                                          #val #[ UNQ n d ] : chUNQinp → chUNQout
                 ]) Names) (Ls d Names P H).
  Proof.
    intros.
    unfold Ls.
    destruct Names ; [ intros ; apply trimmed_empty_package | ].
    rewrite trimmed_eq_rect_r.
    unfold pack.
    set (s :: Names) in *. replace (s :: _) with l by reflexivity.

    apply trimmed_parallel_raw.
    - intros.
      apply fseparate_set1.
      * solve_imfset_disjoint.
      * apply fseparatem0.
    - apply H.
    - apply trimmed_pairs_map.
      intros.
      apply trimmed_package_cons.
      apply trimmed_empty_package.
  Qed.

  Lemma function_fset_cons :
    forall {A : eqType} {T} x xs, (fun (n : A) => fset (x n :: xs n)) = (fun (n : A) => fset (T := T) ([x n]) :|: fset (xs n)).
  Proof. now setoid_rewrite <- (fset_cat). Qed.

  Lemma function2_fset_cat :
    forall {A B : eqType} {T} x xs, (fun (a : A) (b : B) => fset (x a b :: xs a b)) = (fun (a : A) (b : B) => fset (T := T) ([x a b]) :|: fset (xs a b)).
  Proof. now setoid_rewrite <- (fset_cat). Qed.

  Definition Ks (d k : nat) (H_lt : (d <= k)%nat) (Names : list name) (b : nat -> name -> bool) :
    uniq Names ->
    package
      (L_K)
      (interface_foreach (fun n => [interface #val #[ UNQ n k ] : chUNQinp → chUNQout]) Names)
      (unionm (SET_n (Names) d k) (GET_n (Names) d k)).
  Proof.
    intros.
    rewrite interface_hierarchy_foreachU.

    rewrite <- function2_fset_cat.
    refine (combined _ d L_K
              (λ n : name, [interface #val #[UNQ n k] : chUNQinp → chUNQout ])
              (λ (n : name) (ℓ : nat),
                [interface #val #[SET n ℓ k] : chUNQinp → chDHEXPout
                 ; #val #[GET n ℓ k] : chDHEXPout → chGETout])
              Names (fun n H0 y => K_package k y n (leq_trans H0 H_lt) (b n y)) _ _ _ H).
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

  Lemma trimmed_Ks d k H_lt (Names : _) b :
    forall (H : uniq Names),
      trimmed (interface_hierarchy_foreach
                 (λ (n : name) (ℓ : nat),
                   [interface
                      #val #[SET n ℓ k] : chSETinp → chSETout ;
                    #val #[GET n ℓ k] : chGETinp → chGETout ]) Names d) (Ks d k H_lt Names b H).
  Proof.
    intros.
    unfold Ks.
    unfold combined.

    rewrite trimmed_eq_rect.
    destruct (function2_fset_cat _ _).
    unfold eq_rect.
    unfold eq_rect_r.
    unfold eq_rect.
    destruct Logic.eq_sym.
    apply (trimmed_ℓ_packages).
  Qed.

  (* Fig 15 *)
  Definition Nk_package (d k : nat) (_ : (d <= k)%nat) :
    package
      L_K
      [interface
         #val #[ UNQ DH k ] : chUNQinp → chUNQout
      ]
      (SET_n [DH] d k :|: GET_n [DH] d k)
    (* [interface *)
    (*    #val #[ SET DH ℓ k ] : chSETinp → chSETout ; *)
    (*    #val #[ GET DH ℓ k ] : chGETinp → chGETout *)
(* ] *).
    epose ℓ_packages.
    unfold SET_n.
    unfold GET_n.
    rewrite interface_hierarchy_U.
    rewrite (interface_hierarchy_trivial [interface #val #[UNQ DH k] : chUNQinp → chDHEXPout ] d).
    refine (ℓ_packages d
            (fun ℓ _ =>
            [package
      #def #[ SET DH ℓ k ] ('(h,hon,key) : chSETinp) : chSETout {
        #import {sig #[ UNQ DH k ] : chUNQinp → chUNQout }
        as unq_fn ;;
        get_or_case_fn (K_table h) (H := pos_prod pos_key pos_bool) fin_K_table chHandle (
            unq_fn (h, hon, key) ;;
            set_at (K_table h)(H := pos_prod pos_key pos_bool) fin_K_table (otf key, hon) ;;
            ret h
          ) (fun _ => ret h)
      } ;
      #def #[ GET DH ℓ k ] (h : chGETinp) : chGETout {
        p ← get_or_fail (K_table h) (H := pos_prod pos_key pos_bool) fin_K_table ;;
        let (k, hon) :=
          (fto (fst (otf p)) , snd (otf p) : 'bool) : (chProd chKey 'bool)
        in
        ret (k, hon)
      }
            ]) _ _).
    {
      intros.
      unfold SET_ℓ, GET_ℓ.
      unfold interface_foreach.
      unfold pack.
      rewrite <- fset1E.
      rewrite <- fset_cons.
      apply (trimmed_package_cons).
      apply (trimmed_package_cons).
      apply (trimmed_empty_package).
    }
    {
      intros.
      unfold SET_ℓ, GET_ℓ.
      unfold interface_foreach.
      unfold idents.
      solve_imfset_disjoint.
    }

    Unshelve.
    all: try apply DepInstance.

    unfold SET_ℓ, GET_ℓ.
    unfold interface_foreach.
    set ([interface #val #[UNQ DH k] : chUNQinp → chDHEXPout ]).
    rewrite <- (fset1E ).
    rewrite <- fset_cons.
    subst f.

    
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
  (* Definition K (n : chName) (ℓ : nat) := 10%nat. *)

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
  Next Obligation.
    intros.
    now rewrite <- interface_hierarchy_trivial.
  Qed.
  Fail Next Obligation.

End KeyPackages.
