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
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

(*** Core *)

Definition Simulator d :=
  (package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d)
    [interface
    ]
  ).

Axiom Gcore_ki : package fset0 [interface] [interface].
Axiom Gcore_hyb : forall (d : nat), package f_parameter_cursor_loc
    (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[HASH] : chHASHout → chHASHout ]
     :|: (GET_XTR d.+1 :|: SET_XTR d.+1))
    (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[HASH] : chHASHout → chHASHout ]
     :|: (GET_XTR d.+1 :|: SET_XTR d.+1)
     :|: [interface #val #[SET ExtraTypes.DH 0] : chKinp → chXPDout ]).

Context (PrntN: name -> code fset0 fset0 (chName × chName)).
Context (Labels : name -> bool -> code fset0 fset0 chLabel).

Program Definition Gcore_real (d : nat) :
    package fset0
      ((GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[ HASH ] : chHASHinp → chHASHout]) :|: (GET_XTR d.+1 :|: SET_XTR d.+1))
      (XPD_n_ℓ d.+1 :|: XTR_n_ℓ d.+1
       :|: [interface #val #[DHGEN] : chDHGENout → chDHGENout ; #val #[DHEXP] : chDHEXPinp → chXPDout ])
      (* ([interface #val #[SET_psk 0] : chSETinp → chSETout ; *)
      (*   #val #[DHGEN] : 'unit → 'unit ; *)
      (*   #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: XPD_n_ℓ d :|:  *)
      (*    GET_o_star_ℓ d) *)
  :=
  {package (par (par (XPD_packages d) (XTR_packages d)) DH_package) ∘ Gcore_hyb d}.
Next Obligation.
  intros.
  ssprove_valid.
  1:{
    unfold FDisjoint.
    rewrite domm_union.
    simpl.
    erewrite <- (trimmed_xtr_level _ d).
    erewrite <- (trimmed_xpd_level _ d).

    admit.
  }
  1:{
    unfold FDisjoint.

    assert (forall d1 d2, domm (xpd_level_raw d1) :#: domm (xtr_level_raw d2)).
    {
      clear ; intros.
      unfold xpd_level_raw.
      unfold xtr_level_raw.
      unfold XTR_names.
      unfold XPR.
      unfold "++".
      unfold parallel_raw.
      unfold List.map.
      unfold List.fold_left.
      rewrite !domm_union.
      unfold domm.
      simpl.
      rewrite !fdisjointUr.
      rewrite !fdisjointUl.
      rewrite  <- !fset1E.
      rewrite !fdisjoints1.
      unfold "\notin" ; rewrite !ifF ; [ reflexivity | unfold "\in"; simpl; unfold "\in"; simpl ; Lia.lia.. ].
    }

    induction d.
    - simpl.
      unfold par ; rewrite !unionm0.
      apply H.
    - simpl.
      rewrite domm_union.
      set (temp := _ :|: _).
      rewrite domm_union.
      subst temp.
      rewrite !fdisjointUl.
      rewrite !fdisjointUr.
      rewrite IHd.
      rewrite Bool.andb_true_r.
      simpl.
      rewrite H.
      simpl.

      rewrite (domm_union (xtr_level_raw d)).
      rewrite fdisjointUr.
      rewrite (domm_union (xpd_level_raw d)).
      rewrite fdisjointUl.
      rewrite !H.
      simpl.


      assert (forall (d n : nat), n >= d -> domm (xpd_level_raw n) :#: domm (ℓ_raw_packages [eta xtr_level_raw] d)).
      {
        clear -H.
        induction d ; intros.
        - simpl.
          unfold domm.
          rewrite <- fset0E.
          now rewrite fdisjoints0.
        - simpl.
          set (temp := domm _).
          rewrite domm_union.
          subst temp.
          rewrite fdisjointUr.
          rewrite H.
          now rewrite IHd ; [ | Lia.lia ].
      }
      (* rewrite H0. *)

      assert (forall (d n : nat), n >= d -> domm (ℓ_raw_packages [eta xpd_level_raw] d) :#: domm (xtr_level_raw n)).
      {
        clear -H.
        induction d ; intros.
        - simpl.
          unfold domm.
          rewrite <- fset0E.
          now rewrite fdisjoint0s.
        - simpl.
          rewrite domm_union.
          rewrite fdisjointUl.
          rewrite H.
          now rewrite IHd ; [ | Lia.lia ].
      }

      rewrite H0 ; [ | Lia.lia].
      rewrite H1 ; [ | Lia.lia].
      reflexivity.
  }
  4:{
    rewrite fsetU0.
    apply fsubsetxx.
  }
  7,6: apply fsubsetxx.
  1: rewrite fset0U; apply fsubsetxx.
  1:{
    apply fsubsetxx.
  }
  1:{
    apply fsubsetxx.
  }
  1:{
    apply fsubsetxx.
  }
  1:{
    apply fsubsetxx.
  }
  Unshelve.
  1,2: apply d.

  (* all: try solve_Parable ; unfold idents ; solve_imfset_disjoint. *)
  (* all: try (apply valid_trim ; apply Xpd). *)
  (* all: try (rewrite fsetU0 ; apply fsubsetxx). *)
  (* all: try apply fsubsetxx. *)

Admit Obligations.
Fail Next Obligation.

Program Definition Gcore_ideal (d : nat) (Score : Simulator d) :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ] := {package (Score ∘ Key_o_star_ideal d) }.
Admit Obligations.
Fail Next Obligation.
