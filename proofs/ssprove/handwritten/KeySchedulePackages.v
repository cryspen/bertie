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
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

From KeyScheduleTheorem Require Import Core.

(*** Key schedule packages *)

Section KeySchedulePackages.

  Context {Dependencies : Dependencies}.
  Existing Instance Dependencies.

  Definition key_schedule_interface d :=
    ([interface
        #val #[ SET PSK 0 d ] : chSETinp → chSETout
      ]
       :|: DH_interface (* DHEXP, DHGEN *)
       :|: XTR_n d (* {ES,HS,AS},  0..d *)
       :|: XPD_n d (* XPN,         0..d *)
       :|: GET_O_star d).

  Definition key_schedule_export d :=
    GET_O_star d :|: SET_O_star d.

  (* Context {ord : chGroup → nat} {E : nat -> nat}. *)

  Lemma required_O_subset d : SET_DH d :<=: SET_O_star d :|: GET_O_star d.
  Proof.
    (* DH must be in O_star *)
    unfold SET_DH.
    unfold O_star.
    rewrite interface_hierarchy_foreachU.
    unfold interface_hierarchy_foreach.

    set d at 1 3 4.
    generalize dependent n.
    induction d ; intros.
    - simpl.
      unfold interface_hierarchy_foreach.
      unfold interface_hierarchy.
      unfold interface_foreach.
      rewrite !fsetUA.
      repeat (apply fsubsetU ; apply /orP ; ((right ; apply fsubsetxx) || left)).
    - unfold interface_hierarchy ; fold interface_hierarchy.
      rewrite fsubUset.
      apply /andP ; split ; apply fsubsetU ; apply /orP ; [ left | right ].
      + apply IHd.
      + simpl.
        unfold interface_hierarchy_foreach.
        unfold interface_hierarchy.
        unfold interface_foreach.
        rewrite !fsetUA.
        repeat (apply fsubsetU ; apply /orP ; ((right ; apply fsubsetxx) || left)).
  Qed.

  (* Fig.11, p.17 *)
  Program Definition Gks_real (d : nat) :
    package
      (L_K :|: L_L)
      [interface]
      (GET_O_star d) :=
    {package
       Gcore_real d (* ∘ XPD_DH_XTR *)
       #with
     _
    }.
    Fail Next Obligation.

  (* Look into the use nominal sets (PR - Markus?)! *)

  Obligation Tactic := idtac.
  Program Definition Gks_ideal d (S : Simulator d) :
    package
      L_K
      (key_schedule_interface d)
      (GET_O_star d)
    :=
    {package
       (* (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E)) ∘ *)
       (Ks d O_star true erefl) ∘ S
    }.
  Final Obligation.
    intros.
    unfold key_schedule_interface.
    eapply valid_link_upto.
    1:{
      eapply valid_package_inject_export.
      2: apply (pack_valid (Ks d O_star true erefl)).
      unfold GET_O_star.
      solve_in_fset.
    }
    1:{
      eapply valid_package_inject_import.
      2: apply (pack_valid S).
      solve_in_fset.
    }
    {
      solve_in_fset.
    }
    {
      solve_in_fset.
    }
  Qed.

End KeySchedulePackages.
