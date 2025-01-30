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

From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem Require Import BasePackages.
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

From KeyScheduleTheorem Require Import Core.
From KeyScheduleTheorem Require Import MapPackage.

(*** Core theorem *)

Section CoreTheorem.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

Axiom R_cr : package fset0 [interface] [interface].
Axiom R_Z : package fset0 [interface] [interface].
Axiom R_D : package fset0 [interface] [interface].

Axiom Gacr :
    loc_GamePair
      [interface
         (* #val #[ ACR ] : 'unit → 'unit *)
      ].

Axiom Gsodh :
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

Axiom Ai : raw_package -> bool -> raw_package.
Axiom R_sodh : package fset0 [interface] [interface].

Axiom Gcore_sodh : package fset0 [interface] [interface].

Lemma core_theorem :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gcore_real (* d *))
       (Gcore_ideal (* d *) Score) (A (* ∘ R d M H *))
     <= sumR_l [R_cr; R_Z; R_D] (fun R => Advantage Gacr (A ∘ R))
     +maxR (fun i => Advantage Gsodh (Ai A i ∘ R_sodh) + AdvantageE Gcore_sodh (Gcore_ideal (* d *) Score) (Ai A i))
    )%R.
Proof. Admitted.

Lemma equation20_lhs :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_sodh (Gcore_hyb 0) (Ai A i) = 0)%R.
Proof. Admitted.

Lemma equation20_rhs :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_ki (Gcore_hyb d) (Ai A i) = 0)%R.
Proof. Admitted.

Lemma hyb_telescope :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  (* forall (K_table : chHandle -> nat), *)
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
      (AdvantageE (Gcore_hyb 0) (Gcore_hyb d) (Ai A i)
       = sumR 0 (d-1) (fun ℓ => AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ+1)) (Ai A i))
      )%R.
Proof. Admitted.

Lemma equation20_eq :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  (* forall (K_table : chHandle -> nat), *)
  forall i,
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE Gcore_sodh (Gcore_ideal (* d *) Score) (Ai A i)
     <= AdvantageE Gcore_ki (Gcore_ideal (* d *) Score) (Ai A i)
     +sumR 0 (d-1) (fun ℓ => AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ + 1)) (Ai A i))
    )%R.
Proof.
  intros.

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := (Gcore_hyb 0)).
  rewrite (equation20_lhs (* d *) Score).
  rewrite add0r.

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := Gcore_ki).
  rewrite addrC.
  apply Num.Theory.lerD ; [ easy | ].

  eapply Order.le_trans ; [ apply Advantage_triangle | ].
  instantiate (1 := (Gcore_hyb d)).

  epose (e := equation20_rhs (* d *) Score).
  setoid_rewrite (Advantage_sym _ _) in e.
  rewrite e ; clear e.
  rewrite addr0.

  setoid_rewrite <- hyb_telescope ; easy.
Qed.

End CoreTheorem.
