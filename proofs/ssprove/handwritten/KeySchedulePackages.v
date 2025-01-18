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

Definition key_schedule_interface (* d *) :=
  ([interface
      #val #[ SET PSK 0 d ] : chSETinp → chSETout
    ]
     :|: DH_interface (* DHEXP, DHGEN *)
     :|: XTR_n_ℓ (* d *) (* {ES,HS,AS},  0..d *)
     :|: XPD_n_ℓ (* d *) (* XPN,         0..d *)
     :|: GET_O_star_ℓ d).

Definition key_schedule_export (* d *) :=
  GET_O_star_ℓ d :|: SET_O_star_ℓ d.

(* Context {ord : chGroup → nat} {E : nat -> nat}. *)

(* Fig.11, p.17 *)
Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition Gks_real (* (d : nat) *) :
  package
    fset0
    (GET_XPD d.+1 :|: SET_XPD d.+1 :|: DH_Set_interface :|: [interface #val #[HASH] : chHASHout → chHASHout ] :|: (GET_XTR d.+1 :|: SET_XTR d.+1))
    (SET_O_star_ℓ d :|: GET_O_star_ℓ d)
    (* ] *) :=
  {package
     (* (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E)) ∘ *)
     Gcore_real (* d *)
     #with
    _
  }.
Fail Next Obligation.

(* Look into the use nominal sets (PR - Markus?)! *)

Program Definition Gks_ideal (* d *) (S : Simulator d) :
  package
    fset0
    (key_schedule_interface (* d *))
    [interface
    ]
  :=
  {package
     (* (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E)) ∘ *)
     K_O_star d true ∘ S
  }.
Final Obligation.
intros.
ssprove_valid.
1:{
  eapply valid_package_inject_import.
  2:{
    epose (K_O_star d true).
    admit.
  }
Admitted.

End KeySchedulePackages.
