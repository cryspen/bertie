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
Axiom Gcore_hyb : nat -> package fset0 [interface] [interface].

Program Definition Gcore_real (d : nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
:
    package fset0
      [interface]
      ([interface #val #[SET_psk 0] : chSETinp → chSETout ;
        #val #[DHGEN] : 'unit → 'unit ;
        #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: XPD_n_ℓ d :|: 
         GET_o_star_ℓ d)
  :=
  {package (par (par (XPD_packages d PrntN Labels) (XTR_packages d PrntN Labels)) DH_package) ∘ DH_package ∘ Gcore_hyb d}.
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
