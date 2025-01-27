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

Axiom chGroup : choice_type.
Axiom chGroup_is_finGroup : FinGroup chGroup.
Axiom gen : chGroup -> code fset0 fset0 chGroup.

Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool.
Definition chK_table := 'fin #|fin_K_table|.

Class Dependencies := {
    PrntN: name -> code fset0 fset0 (chName × chName) ;
    Labels : name -> bool -> code fset0 fset0 chLabel ;
    (* O_star : list name ; *)
    xpd : chKey -> (chLabel * bitvec) -> code fset0 fset0 chKey ;
    xtr : chKey -> chKey -> code fset0 fset0 chKey ;
    xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle ;
    xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle ;
    PrntIdx : name -> forall (ℓ : bitvec), code fset0 [interface] (chProd chName chName) ;
    ord : chGroup → nat ;
    E : nat -> nat ;

    L_K : {fset Location} ;
    K_table : chHandle -> nat ;
    in_K_table : forall x, ('option chK_table; K_table x) \in L_K ;

    L_M : {fset Location} ;
    M : chHandle -> nat ;
    H : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M ;

    d : nat ;

    DHGEN_function : chGroup -> code fset0 fset0 chGroup ;
    DHEXP_function : chGroup -> chGroup -> code fset0 fset0 chHandle ;
  }.
