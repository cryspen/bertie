(* begin details : imports *)
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

Require Import Lia.

Import PackageNotation.
(* end details *)

(** * Advantage *)

Lemma advantage_reflexivity :
  forall P A, AdvantageE P P A = 0%R.
Proof.
  unfold AdvantageE.
  intros.
  rewrite subrr.
  rewrite Num.Theory.normr0.
  reflexivity.
Qed.

Lemma Advantage_par_emptyR :
  ∀ G₀ G₁ A,
    AdvantageE (par G₀ emptym) (par G₁ emptym) A = AdvantageE G₀ G₁ A.
Proof.
  intros G₀ G₁ A.
  unfold AdvantageE.
  unfold par.
  rewrite !unionm0.
  reflexivity.
Qed.

Lemma Advantage_parR :
  ∀ G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁,
    ValidPackage L₀ Game_import E₀ G₀ →
    ValidPackage L₁ Game_import E₁ G₁ →
    ValidPackage L₁' Game_import E₁ G₁' →
    flat E₁ →
    trimmed E₀ G₀ →
    trimmed E₁ G₁ →
    trimmed E₁ G₁' →
    AdvantageE (par G₁ G₀) (par G₁' G₀) A =
      AdvantageE G₁ G₁' (A ∘ par (ID E₁) G₀).
Proof.
  intros G₀ G₁ G₁' A L₀ L₁ L₁' E₀ E₁.
  intros Va0 Va1 Va1' Fe0 Te0 Te1 Te1'.
  replace (par G₁ G₀) with ((par (ID E₁) G₀) ∘ (par G₁ (ID Game_import) )).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    4:{
      ssprove_valid.
      rewrite domm_ID_fset.
      rewrite -fset0E.
      apply fdisjoints0.
    }
    2:{ unfold Game_import. rewrite -fset0E. discriminate. }
    2: apply trimmed_ID.
    rewrite link_id.
    2:{ unfold Game_import. rewrite -fset0E. discriminate. }
    2: assumption.
    rewrite id_link.
    2: assumption.
    reflexivity.
  }
  replace (par G₁' G₀) with ((par (ID E₁) G₀) ∘ (par G₁' (ID Game_import))).
  2:{
    erewrite <- interchange.
    all: ssprove_valid.
    4:{
      ssprove_valid.
      rewrite domm_ID_fset.
      rewrite -fset0E.
      apply fdisjoints0.
    }
    2:{ unfold Game_import. rewrite -fset0E. discriminate. }
    2: apply trimmed_ID.
    rewrite link_id.
    2:{ unfold Game_import. rewrite -fset0E. discriminate. }
    2: assumption.
    rewrite id_link.
    2: assumption.
    reflexivity.
  }
  rewrite -Advantage_link.
  unfold Game_import. rewrite -fset0E.
  rewrite Advantage_par_emptyR.
  reflexivity.
  Unshelve. all: auto.
Qed.
