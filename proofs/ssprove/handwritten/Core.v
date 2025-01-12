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

Lemma idents_interface_hierachy2 :
  forall g f d,
    (forall x, idents g :#: idents (f x)) ->
    idents g :#: idents (interface_hierarchy f d).
Proof.
  clear ; intros.
  unfold idents.
  induction d ; simpl.
  - rewrite <- !fset0E.
    rewrite imfset0.
    apply fdisjoints0.
  - rewrite imfsetU.
    rewrite fdisjointUr.
    rewrite IHd.
    + intros.
      rewrite Bool.andb_true_r.
      apply H.
Qed.

Axiom Gcore_ki : package fset0 [interface] [interface].
Axiom Gcore_hyb : forall (d : nat), package f_parameter_cursor_loc
    (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[HASH] : chHASHout → chHASHout ]
     :|: (GET_XTR d.+1 :|: SET_XTR d.+1))
    (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[HASH] : chHASHout → chHASHout ]
     :|: (GET_XTR d.+1 :|: SET_XTR d.+1)
     :|: [interface #val #[SET_DH] : chKinp → chXPDout ]).

Context (PrntN: name -> code fset0 fset0 (chName × chName)).
Context (Labels : name -> bool -> code fset0 fset0 chLabel).

Lemma xpd_dh : forall {ord : chGroup → nat} {E : nat -> nat} (d : nat),
    domm (pack (XPD_packages d)) :#: domm (pack (DH_package ord E)) = true.
Proof.
  intros.
  unfold pack.

  erewrite <- (trimmed_xpd_package d).
  rewrite <- (trimmed_dh).

  apply domm_trim_disjoint_is_ident.
  unfold XPD_n_ℓ.
  rewrite fdisjointC.
  apply idents_interface_hierachy2.
  intros.
  rewrite (fset_cons (DHGEN, (chGroup, chGroup))).
  unfold idents.
  unfold DHEXP, DHGEN, XPD, XPR, serialize_name.
  simpl.
  solve_imfset_disjoint.
Qed.

Lemma xtr_dh : forall {ord : chGroup → nat} {E : nat -> nat} (d : nat),
    domm (pack (XTR_packages d)) :#: domm (pack (DH_package ord E)) = true.
Proof.
  intros.
  unfold pack.

  erewrite <- (trimmed_xtr_package d).
  rewrite <- (trimmed_dh).

  apply domm_trim_disjoint_is_ident.
  rewrite fdisjointC.
  apply idents_interface_hierachy2.
  intros.
  rewrite (fset_cons (DHGEN, (chGroup, chGroup))).
  unfold idents.
  unfold DHEXP, DHGEN, XTR, serialize_name.
  simpl.
  solve_imfset_disjoint.
Qed.

Definition Gcore_real {ord : chGroup → nat}
  {E : nat -> nat} (d : nat) :
    package fset0
      ((GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[ HASH ] : chHASHinp → chHASHout]) :|: (GET_XTR d.+1 :|: SET_XTR d.+1))
      (XPD_n_ℓ d :|: XTR_n_ℓ d
       :|: [interface #val #[DHGEN] : chDHGENout → chDHGENout ; #val #[DHEXP] : chDHEXPinp → chXPDout ])
      (* ([interface #val #[SET_psk 0] : chSETinp → chSETout ; *)
      (*   #val #[DHGEN] : 'unit → 'unit ; *)
      (*   #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: XPD_n_ℓ d :|:  *)
      (*    GET_o_star_ℓ d) *)
.
Proof.
  refine {package (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E)) ∘ Gcore_hyb d}.

  ssprove_valid.
  6:{
    rewrite fsetU0.
    apply fsubsetxx.
  }
  8,7: apply fsubsetxx.
  3: rewrite fset0U; apply fsubsetxx.
  3,4,6: try apply fsubsetxx.

  1:{
    unfold FDisjoint.
    rewrite domm_union.
    rewrite fdisjointUl.

    rewrite xpd_dh.
    rewrite xtr_dh.
    reflexivity.
  }
  1:{
    unfold FDisjoint.
    rewrite <- trimmed_xtr_package.
    rewrite <- trimmed_xpd_package.
    apply domm_trim_disjoint_is_ident.

    apply idents_interface_hierachy2.
    intros.
    rewrite fdisjointC.
    apply idents_interface_hierachy2.
    intros.

    simpl.
    unfold idents, XPD, XTR, serialize_name.
    solve_imfset_disjoint.
  }
  {
    solve_in_fset.
  }
Defined.
Fail Next Obligation.

(* Program Definition Gcore_ideal (d : nat) (Score : Simulator d) : *)
(*   package *)
(*     fset0 *)
(*     ([interface *)
(*        #val #[ SET_psk 0 ] : chSETinp → chSETout ; *)
(*        #val #[ DHGEN ] : 'unit → 'unit ; *)
(*        #val #[ DHEXP ] : 'unit → 'unit *)
(*     ] :|: *)
(*     XTR_n_ℓ d :|: *)
(*     XPD_n_ℓ d :|: *)
(*     GET_o_star_ℓ d) *)
(*     [interface *)
(*     ] := {package (Score ∘ Key_o_star_ideal d) }. *)
(* Admit Obligations. *)
(* Fail Next Obligation. *)
