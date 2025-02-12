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

(*** Core *)

Section Core.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  Axiom Gcore_ki : package fset0 [interface] [interface].
  Axiom Gcore_hyb : forall d (ℓ : nat),
      package f_parameter_cursor_loc
        ((GET_XPD d :|: SET_XPD d)
           :|: (GET_DH d :|: SET_DH d)
           :|: [interface #val #[ HASH ] : chHASHinp → chHASHout]
           :|: (GET_XTR d :|: SET_XTR d))
        (SET_O_star_ℓ d :|: GET_O_star_ℓ d).

  Axiom hash : package fset0 [interface] [interface #val #[ HASH ] : chHASHinp → chHASHout].
  Lemma trimmed_hash : (trimmed ([interface #val #[ HASH ] : chHASHinp → chHASHout]) hash). Admitted.

  Definition Simulator d :=
    (package
       fset0
       ([interface
           #val #[ SET PSK 0 d ] : chSETinp → chSETout
         ]
          :|: DH_interface
          :|: XTR_n d
          :|: XPD_n d)
       (UNQ_O_star d)
    ).

  Lemma idents_interface_hierachy2 :
    forall g f d,
      (forall x, idents g :#: idents (f x)) ->
      idents g :#: idents (interface_hierarchy f d).
  Proof.
    clear ; intros.
    unfold idents.
    induction d ; simpl.
    - apply H.
    - rewrite imfsetU.
      rewrite fdisjointUr.
      rewrite IHd.
      apply H.
  Qed.

  Lemma xtr_dh : forall (d : nat),
    domm (pack (XTR_packages d)) :#: domm (pack (DH_package d)) = true.
  Proof.
    intros.
    unfold pack.

    erewrite <- (trimmed_xtr_package d).
    rewrite <- (trimmed_dh).

    apply domm_trim_disjoint_is_ident.
    rewrite fdisjointC.
    apply idents_interface_hierachy2.
    intros.
    unfold DH_interface. rewrite (fset_cons (DHGEN, (chGroup, chGroup))).
    unfold idents.
    unfold DHEXP, DHGEN, XTR, serialize_name.
    simpl.
    solve_imfset_disjoint.
    all: Lia.lia.
  Qed.

  Lemma xpd_dh : forall (d : nat),
    domm (pack (XPD_packages d)) :#: domm (pack (DH_package d)) = true.
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
    unfold DH_interface. rewrite (fset_cons (DHGEN, (chGroup, chGroup))).
    unfold idents.
    unfold DHEXP, DHGEN, XPD, XPR, serialize_name.
    simpl.
    solve_imfset_disjoint.
    all: Lia.lia.
  Qed.

  Obligation Tactic := (* try timeout 8 *) idtac.
  Program Definition XPD_DH_XTR d :
    package
      (L_K :|: L_L)
      [interface]
      (XPD_n d :|: (DH_interface :|: XTR_n d)) :=
    {package
       (par
          (XPD_packages d ∘ (par (Ks d XPR false erefl ∘ Ls d XPR F erefl) hash))
          (par (DH_package d ∘ (Ks d [DH] false erefl ∘ Ls d [DH] F erefl))
             (XTR_packages d ∘ (Ks d XTR_names false erefl ∘ Ls d XTR_names F erefl))))
       ∘ (Ks d O_star false erefl ∘ Ls d O_star F (erefl))}.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply valid_link.
    2:{
      eapply valid_package_inject_import.
      2: eapply valid_link ; [ apply Ks | apply Ls ].
      rewrite <- fset0E.
      apply fsub0set.
    }

    rewrite <- trimmed_xpd_package.
    rewrite <- trimmed_dh.
    rewrite <- trimmed_hash.
    rewrite <- trimmed_xtr_package.

    eapply valid_par_upto.
    2:{
      eapply valid_link.
      1: apply valid_trim ; apply (pack_valid (XPD_packages d)).
      apply valid_par.
      2: rewrite (fsetUC) ; eapply valid_link ; apply pack_valid.
      2: apply valid_trim ; apply pack_valid.
      rewrite <- trimmed_Ks.
      rewrite link_trim_commut.
      solve_Parable.
      rewrite fdisjointC.
      apply idents_interface_hierachy3.
      intros.
      rewrite function_fset_cat.
      unfold idents.
      solve_imfset_disjoint.
    }

    2:{
      apply valid_par.
      2:{
        eapply valid_link.
        2:{
          eapply valid_link.
          - apply (Ks _ _ _).
          - apply (Ls _ _ _).
        }
        apply valid_trim ; eapply valid_package_inject_import ; [ | apply pack_valid ].
        1: unfold SET_DH , interface_hierarchy_foreach, interface_foreach ; solve_in_fset.
      }
      1:{
        rewrite !link_trim_commut.
        solve_Parable.

        unfold XTR_n_ℓ.
        apply idents_interface_hierachy3.
        intros.
        unfold DH_interface.
        rewrite fset_cons.
        unfold idents.
        solve_imfset_disjoint.
      }
      {
        eapply valid_link.
        2:{
          eapply valid_link.
          - apply (Ks _ _ _).
          - apply (Ls _ _ _).
        }
        apply valid_trim ; eapply valid_package_inject_import ; [ | apply pack_valid ].
        1: fold (GET_XTR d) ; fold (SET_XTR d) ; solve_in_fset.
      }
    }

    1:{
      rewrite !link_trim_commut.
      solve_Parable.

      {
        unfold XPD_n_ℓ.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        unfold DH_interface.
        rewrite fset_cons.
        unfold idents.
        solve_imfset_disjoint.
      }
      {
        apply idents_interface_hierachy3.
        intros.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    1: solve_in_fset.
    1:{
      rewrite <- !fset0E.
      rewrite !fsetU0.
      apply fsub0set.
      (* rewrite !fset0U. *)
      (* fold SET_O_star_ℓ. *)
      (* fold GET_O_star_ℓ. *)

      (* apply required_O_subset. *)
    }
    apply fsubsetxx.
  Defined.

  Obligation Tactic := (* try timeout 8 *) idtac.
  Program Definition Gcore_real (d : nat) :
    package (L_K :|: L_L)
            [interface]
      (* ((GET_XPD :|: SET_XPD) *)
      (*     :|: DH_Set_interface *)
      (*     :|: [interface #val #[ HASH ] : chHASHinp → chHASHout] *)
      (*    :|: (GET_XTR :|: SET_XTR)) *)
      ((* SET_O_star_ℓ d :|:  *)GET_O_star_ℓ d)
    (* ([interface #val #[SET_psk 0] : chSETinp → chSETout ; *)
    (*   #val #[DHGEN] : 'unit → 'unit ; *)
    (*   #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: XPD_n_ℓ d :|:  *)
    (*    GET_o_star_ℓ d) *)
    :=
    {package (Ks d O_star false erefl ∘ Ls d O_star F erefl) ∘ XPD_DH_XTR d}.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply valid_link.
    2: apply XPD_DH_XTR.
    eapply valid_link.
  - eapply valid_package_inject_export.
    2: apply (Ks _ _ _).
    unfold GET_O_star_ℓ.
    solve_in_fset.
  - eapply valid_package_inject_import.
    2: apply (Ls _ _ _).
    rewrite <- fset0E.
    solve_in_fset.
  Defined.
  Fail Next Obligation.

  Program Definition Gcore_ideal (d : nat) (Score : Simulator d) :
    package
      L_K
      ([interface
          #val #[ SET PSK 0 d ] : chSETinp → chSETout
        ] :|: DH_interface :|:
         XTR_n d :|:
         XPD_n d :|:
         GET_O_star_ℓ d)
      (GET_O_star_ℓ d) :=
    {package (Ks d O_star true erefl ∘ Score) }.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply (valid_link_upto L_K _ _ _ (UNQ_O_star d)).
    - epose (pack_valid (Ks d O_star true erefl)).
      eapply valid_package_inject_export.
      2: apply v.
      unfold GET_O_star_ℓ.
      solve_in_fset.
    - eapply valid_package_inject_import.
      2: apply (pack_valid Score).
      solve_in_fset.
    - solve_in_fset.
    - solve_in_fset.
  Defined.
  Fail Next Obligation.

End Core.
