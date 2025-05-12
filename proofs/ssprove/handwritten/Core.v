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

Import PackageNotation.
(* end details *)

From KeyScheduleTheorem Require Import Types.
From KeyScheduleTheorem Require Import ExtraTypes.
From KeyScheduleTheorem Require Import Utility.

From KeyScheduleTheorem Require Import Dependencies.

From KeyScheduleTheorem Require Import BasePackages.
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

(** * Helper *)

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

(** * Core *)

Section Core.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  (** ** Definitions *)

  Notation " 'chXTRinp' " :=
    (chHandle × chHandle)
      (in custom pack_type at level 2).
  Notation " 'chXTRout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  Definition KS_interface d k :=
    ([interface #val #[SET PSK 0 k] : chSETinp → chSETout ]
       :|: DH_interface
       :|: (XPD_n d k :|: XTR_n d k)
       :|: GET_O_star d k
    ).

  Definition parallel_ID d (L : seq name) (f : name -> Interface) :
    (∀ x y, x ≠ y → idents (f x) :#: idents (f y)) ->
    (uniq L) ->
    (forall x, flat (f x)) ->
    package fset0 (interface_foreach f L) (interface_foreach f L) :=
    fun H H0 H1 =>
      parallel_package d L
        (fun x => {package ID (f x) #with valid_ID _ _ (H1 x)}) H
        (fun x => trimmed_ID _) H0.

  Definition combined_ID (d : nat) (L : seq name) (f : name -> nat -> Interface) :
    (forall n x y, x ≠ y → idents (f x n) :#: idents (f y n)) ->
    (uniq L) ->
    (forall n x, flat (f x n)) ->
    (forall n ℓ,
        (ℓ < n)%nat ->
        (n <= d)%nat ->
        ∀ x y, idents (f x ℓ) :#: idents (f y n)) ->
    package
      fset0
      (interface_hierarchy_foreach f L d)
      (interface_hierarchy_foreach f L d).
  Proof.
    intros.
    refine (ℓ_packages d (fun x _ => parallel_ID d L (f^~ x) _ _ _) _ _).
    - intros.
      unfold parallel_ID.
      apply trimmed_parallel_raw.
      + apply H.
      + apply H0.
      + apply trimmed_pairs_map.
        intros.
        unfold pack.
        apply trimmed_ID.
    - intros.
      apply idents_foreach_disjoint_foreach.
      intros.
      now apply H2.

      Unshelve.
      + intros.
        now apply H.
      + apply H0.
      + apply H1.
  Defined.

  Lemma reindex_interface_hierarchy_PSK2 :
    forall d k,
      (interface_hierarchy
         (λ n : nat, [interface #val #[SET PSK n k] : chUNQinp → chXTRout ])
         d.+1)
      =
        ([interface #val #[SET PSK 0 k] : chUNQinp → chXTRout ]
           :|: interface_hierarchy
           (λ n : nat, [interface #val #[SET PSK (n.+1) k] : chUNQinp → chXTRout ])
           d).
  Proof.
    intros.
    symmetry.
    induction d ; intros.
    - simpl.
      reflexivity.
    - simpl.
      rewrite fsetUA.
      rewrite  IHd.
      reflexivity.
  Qed.

  Axiom Hash :
    bool -> package fset0
             [interface]
             [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout].
  Lemma trimmed_hash (b : bool) :
    (trimmed ([interface #val #[ HASH  f_hash ] : chHASHinp → chHASHout]) (Hash b)).
  Admitted.

  Definition Simulator d k :=
    (package
       fset0
       ([interface
           #val #[ SET PSK 0 k ] : chSETinp → chSETout
         ]
          :|: DH_interface
          :|: XTR_n d k
          :|: XPD_n d k)
       (UNQ_O_star k)
    ).

  Lemma xtr_dh : forall (d k : nat) b H_lt,
    domm (pack (XTR_packages d k b H_lt)) :#: domm (pack (DH_package k)) = true.
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
    unfold DHEXP, DHGEN, XTR, serialize_name, XTR_n_ℓ_f.
    simpl.
    solve_imfset_disjoint.
  Qed.

  Lemma xpd_dh : forall (d k : nat) H_lt,
    domm (pack (XPD_packages d k H_lt)) :#: domm (pack (DH_package k)) = true.
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
    unfold DHEXP, DHGEN, XPD, XPR, serialize_name, XPD_n_ℓ_f.
    simpl.
    solve_imfset_disjoint.
  Qed.

  Obligation Tactic := (* try timeout 8 *) idtac.

  Program Definition XPD_ d k b key_b H_lt
    : package (L_K :|: L_L) [interface] (XPD_n d k) :=
    {package
       XPD_packages d k H_lt ∘
       (par
          (Ks d.+1 k (H_lt) (undup (XPR ++ XPR_parents)) key_b erefl
             ∘ Ls k (undup (XPR ++ XPR_parents)) (fun _ => F) erefl)
          (Hash b))
       #with _
    }.
  Next Obligation.
    intros.
    rewrite <- fset0U.
    eapply valid_link.
    1: apply pack_valid.

    rewrite <- fsetU0.
    rewrite <- (fsetUid (fset [::])).
    apply valid_par.
    3: apply pack_valid.
    2:{
      eapply valid_link.
      2: apply pack_valid.
      {
        fold (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ k] : chXTRout → chGETout ]) XPR_parents).

        eapply valid_package_inject_export.
        2: apply pack_valid.

        rewrite fsetUC.
        apply subset_pair.
        - rewrite fsubUset.
          apply /andP.
          split.
          + unfold SET_n. unfold SET_ℓ.
            fold (interface_hierarchy_foreach (λ n ℓ, [interface #val #[SET n ℓ k] : chSETinp → chSETout ]) (undup (XPR ++ XPR_parents))).
            rewrite interface_hierarchy_foreach_shift.
            unfold SET.

            apply fsubsetU.
            apply /orP ; right.

            unfold interface_hierarchy_foreach.
            apply interface_hierarchy_subset_pairs.
            intros.
            solve_in_fset.
          + unfold SET_n.

            unfold interface_hierarchy_foreach.
            unfold interface_hierarchy ; fold interface_hierarchy.
            apply fsubsetU.
            apply /orP ; left.

            apply interface_hierarchy_subset_pairs.
            intros.
            unfold SET_ℓ.

            apply interface_foreach_subset.
            intros.
            apply interface_foreach_subsetR.
            2: easy.
            assert (x \in undup (XPR ++ XPR_parents)).
            {
              rewrite !in_cons in H0 ; rewrite <- in_cons in H0 ; rewrite mem_seq1 in H0.
              now repeat move: H0 => /orP [ /eqP ? | H0 ] ; [ .. | move: H0 => /eqP ? ] ; subst.
            }
            exists x, H1.
            apply fsubsetxx.
        - unfold GET_n.

          unfold interface_hierarchy_foreach.
          unfold interface_hierarchy ; fold interface_hierarchy.
          apply fsubsetU.
          apply /orP ; left.

          apply interface_hierarchy_subset_pairs.
          intros.
          unfold GET_ℓ.

          apply interface_foreach_subset.
          intros.
          apply interface_foreach_subsetR.
          2: easy.
          assert (x \in undup (XPR ++ XPR_parents)).
          {
            rewrite !in_cons in H0 ; rewrite <- in_cons in H0 ; rewrite mem_seq1 in H0.
            now repeat move: H0 => /orP [ /eqP ? | H0 ] ; [ .. | move: H0 => /eqP ? ] ; subst.
          }
          exists x, H1.
          apply fsubsetxx.
      }
    }

    rewrite <- trimmed_Ks.
    rewrite !link_trim_commut.
    rewrite <- trimmed_hash.
    solve_Parable.

    unfold interface_hierarchy_foreach.
    rewrite fdisjointC.
    apply idents_interface_hierachy3.
    intros.
    apply idents_disjoint_foreach.
    intros.
    rewrite (fset_cons (SET _ _ _, _)).
    unfold idents.
    solve_imfset_disjoint.
  Qed.

  Definition XTR_ (d k : nat) (b : name -> bool)
    (key_b : nat -> name -> bool) (H_lt : (d <= k)%nat)
    : package (L_K :|: L_L) (fset [::]) (XTR_n d k).
  Proof.
    refine {package XTR_packages d k b H_lt ∘
       (Ks d k H_lt (undup (XTR_parent_names ++ XTR_names)) key_b erefl ∘ Ls k (undup (XTR_parent_names ++ XTR_names)) (fun _ => Z) erefl)
       #with
     _
      }.
    Unshelve.
    2-4: apply DepInstance.
    rewrite <- fset0U.

    eapply valid_link.
    2: eapply valid_link ; apply pack_valid.

    eapply valid_package_inject_import.
    2: apply pack_valid.

    rewrite undup_id ; [ | easy ].
    rewrite fsetUC.
    unfold SET_n, SET_ℓ.
    unfold GET_n, GET_ℓ.
    fold (interface_hierarchy_foreach (fun n ℓ => [interface #val #[SET n ℓ k] : chUNQinp → chXTRout ]) (XTR_parent_names ++ XTR_names) d).
    fold (interface_hierarchy_foreach (fun n ℓ => [interface #val #[GET n ℓ k] : chXTRout → chGETout ]) (XTR_parent_names ++ XTR_names) d).
    apply subset_pair ;
      rewrite interface_hierarchy_foreach_cat ;
      [ apply fsubsetUr | apply fsubsetUl ].
  Defined.

  Lemma idents_disjoint_foreach_in :
    (forall {A: eqType} f g (L : list A),
        (forall m, (m \in L) -> idents f :#: idents (g m)) ->
        idents f :#: idents (interface_foreach g L)).
  Proof.
    intros.
    induction L.
    + simpl.
      rewrite <- fset0E.
      unfold idents.
      rewrite imfset0.
      apply fdisjoints0.
    + rewrite interface_foreach_cons.
      unfold idents.
      rewrite !imfsetU.
      rewrite fdisjointUr.
      rewrite IHL ; clear IHL.
      * rewrite Bool.andb_true_r.
        apply H.
        apply mem_head.
      * intros.
        apply H.
        rewrite in_cons.
        apply /orP.
        now right.
  Qed.

  Program Definition XPD_DH_XTR d k b_hash b key_b H_lt :
    package
      (L_K :|: L_L)
      [interface]
      (XPD_n d k :|: (DH_interface :|: XTR_n d k)) :=
    {package
       (par
          (XPD_ d k b_hash key_b H_lt)
          (par
             (DH_package k
                ∘ (Ks d k (ltnW H_lt) [DH] key_b erefl
                     ∘ Ls k [DH] (fun _ => F) erefl))
             (XTR_packages d k b (ltnW H_lt)
                ∘ (Ks d k (ltnW H_lt)
                     (undup (XTR_names ++ XTR_parent_names))
                     key_b erefl
                     ∘ Ls k
                     (undup (XTR_names ++ XTR_parent_names))
                     (fun _ => Z) erefl))))
       ∘ (Ks d k (ltnW H_lt) O_star key_b erefl
            ∘ Ls k O_star (fun _ => Z) (erefl))}.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply valid_link.
    2: eapply valid_link ; apply pack_valid.
    (* *)
    rewrite <- trimmed_dh.
    rewrite <- trimmed_xtr_package.
    (* *)
    eapply valid_par_upto.
    2: apply pack_valid.
    2:{
      apply valid_par.
      2:{
        eapply valid_link.
        2: eapply valid_link ; apply pack_valid.
        1:{
          apply valid_trim.
          eapply valid_package_inject_import.
          2: apply pack_valid.
          apply fsubsetU.
          apply /orP.
          left.
          (* *)
          unfold SET_DH, SET_n.
          apply interface_hierarchy_subsetR.
          exists O, (leq0n d).
          (* *)
          apply fsubsetxx.
        }
      }
      2:{
        eapply valid_link.
        2: eapply valid_link ; apply pack_valid.
        1:{
          apply valid_trim.
          eapply valid_package_inject_import.
          2: apply pack_valid.
          rewrite fsetUC.
          apply subset_pair.
          1:{
            apply interface_hierarchy_subset_pairs.
            intros.
            unfold SET_ℓ.
            (* *)
            apply interface_foreach_subset.
            intros.
            apply interface_foreach_subsetR.
            2: easy.
            assert (x \in undup (XTR_names ++ XTR_parent_names)).
            {
              rewrite !in_cons in H0 ; rewrite <- in_cons in H0 ; rewrite mem_seq1 in H0.
              now repeat move: H0 => /orP [ /eqP ? | H0 ] ; [ .. | move: H0 => /eqP ? ] ; subst.
            }
            exists x, H1.
            apply fsubsetxx.
          }
          1:{
            apply interface_hierarchy_subset_pairs.
            intros.
            unfold SET_ℓ.
            (* *)
            apply interface_foreach_subset.
            intros.
            apply interface_foreach_subsetR.
            2: easy.
            assert (x \in undup (XTR_names ++ XTR_parent_names)).
            {
              rewrite !in_cons in H0 ; rewrite <- in_cons in H0 ; rewrite mem_seq1 in H0.
              now repeat move: H0 => /orP [ /eqP ? | H0 ] ; [ .. | move: H0 => /eqP ? ] ; subst.
            }
            exists x, H1.
            apply fsubsetxx.
          }
        }
      }
      {
        rewrite !link_trim_commut.
        solve_Parable.
        rewrite fdisjointC.
        (* *)
        unfold XTR_n.
        unfold DH_interface.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        rewrite fset_cons.
        unfold idents, XTR_n_ℓ_f.
        solve_imfset_disjoint.
      }
    }
    1:{
      rewrite !link_trim_commut.
      unfold XPD_.
      unfold pack.
      rewrite <- trimmed_xpd_package.
      rewrite !link_trim_commut.
      solve_Parable.
      (* *)
      {
        unfold XPD_n_ℓ.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        unfold DH_interface.
        rewrite fset_cons.
        unfold idents, XPD_n_ℓ_f.
        solve_imfset_disjoint.
      }
      {
        apply idents_interface_hierachy3.
        intros.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        apply idents_disjoint_foreach_in.
        intros.
        rewrite fdisjointC.
        apply idents_disjoint_foreach_in.
        intros.
        unfold idents, XPD_n_ℓ_f, XTR_n_ℓ_f.
        solve_imfset_disjoint.
        (* *)
        rewrite !in_cons in H1.
        rewrite !in_cons in H2.
        repeat move: H1 => /orP [/eqP ? | H1 ] ; subst ; repeat move: H2 => /orP [/eqP ? | H2 ] ; subst ; now apply serialize_name_notin_different_name.
      }
    }
    1: solve_in_fset.
    1:{
      rewrite <- !fset0E.
      rewrite !fsetU0.
      apply fsub0set.
    }
    apply fsubsetxx.
  Defined.

  (** * Actual core *)


  Notation " 'chXPDinp' " :=
    (chHandle × 'bool × bitvec)
      (in custom pack_type at level 2).
  Notation " 'chXPDout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  Axiom level : chHandle -> nat.

  (** [∀ n ∈ O]: the path from psk to n contains an [n' ∈ S.]
      If there exists a path from [dh] to an [n ∈ O], then it contains an [n' ∈ S].
   *)
  Definition seperation_points := [BIND].
  Definition early := [BIND].

  Axiom BinderArgs : bitvec -> code fset0 fset0 chKey.
  Axiom BinderHand : chHandle -> bitvec -> code fset0 fset0 chHandle.

  Axiom DhArgs : bitvec -> code fset0 fset0 (chProd chGroup chGroup).
  Axiom DhHand : chHandle -> code fset0 fset0 chHandle.

  Axiom sort : (chProd chGroup chGroup) -> (chProd chGroup chGroup).
  Axiom dh_angle : (chProd chGroup chGroup) -> chHandle.

  Definition check_raw (d : nat) (n : name) (ℓ : nat) : raw_package :=
    (mkfmap
       (cons
          (pair (XPD n ℓ d)
             (mkdef (chProd (chProd chHandle chBool) bitvec) chHandle
                (fun '(pair (pair h1 r) args) =>
                #import {sig #[ GET BINDER ℓ d ] : chGETinp → chGETout }
                as get_fn ;;
                #import {sig #[ XPD n ℓ d ] : chXPDinp → chXPDout }
                as xpd_fn ;;
                (if name_eq n BIND
                then
                  if r == false then assert (level h1 == 0) else ret Datatypes.tt ;;
                  if r == true then assert (level h1 >? 0) else ret Datatypes.tt
                else
                  if name_to_chName n
                       \in
                    (fset (List.map name_to_chName seperation_points)
                       :&: fset (List.map name_to_chName early))
                  then
                    binder ← BinderArgs args ;;
                    h_bndr ← BinderHand h1 args ;;
                    '(k, _) ← get_fn h_bndr ;;
                    assert (binder == k)
                  else
                    if n \in seperation_points
                    then
                      '(X,Y) ← DhArgs(args) ;;
                      let X : chGroup := X in
                      h_dh ← DhHand(h1) ;;
                      assert (h_dh == dh_angle (sort (X, Y))) ;;
                      binder ← BinderArgs(args) ;;
                      h_bndr ← BinderHand h1 args ;;
                      '(k, _) ← get_fn h_bndr ;;
                      assert (binder == k)
                    else ret Datatypes.tt) ;;
             h ← xpd_fn (h1, r, args) ;;
             ret h
          ))) nil)).

  Lemma check_valid d (n : name) (ℓ : nat) :
    ValidPackage f_parameter_cursor_loc
      (XPD_n_ℓ_f d n ℓ
         :|: [interface #val #[GET BINDER ℓ d] : chXPDout → chGETout ])
    (XPD_n_ℓ_f d n ℓ) (check_raw d n ℓ).
  Proof.
    unfold check_raw.
    ssprove_valid ; ssprove_valid'_2.
    - unfold mkopsig.
      unfold XPD_n_ℓ_f.
      rewrite <- fset1E.
      rewrite <- fset_cons.
      rewrite in_fset.
      rewrite !in_cons.
      rewrite eqxx ; apply /orP ; eauto.
    - unfold mkopsig.
      unfold XPD_n_ℓ_f.
      rewrite <- fset1E.
      rewrite <- fset_cons.
      rewrite in_fset.
      rewrite !in_cons.
      rewrite eqxx ; apply /orP ; eauto.
    - unfold mkopsig.
      unfold XPD_n_ℓ_f.
      rewrite <- fset1E.
      rewrite <- fset_cons.
      rewrite in_fset.
      rewrite !in_cons.
      rewrite eqxx ; apply /orP ; eauto.
  Defined.

  Definition check d (n : name) (ℓ : nat) :
    package fset0
      (XPD_n_ℓ_f d n ℓ
         :|: [interface #val #[ GET BINDER ℓ d ] : chGETinp → chGETout])
      (XPD_n_ℓ_f d n ℓ) :=
    {package check_raw d n ℓ #with check_valid d n ℓ}.

  Definition G_check (d k : nat) (H_lt : (d <= k)%nat) :
    package fset0
            (XPD_n d k :|: GET_n [BINDER] d k)
            (XPD_n d k).
  Proof.
    unfold XPD_n.
    unfold GET_n. unfold GET_ℓ.
    fold (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ k] : chXPDout → chGETout ]) [::BINDER] d).

    replace (interface_hierarchy_foreach
       (λ (n : name) (ℓ : nat), [interface #val #[XPD n ℓ k] : chXPDinp → chXPDout ]) XPR d
     :|: interface_hierarchy_foreach
           (λ (n : name) (ℓ : nat), [interface #val #[GET n ℓ k] : chXPDout → chGETout ]) [:: BINDER]
           d) with (interface_hierarchy_foreach
                      (λ (n : name) (ℓ : nat), [interface #val #[XPD n ℓ k] : chXPDinp → chXPDout ] :|: [interface #val #[GET BINDER ℓ k] : chXPDout → chGETout ]) XPR d).
    2:{
      rewrite <- interface_hierarchy_foreachU.
      f_equal.
      unfold interface_hierarchy_foreach.
      f_equal.
      apply functional_extensionality. intros.
      now rewrite <- interface_foreach_trivial.
    }

    replace (interface_hierarchy_foreach
           (λ (n : name) (ℓ : nat), [interface #val #[GET n ℓ k] : chXPDout → chGETout ]) [:: BINDER]
           d) with (interface_hierarchy_foreach
           (λ (n : name) (ℓ : nat), [interface #val #[GET BINDER ℓ k] : chXPDout → chGETout ]) XPR
           d).
    2:{
      unfold interface_hierarchy_foreach.
      f_equal.
      apply functional_extensionality ; intros.
      unfold XPR, interface_foreach, XPR_sub_PSK.
      simpl.
      now rewrite !fsetUid.
    }

    rewrite interface_hierarchy_foreachU.

    refine (ℓ_packages
           d
           (fun n H_le =>
              parallel_package d XPR
                (f := fun a => XPD_n_ℓ_f k a n :|: [interface #val #[GET BINDER n k] : chXPDout → chGETout ])
                (fun a => check k a n) _ _ _
           )
           (fun n H_le =>
              trimmed_parallel_raw
                _
                _
                (trimmed_pairs_map _ _ _ _))
           (fun n ℓ i0 i1 => idents_foreach_disjoint_foreach _ _ XPR _)
           ).
    - intros.
      unfold idents.
      unfold XPD_n_ℓ_f.
      solve_imfset_disjoint.
    - intros.
      apply trimmed_package_cons.
      apply trimmed_empty_package.
    - reflexivity.
    - intros.
      unfold idents.
      unfold XPD_n_ℓ_f.
      solve_imfset_disjoint.
    - reflexivity.
    - intros.
      apply trimmed_package_cons.
      apply trimmed_empty_package.
    - intros.
      unfold idents.
      unfold XPD_n_ℓ_f.
      solve_imfset_disjoint.
  Defined.

  Definition G_dh (d k : nat) (H_lt : (d <= k)%nat) :
    package fset0
            (SET_ℓ [DH] k 0)
            DH_interface := DH_package k.

  Definition I_star : seq name := [:: RM; ES; BIND; HS; AS; ESALT; HSALT].

  Ltac solve_direct_in :=
    rewrite !fsubUset
    ; repeat (apply /andP ; split)
    ; repeat (apply fsubsetxx
              || (apply fsubsetU
                  ; apply /orP
                  ; ((right ; apply fsubsetxx) || left))).

  Definition G_XTR_XPD (d k : nat) (b : name -> bool) (H_lt : (d < k)%nat) :
    package fset0
      ((GET_n [DH] d k
          :|: GET_n [PSK] d k
          :|: GET_n [ZERO_SALT] d k
          :|: GET_n [ZERO_IKM] d k
          :|: GET_n I_star d k)
         :|:
         (SET_n I_star d k
            :|: SET_n O_star d k
            :|: interface_hierarchy (fun ℓ =>
                  [interface #val #[ SET PSK ℓ.+1 k ] : chSETinp → chSETout])
                  d)
         :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout]
      )
      (XPD_n d k :|: XTR_n d k).
  Proof.
    refine {package par (XPD_packages d k H_lt) (XTR_packages d k b (ltnW H_lt))}.
    rewrite <- fsetUid.
    eapply valid_par_upto.
    - unfold XPD_, XTR_.
      unfold pack.
      rewrite <- trimmed_xpd_package.
      rewrite <- trimmed_xtr_package.
      (* rewrite !link_trim_commut. *)
      solve_Parable.
      unfold XPD_n, XTR_n.
      apply idents_interface_hierachy3.
      intros.
      rewrite fdisjointC.
      apply idents_interface_hierachy3.
      intros.
      unfold idents.
      unfold XTR_n_ℓ_f, XPD_n_ℓ_f.
      solve_imfset_disjoint.
    - apply pack_valid.
    - apply pack_valid.
    - apply fsubsetxx.
    - rewrite fsubUset.
      apply /andP ; split.
      + apply subset_pair.
        2: apply fsubsetxx.
        apply subset_pair.
        * unfold XPR_parents.
          unfold I_star.
          rewrite !interface_hierarchy_U.
          apply interface_hierarchy_subset_pairs.
          intros.
          unfold GET_ℓ.
          simpl.
          rewrite !fsetUA.
          solve_direct_in.
        * rewrite !interface_hierarchy_U.
          apply interface_hierarchy_subset_pairs.
          intros.
          unfold SET_ℓ.
          simpl.
          rewrite !fsetUA.
          solve_direct_in.
      + apply fsubsetU.
        apply /orP ; left.

        apply subset_pair.
        * unfold XTR_parent_names.
          rewrite !interface_hierarchy_U.
          apply interface_hierarchy_subset_pairs.
          intros.
          unfold GET_ℓ.
          simpl.
          rewrite !fsetUA.
          solve_direct_in.
        * rewrite !interface_hierarchy_U.
          apply interface_hierarchy_subset_pairs.
          intros.
          unfold SET_ℓ.
          simpl.
          rewrite !fsetUA.
          solve_direct_in.
    - apply fsubsetxx.
  Defined.

  Ltac solve_idents :=
    repeat match goal with
      | |- context [ idents ?a :#: idents (?b :|: ?c) ] =>
          unfold idents at 2
          ; rewrite (imfsetU _ b c)
          ; fold (idents b)
          ; fold (idents c)
          ; rewrite fdisjointUr
          ; apply /andP ; split
      | |- context [ idents (?a :|: ?b) :#: idents ?c ] =>
          unfold idents at 1
          ; rewrite (imfsetU _ a b)
          ; fold (idents a)
          ; fold (idents b)
          ; rewrite fdisjointUl
          ; apply /andP ; split
      | |- context [ idents (fset (?a :: ?b :: _)) ] =>
          rewrite (fset_cons a)
      | |- context [ ?K :#: idents (interface_hierarchy ?f ?d) ] =>
          apply idents_interface_hierachy3 ; intros
      | |- context [ idents (interface_hierarchy ?f ?d) :#: ?K ] =>
          rewrite fdisjointC
          ; apply idents_interface_hierachy3
          ; intros
      | |- context [ idents (interface_foreach ?f ?L)
                       :#:
                     idents (interface_foreach ?g ?K) ] =>
          apply idents_foreach_disjoint_foreach_in
          ; let H := fresh in
            intros ? H
            ; now repeat (move: H => /orP [ /eqP ? | H ])
            ; subst
      | |- context [ idents ?K :#: idents (interface_foreach ?f ?L) ] =>
          let H := fresh in
          apply idents_disjoint_foreach_in
          ; intros ? H
      (* ; rewrite in_cons in H *)
      (* ; repeat (move: H => /orP [ /eqP ? | H ]) ; subst *)
      | |- context [ idents (interface_foreach ?f ?L) :#: ?K ] =>
          rewrite fdisjointC
      end
    ; unfold idents
    ; solve_imfset_disjoint.

  Ltac solve_trimmed2 :=
    repeat match goal with
      | |- context [ trimmed _ (trim _ _) ] =>
          apply trimmed_trim
      | |- context [ trimmed ?E (parallel_raw _) ] =>
          eapply trimmed_parallel_raw
          ; [ | | apply trimmed_pairs_map ; intros  ]
          ; [ | reflexivity | ]
          ; [ | solve_trimmed2 ]
          ; [ intros ; unfold idents ; solve_imfset_disjoint ]
      | |- context [ trimmed _ (pack (ℓ_packages _ _ _ _)) ] =>
          apply trimmed_ℓ_packages
      | |- context [ trimmed ?E (par ?a ?b) ] =>
          eapply trimmed_par ; [ | solve_trimmed2..] ; solve_idents
      | |- context [ trimmed ?E (pack {| pack := _; |}) ] =>
          unfold pack
      | |- context [ trimmed ?E (mkfmap (cons ?a ?b)) ] =>
          apply trimmed_package_cons
      | |- context [ trimmed ?E (mkfmap nil) ] =>
          apply trimmed_empty_package
      | |- context [ trimmed ?E (ID _) ] =>
          apply trimmed_ID
      end.

  Lemma parable_link_l : forall a b c, Parable a b -> Parable (a ∘ c) b.
  Proof.
    intros.
    unfold Parable.
    unfold "∘".
    rewrite domm_map.
    apply H.
  Qed.

  Lemma parable_link_r : forall a b c, Parable a b -> Parable a (b ∘ c).
  Proof.
    intros.
    unfold Parable.
    unfold "∘".
    rewrite domm_map.
    apply H.
  Qed.

  Ltac split_Parable :=
    repeat match goal with
    | |- context [ Parable ?a (par ?b ?c) ] =>
        apply ssp_helper.parable_par_r
    | |- context [ Parable (par ?a ?b) ?c ] =>
        apply ssp_helper.parable_par_l
    | |- context [ Parable ?a (?b ∘ ?c) ] =>
        apply parable_link_r
    | |- context [ Parable (?a ∘ ?b) ?c ] =>
        apply parable_link_l
    end.

  Ltac solve_Parable2 :=
    split_Parable ;
    match goal with
    | [ |- context [ Parable ?a ?b ] ] =>
        let H := fresh in
        let H0 := fresh in
        eassert (H : trimmed _ a) by solve_trimmed2
        ; rewrite <- H ; clear H
        ; eassert (H0 : trimmed _ b) by solve_trimmed2
        ; rewrite <- H0 ; clear H0
        ; solve_Parable
        ; solve_idents
    end.

  Definition G_core (d k : nat) (b : bool) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k).
  Proof.
    refine ({package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun _ => b) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID d [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => b) erefl ∘ Ls k all_names (fun _ => Z) erefl) (K_package k PSK d.+1 H_lt b ∘ L_package k PSK Z)) (Hash b))
             } :  _).

    Unshelve.
    all: try now (intros ; solve_idents).
    all: try now (intros n x n0 u1 u2 ; rewrite !in_fset !(mem_seq1 _ _) => /eqP H ; inversion_clear H => /eqP H ; inversion_clear H).
    all: try now (intros n x u1 u2 ; rewrite !in_fset !(mem_seq1 _ _) => /eqP H ; inversion_clear H => /eqP H ; inversion_clear H).

    rewrite <- fsetUid.
    eapply valid_link.
    1:{
      eapply valid_par_upto.
      3:{
        apply valid_par.
        2: apply pack_valid.
        2: apply parallel_ID.
        shelve.
      }
      2:{
        eapply valid_link.
        2:{
          apply valid_par.
          3: apply pack_valid.
          2: apply pack_valid.

          shelve.
        }

        rewrite fsetUA.
        eapply valid_par_upto.
        2: apply pack_valid.
        2:{
          apply valid_par.
          2: apply pack_valid.
          2: apply pack_valid.
          shelve.
        }

        2: rewrite !fsetU0 ; apply fsubsetxx.
        2:{
          fold (XTR_n_ℓ_f k).
          fold (XTR_n d k).

          fold (GET_n O_star d k).
          rewrite fsetUC.
          rewrite fsetUA.
          rewrite fsubUset.

          apply /andP ; split.
          1: solve_in_fset.

          apply fsubsetU.
          apply /orP ; left.

          apply fsubsetU.
          apply /orP ; left.

          unfold GET_n.
          apply interface_hierarchy_subset_pairs.
          intros.

          apply interface_foreach_subsetR.
          2: easy.
          exists BINDER.
          eexists.
          1: easy.
          apply fsubsetxx.
        }
        2: apply fsubsetxx.
        shelve.
      }

      2: solve_in_fset.
      {
        shelve.
      }
      {
        apply fsubsetxx.
      }
      {
        fold (XTR_n_ℓ_f k).
        fold (XTR_n d k).
        fold (SET_ℓ [:: PSK] k 0).
        unfold interface_hierarchy_foreach.
        unfold GET_n.
        unfold GET_ℓ.
        solve_in_fset.
      }
    }
    {
      rewrite (fsetUA (interface_hierarchy_foreach _ _ _)).
      rewrite <- fsetUA.
      rewrite (fsetUC [interface #val #[HASH f_hash] : chHASHout → chHASHout ]).
      rewrite fsetUA.
      rewrite <- (fsetUid [interface]).
      rewrite <- fsetU0.
      apply valid_par.
      3: apply pack_valid.
      2:{
        eapply valid_package_inject_export.
        2:{
          rewrite <- fsetUid.
          rewrite <- (fsetUid [interface]).
          apply valid_par.
          2:{
            eapply valid_link ; apply pack_valid.
          }
          2:{
            eapply valid_link ; apply pack_valid.
          }
          shelve.
        }
        rewrite (fsetUC (SET_n all_names _ _)).
        rewrite (fsetUA _ _ (SET_n I_star d k :|: SET_n O_star d k
            :|: interface_hierarchy
            (λ ℓ : nat, [interface #val #[SET PSK ℓ.+1 k] : chUNQinp → chXTRout ]) d)).
        rewrite <- fsetUA.

        rewrite fset_cons.
        rewrite fset1E.
        rewrite <- (fsetUA (GET_n all_names d k)).
        rewrite (fsetUA (SET_n all_names d k)).
        rewrite (fsetUC _ ([interface #val #[GET PSK d.+1 k] : chXTRout → chGETout ])).
        rewrite (fsetUA (GET_n all_names d k)).

        apply subset_pair.
        - rewrite !interface_hierarchy_U.
          rewrite (interface_hierarchy_trivial [interface #val #[GET PSK d.+1 k] : chXTRout → chGETout ] d).
          rewrite !interface_hierarchy_U.

          apply interface_hierarchy_subset_pairs.
          intros.
          unfold GET_ℓ.
          simpl.
          rewrite !fsetUA.
          solve_direct_in.
        - rewrite !interface_hierarchy_U.

          rewrite fsubUset.
          apply /andP ; split.
          + rewrite <- interface_hierarchy_U.

            rewrite fsubUset.
            apply /andP ; split.
            * apply fsubsetU.
              apply /orP ; left.

              apply interface_hierarchy_subset_pairs.
              intros.
              unfold SET_ℓ.
              simpl.
              rewrite !fsetUA.
              solve_direct_in.
            * apply interface_hierarchy_subset.
              intros.
              destruct (x == d) eqn:x_is_d ; move: x_is_d => /eqP ? ; subst.
              {
                apply fsubsetU.
                apply /orP ; right.
                apply fsubsetxx.
              }
              {
                apply fsubsetU.
                apply /orP ; left.

                eapply interface_hierarchy_subsetR.
                exists x.+1.
                eexists.
                - Lia.lia.
                - solve_in_fset.
              }
          + apply fsubsetU.
            apply /orP ; left.

            eapply interface_hierarchy_subsetR.
            exists O, (leq0n d).
            simpl.
            unfold SET_ℓ.
            simpl.
            rewrite !fsetUA.
            solve_direct_in.
      }
      shelve.
    }

    Unshelve.
    (* Parable *)
    all: unfold G_dh, DH_package, combined_ID, parallel_ID, parallel_package.
    all: unfold G_XTR_XPD, XPD_packages, XTR_packages, G_check, Ks.
    all: unfold XTR_n_ℓ_f, XPD_n_ℓ_f.
    all: unfold XTR_n.
    all: unfold XPD_n.
    all: unfold combined, eq_rect_r, eq_rect, pack, K_package.
    all: unfold XTR_n_ℓ_f, XPD_n_ℓ_f.
    (* all: repeat destruct eq_trans. *)
    all: repeat destruct Logic.eq_sym.
    all: repeat destruct function2_fset_cat.
    all: repeat destruct eq_ind.
    all: repeat destruct Logic.eq_sym.
    (* all: unfold eq_trans. *)
    all: try rewrite <- trimmed_hash.
    all: try now solve_Parable2.
    (* all: unfold f_equal. *)

    all: unfold eq_trans.
    all: unfold f_equal.
    all: repeat destruct functional_extensionality.
    all: repeat destruct Logic.eq_sym.

    all: try now solve_Parable2.
  (* Time *) Defined. (* 36.626 *)
  Fail Next Obligation.

  Notation " 'chXTRinp' " :=
    (chHandle × chHandle)
      (in custom pack_type at level 2).
  Notation " 'chXTRout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  Obligation Tactic := (* try timeout 8 *) idtac.

  Program Definition KeysAndHash
    (d k : nat) (H_lt : (d < k)%nat) f_ks f_ls Names
    (Names_uniq : uniq Names)
    : package
        (L_K :|: L_L)
        [interface]
        ((SET_n Names d k
            :|: SET_ℓ [PSK] k d.+1
            :|: GET_n Names d k)
           :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ]) :=
    {package
       (par
          (par
             (Ks d k (ltnW H_lt) Names f_ks Names_uniq
                ∘ Ls k Names f_ls Names_uniq)
             (K_package k PSK d.+1 H_lt false
                ∘ L_package k PSK Z))
          (Hash true))}.
  Next Obligation.
    intros.
    eapply valid_par_upto.
    2:{
      eapply valid_par.
      2: eapply valid_link.
      2: eapply pack_valid.
      2: eapply pack_valid.
      2:{
        eapply valid_link.
        1: eapply pack_valid.
        1: eapply pack_valid.
      }
      unfold Ks.
      unfold K_package.

      unfold eq_rect_r, eq_rect.
      destruct Logic.eq_sym, function2_fset_cat.
      unfold combined.
      unfold eq_rect_r, eq_rect.
      destruct Logic.eq_sym.
      solve_Parable2.
    }
    2: eapply pack_valid.
    2: rewrite  fsetUid fsetU0; apply fsubsetxx.
    2: rewrite !fsetUid ; apply fsubsetxx.
    2:{
      rewrite (fset_cons (SET PSK d.+1 k, _)).
      rewrite fset1E.
      unfold SET_ℓ.
      unfold interface_foreach.
      solve_in_fset.
    }

    rewrite <- trimmed_hash.
    unfold Ks.
    unfold K_package.

    unfold eq_rect_r, eq_rect.
    destruct Logic.eq_sym, function2_fset_cat.
    unfold combined.
    unfold eq_rect_r, eq_rect.
    destruct Logic.eq_sym.
    solve_Parable2.
  Qed.
  Fail Next Obligation.

  Lemma subset_all (d k : nat) (H_lt : (d < k)%nat) :
    interface_hierarchy_foreach (λ (n : name) (ℓ : nat),
        [interface #val #[GET n ℓ k] : chXTRout → chGETout ])
        O_star d
        :|: (GET_n [:: DH] d k
               :|: GET_n [:: PSK] d k
               :|: GET_n [:: ZERO_SALT] d k
               :|: GET_n [:: ZERO_IKM] d k
               :|: GET_n I_star d k
               :|: (SET_n I_star d k
                      :|: SET_n O_star d k
                      :|: interface_hierarchy (λ ℓ : nat,
                            [interface #val #[SET PSK ℓ.+1 k] : chUNQinp → chXTRout ])
                            d)
               :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ])
        :|: (SET_ℓ [:: DH] k 0
               :|: interface_foreach (λ n : name,
                     [interface #val #[SET n 0 k] : chUNQinp → chXTRout ])
                     [:: PSK])
        :<=: SET_n all_names d k
          :|: SET_ℓ [:: PSK] k d.+1
          :|: GET_n all_names d k
          :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ].
  Proof.
    replace (interface_hierarchy_foreach _ _ _ :|: _ :|: _) with
      (interface_hierarchy_foreach
         (λ (n : name) (ℓ : nat), [interface #val #[GET n ℓ k] : chXTRout → chGETout ]) O_star d
         :|: (GET_n [:: DH] d k :|: GET_n [:: PSK] d k :|: GET_n [:: ZERO_SALT] d k
                :|: GET_n [:: ZERO_IKM] d k :|: GET_n I_star d k
                :|: (SET_ℓ [:: DH] k 0 :|: SET_n I_star d k :|: SET_n O_star d k)
         )
         :|: (interface_foreach (λ n : name, [interface #val #[SET n 0 k] : chUNQinp → chXTRout ])
                [:: PSK] :|: interface_hierarchy
                (λ ℓ : nat, [interface #val #[SET PSK ℓ.+1 k] : chUNQinp → chXTRout ]) d)
         :|: ([interface #val #[HASH f_hash] : chHASHout → chHASHout ])
      ).
    2:{
      rewrite !fsetUA.
      repeat set (interface_hierarchy_foreach _ _ _).
      repeat set (interface_hierarchy _ _).
      repeat set (interface_foreach _ _).
      repeat set (GET_n _ _ _).
      repeat set (SET_n _ _ _).
      solve_fset_eq.
    }

    apply subset_pair ; [ | apply fsubsetxx ].

    unfold interface_foreach.
    rewrite <- (reindex_interface_hierarchy_PSK2 d k).
    unfold interface_hierarchy ; fold interface_hierarchy.
    rewrite fsetUA.
    rewrite fsetUA.
    rewrite <- fsetUA.
    rewrite <- fsetUA.
    rewrite <- (fsetUC (GET_n all_names d k)).
    apply subset_pair.
    - rewrite !interface_hierarchy_U.
      apply interface_hierarchy_subset_pairs.
      intros.
      unfold GET_ℓ.
      rewrite <- !interface_foreach_cat.
      unfold cat ; fold (cat O_star).
      apply interface_foreach_subset.
      intros.
      apply interface_foreach_subsetR.
      2: easy.
      exists x.
      eexists.
      2: apply fsubsetxx.
      rewrite !in_cons in H0 |- * ; repeat move /orP: H0 => [ /eqP ? | H0 ] ; [ subst .. | discriminate ].
      all: now rewrite eqxx.
    - rewrite !fsetUA.
      apply subset_pair ; [ | apply fsubsetxx ].

      rewrite <- !fsetUA.
      rewrite fsubUset.
      rewrite !fsetUA.
      apply /andP ; split.
      {
        unfold SET_n.
        apply interface_hierarchy_subsetR.
        exists O, (leq0n _).
        unfold SET_ℓ.
        apply interface_foreach_subset.
        intros.
        rewrite mem_seq1 in H.
        move: H => /eqP H ; subst.
        apply interface_foreach_subsetR.
        2: easy.
        exists DH.
        eexists ; [ easy | ].
        apply fsubsetxx.
      }
      {
        rewrite !interface_hierarchy_U.
        apply interface_hierarchy_subset_pairs.
        intros.
        unfold SET_ℓ.
        rewrite <- !interface_foreach_cat.
        rewrite fsubUset.
        apply /andP ; split.
        {
          apply interface_foreach_subset.
          intros.
          apply interface_foreach_subsetR.
          2: easy.
          exists x.
          eexists.
          2: apply fsubsetxx.
          rewrite !in_cons in H0 |- * ; repeat move /orP: H0 => [ /eqP ? | H0 ] ; [ subst .. | discriminate ].
          all: now rewrite eqxx.
        }
        {
          apply interface_foreach_subsetR.
          2: easy.
          exists PSK.
          eexists ; [ easy | ].
          apply fsubsetxx.
        }
      }
  Qed.

  Program Definition G_check_XTR_XPD (d k : nat) (H_lt : (d < k)%nat) f_XTR_XPD :
    package
      fset0
      (interface_hierarchy_foreach (λ (n : name) (ℓ : nat),
           [interface #val #[GET n ℓ k] : chXTRout → chGETout ])
           O_star d
           :|: (GET_n [:: DH] d k
                  :|: GET_n [:: PSK] d k
                  :|: GET_n [:: ZERO_SALT] d k
                  :|: GET_n [:: ZERO_IKM] d k
                  :|: GET_n I_star d k
                  :|: (SET_n I_star d k
                         :|: SET_n O_star d k
                         :|: interface_hierarchy (λ ℓ : nat,
                               [interface #val #[SET PSK ℓ.+1 k] : chUNQinp → chXTRout ])
                               d)
                  :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ]))
      (XPD_n d k :|: XTR_n d k :|: GET_n O_star d k) :=
    {package
       (par
          (G_check d k (ltnW H_lt))
          (par
             (combined_ID d XTR_names
                (fun n ℓ =>
                   [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                _ erefl _ _)
             (combined_ID d O_star
                (fun n ℓ =>
                   [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                _ erefl _ _))
          ∘ (par
               (combined_ID d O_star
                  (fun n ℓ =>
                     [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                  _ erefl _ _)
               (G_XTR_XPD d k f_XTR_XPD H_lt)))
    }.
  Solve Obligations with intros ; solve_idents.
  Solve Obligations with
    intros
    ; now intros ? ? ?
    ; rewrite !in_fset !(mem_seq1 _ _) => /eqP H
    ; inversion_clear H => /eqP H
    ; inversion_clear H.
  Next Obligation.
    intros.
    {
      rewrite <- fsetUid.
      eapply valid_link.
      1:{
        rewrite <- fsetUid.
        rewrite <- !(fsetUA (XPD_n d k)).
        eapply valid_par.
        2: apply pack_valid.
        2:{
          rewrite <- fsetUid.
          eapply valid_par.
          2: apply pack_valid.
          2: apply pack_valid.
          shelve.
        }
        shelve.
      }
      {
        eapply valid_par_upto.
        2: apply pack_valid.
        2: apply pack_valid.
        2: solve_in_fset.
        2:{
          (* TODO: SET PSK ℓ.+1 ? *)
          apply fsubsetxx.

        }
        2:{
          rewrite <- fsetUA.
          rewrite fsetUC.
          rewrite (fsetUC (XPD_n _ _)).
          rewrite !fsetUA.
          apply subset_pair ; [ | apply fsubsetxx ].
          rewrite (fsetUC (GET_n _ _ _)).
          rewrite <- fsetUA.
          rewrite fsetUC.
          apply subset_pair ; [ | apply fsubsetxx ].
          rewrite fsubUset.
          rewrite fsubsetxx.
          rewrite Bool.andb_true_r.
          unfold GET_n.
          apply interface_hierarchy_subset_pairs.
          intros.
          unfold GET_ℓ.
          apply interface_foreach_subsetR.
          2: easy.
          exists BINDER.
          eexists ; [ easy | ].
          apply fsubsetxx.
        }
        shelve.
      }
    }
    Unshelve.
    1:{
      unfold combined_ID.
      solve_Parable2.
    }
    1:{
      unfold combined_ID.
      unfold G_check.
      unfold eq_rect.
      unfold eq_trans, f_equal.
      destruct functional_extensionality.
      unfold eq_rect_r, eq_rect.
      destruct Logic.eq_sym.
      unfold XPD_n_ℓ_f.
      solve_Parable2.
    }
    1:{
      unfold combined_ID.
      unfold G_XTR_XPD.
      unfold XPD_packages.
      unfold XTR_packages.
      unfold pack.
      unfold eq_rect_r.
      unfold eq_rect.
      destruct Logic.eq_sym.
      destruct Logic.eq_sym.
      destruct Logic.eq_sym.
      solve_Parable2.
    }
  Qed.

  Program Definition G_core_package_construction
    (d k : nat) (H_lt : (d < k)%nat)
    G_check_XTR_XPD_f
    KeysAndHash_Kf
    KeysAndHash_Lf
    : package
        (L_K :|: L_L)
        [interface]
        (XPD_n d k
           :|: DH_interface
           :|: SET_ℓ [PSK] k 0
           :|: XTR_n d k
           :|: GET_n O_star d k) :=
    {package
       (par
          (G_check_XTR_XPD d k H_lt G_check_XTR_XPD_f)
          (par
             (G_dh d k (ltnW H_lt))
             (parallel_ID k [:: PSK]
                (fun n =>
                   [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                _ erefl _)
          )
       ) ∘ (KeysAndHash d k H_lt KeysAndHash_Kf KeysAndHash_Lf all_names erefl)
    }.
  Solve Obligations with intros ; solve_idents.
  Solve Obligations with intros
    ; now intros ? ? ?
    ; rewrite !in_fset !(mem_seq1 _ _)  => /eqP H
    ; inversion_clear H => /eqP H
    ; inversion_clear H.
  Next Obligation.
    intros.

    rewrite <- fset0U.
    eapply valid_link.
    1:{
      rewrite <- fset0U.
      replace
        (XPD_n d k :|: DH_interface :|: SET_ℓ [:: PSK] k 0 :|: XTR_n d k :|: GET_n O_star d k)
        with
        (XPD_n d k :|: XTR_n d k :|: GET_n O_star d k :|: (DH_interface :|: SET_ℓ [:: PSK] k 0)).
      2:{
        rewrite <- !fsetUA.
        f_equal.
        rewrite (fsetUC (GET_n _ _ _)).
        rewrite !fsetUA.
        f_equal.
        rewrite (fsetUC (XTR_n _ _)).
        rewrite <- !fsetUA.
        f_equal.
        rewrite fsetUC.
        reflexivity.
      }
      eapply valid_par.
      2: apply pack_valid.
      2:{
        rewrite <- fsetUid.
        eapply valid_par.
        2:apply pack_valid.
        2:apply pack_valid.
        shelve.
      }
      shelve.
    }
    {
      eapply valid_package_inject_export.
      2: apply pack_valid.
      now apply subset_all.
    }

    Unshelve.
    1:{
      unfold G_dh.
      unfold DH_package.
      unfold parallel_ID.
      unfold parallel_package.
      solve_Parable2.
    }
    1:{
      unfold G_check_XTR_XPD.
      unfold pack.
      unfold combined_ID.
      unfold G_check.
      unfold eq_rect.
      unfold eq_trans, f_equal.
      destruct functional_extensionality.
      unfold eq_rect_r, eq_rect.
      destruct Logic.eq_sym.
      unfold XPD_n_ℓ_f.
      unfold G_dh.
      unfold DH_package.
      unfold parallel_ID.
      unfold parallel_package.
      unfold combined_ID.
      unfold G_XTR_XPD.
      unfold XPD_packages.
      unfold XTR_packages.
      unfold pack.
      unfold eq_rect_r.
      unfold eq_rect.
      destruct Logic.eq_sym.
      destruct Logic.eq_sym.
      destruct Logic.eq_sym.
      solve_Parable2.
    }
  (* Time *) Qed.
  Fail Next Obligation.

  (** Page 70 *)
  Definition G_core_Hash (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun _ => false)
      (fun _ _ => false)
      (fun _ => Z).

  Definition G_core_D (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun _ => false)
      (fun _ _ => false)
      (fun _ => D).

  Definition G_core_R_esalt (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun _ => false)
      (fun _ _ => false)
      (fun name => match name with | ESALT => R | _ => D end).

  Definition G_core_SODH (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun name => match name with HS => true | _ => false end)
      (fun _ _ => false)
      (fun name => match name with | ESALT => R | _ => D end).

  Definition N_star :=
    [ES; EEM; CET; BIND; BINDER; HS; SHT; CHT; HSALT; AS; RM;
     CAT; SAT; EAM; ZERO_SALT; ESALT; ZERO_IKM].

  Lemma N_star_correct :
    (forall x, (x \in all_names /\ x \notin [PSK; DH]) <-> x \in N_star).
  Proof.
    intros.
    split.
    - intros [].
      rewrite !in_cons in H |- *.
      now repeat (move /orP: H => [/eqP ? | H] ; subst) ; [ subst .. | discriminate ].
    - intros.
      rewrite !in_cons in H |- *.
      now repeat (move /orP: H => [/eqP ? | H] ; subst) ; [ subst .. | discriminate ] ; simpl.
  Qed.

  Definition G_core_hyb_ℓ (d k : nat) (H_lt : (d < k)%nat) (i : nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun name => match name with HS => true | _ => false end)
      (fun ℓ name =>
         if (name \in N_star) || (name == PSK)
         then
           if (i <=? ℓ)%nat then false else true
         else false)
      (fun name => match name with | ESALT => R | _ => D end).

  (** Idealization order (hybridazation argument for a given level) *)

  Definition G_core_hyb_pred_ℓ_c
    (d k : nat) (H_lt : (d < k)%nat) (i : nat) (C : list name) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun name => match name with HS => true | _ => false end)
      (fun ℓ name =>
         if (name \in N_star) || (name == PSK)
         then
           if (i + (name \in C) <=? ℓ)%nat then false else true
         else false)
      (fun name => match name with | ESALT => R | _ => D end).

  Definition G_core_ki (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    G_core_package_construction d k H_lt
      (fun name => match name with HS => true | _ => false end)
      (fun _ _ => true)
      (fun name => D).

End Core.
