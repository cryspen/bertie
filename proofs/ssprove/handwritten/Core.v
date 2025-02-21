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

  Definition Gcore_sodh (d : nat) :
    package fset0
      ([interface
         #val #[ DHEXP ] : chDHEXPinp → chDHEXPout ;
         #val #[ DHGEN ] : chDHGENinp → chDHGENout
      ] :|: interface_hierarchy (fun ℓ => [interface #val #[ XTR HS ℓ d ] : chXTRinp → chXTRout]) d)
      [interface].
  Proof.
  Admitted.

  Definition Gcore_hyb : forall d (ℓ : nat),
      package f_parameter_cursor_loc
        ((GET_ℓ XPR d ℓ :|: SET_ℓ XPR d ℓ)
           :|: (GET_DH_ℓ d ℓ :|: SET_DH_ℓ d ℓ)
           :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout]
           :|: (GET_ℓ XTR_names d ℓ :|: SET_ℓ XTR_names d ℓ))
        (SET_O_star_ℓ d ℓ :|: GET_O_star_ℓ d ℓ).
  Proof.
    intros.
    epose {package (Ks ℓ d _ O_star false erefl ∘ Ls ℓ O_star F erefl)}.
    fold GET.
  Admitted.

  Definition Gcore_ki : forall d k,
      package f_parameter_cursor_loc
        ((GET_n XPR d k :|: SET_n XPR d k)
           :|: (GET_DH d k :|: SET_DH d k)
           :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout]
           :|: (GET_n XTR_names d k :|: SET_n XTR_names d k))
        (SET_O_star d k :|: GET_O_star d k).
  Proof.
    intros.
  Admitted.

  Axiom Hash : package fset0 [interface] [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout].
  Lemma trimmed_hash : (trimmed ([interface #val #[ HASH  f_hash ] : chHASHinp → chHASHout]) Hash). Admitted.

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

  Lemma xtr_dh : forall (d k : nat) H_lt,
    domm (pack (XTR_packages d k H_lt)) :#: domm (pack (DH_package d k)) = true.
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

  Lemma xpd_dh : forall (d k : nat) H_lt,
    domm (pack (XPD_packages d k H_lt)) :#: domm (pack (DH_package d k)) = true.
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

  Lemma subset_pair : forall {A : ordType} (x : {fset A}) y Lx Ly,
      x :<=: y ->
      Lx :<=: Ly ->
      x :|: Lx :<=: y :|: Ly.
  Proof.
    intros.
    rewrite fsubUset ; apply /andP ; split.
    * rewrite fsubsetU ; [ easy | ].
      apply /orP ; left.
      apply H.
    * rewrite fsubsetU ; [ easy | ].
      apply /orP ; right.
      apply H0.
  Qed.

  Lemma interface_foreach_subset_pairs : forall {A: eqType} f g (L : seq A),
      (forall (x : A), (x \in L) -> f x :<=: g x) ->
      interface_foreach f L :<=: interface_foreach g L.
  Proof.
    intros.
    induction L.
    + apply fsubsetxx.
    + rewrite !interface_foreach_cons.
      apply subset_pair.
      * apply H.
        apply mem_head.
      * apply IHL.
        intros.
        apply H.
        rewrite in_cons.
        now apply /orP ; right.
  Qed.

  Lemma interface_hierarchy_subset_pairs : forall f g d,
      (forall ℓ, (ℓ <= d)%nat -> f ℓ :<=: g ℓ) ->
      interface_hierarchy f d :<=: interface_hierarchy g d.
  Proof.
    intros.
    induction d.
    + now apply H.
    + simpl.
      apply subset_pair.
      * apply IHd.
        now intros ; apply H.
      * now apply H.
  Qed.

  Lemma interface_hierarchy_foreach_subset_pairs : forall {A: eqType} f g (L : seq A) d,
      (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: g x ℓ) ->
      interface_hierarchy_foreach f L d :<=: interface_hierarchy_foreach (A := A) g L d.
  Proof.
    intros.
    unfold interface_hierarchy_foreach.
    apply interface_hierarchy_subset_pairs.
    intros.
    now apply interface_foreach_subset_pairs.
  Qed.

  Lemma interface_foreach_subset : forall {A: eqType} f (L : seq A) K,
      (forall (x : A), (x \in L) -> f x :<=: K) ->
      interface_foreach f L :<=: K.
  Proof.
    intros.
    induction L.
    + simpl. rewrite <- fset0E. apply fsub0set.
    + rewrite interface_foreach_cons.
      rewrite fsubUset.
      apply /andP ; split.
      * apply H.
        apply mem_head.
      * apply IHL.
        intros.
        apply H.
        rewrite in_cons.
        now apply /orP ; right.
  Qed.

  Lemma interface_foreach_subsetR : forall {A: eqType} f (L : seq A) K,
      (exists (x : A) (H_in : x \in L), K :<=: f x) ->
      L <> [] ->
      K :<=: interface_foreach f L.
  Proof.
    intros.
    induction L ; [ easy | ].
      unfold interface_hierarchy.
      rewrite interface_foreach_cons.
      rewrite fsubsetU ; [ easy | ].
      apply /orP.

      destruct H as [? []].
      rewrite in_cons in x0.
      move: x0 => /orP [/eqP ? | x0 ] ; subst.
      + now left.
      + right.
        apply IHL.
        2: destruct L ; easy.
        exists x, x0.
        apply H.
  Qed.

  Lemma interface_hierarchy_foreach_subset : forall {A: eqType} f (L : seq A) d K,
      (forall (x : A), (x \in L) -> forall ℓ, (ℓ <= d)%nat -> f x ℓ :<=: K) ->
      interface_hierarchy_foreach f L d :<=: K.
  Proof.
    intros.
    unfold interface_hierarchy_foreach.
    induction d in H |- * at 1.
    - now apply interface_foreach_subset.
    - simpl.
      rewrite fsubUset.
      apply /andP ; split.
      + now apply IHn.
      + now apply interface_foreach_subset.
  Qed.

  Lemma interface_hierarchy_foreach_subsetR : forall {A: eqType} f (L : seq A) d K,
      (exists (x : A) (H_in : x \in L) ℓ (H_le : (ℓ <= d)%nat), K :<=: f x ℓ) ->
      L <> [] ->
      K :<=: interface_hierarchy_foreach f L d.
  Proof.
    intros.
    unfold interface_hierarchy_foreach.
    induction d in H |- * at 1.
    - destruct H as [? [? [? []]]].
      apply interface_foreach_subsetR.
      2: easy.
      exists x, x0.
      destruct x1 ; [ | easy ].
      apply H.
    - simpl.
      rewrite fsubsetU ; [ easy | ].
      apply /orP.

      destruct H as [? [? [? []]]].
      destruct (x1 == n.+1) eqn:x_eq ; move: x_eq => /eqP x_eq ; subst.
      + right.
        clear IHn.
        apply interface_foreach_subsetR.
        2: easy.
        exists x, x0.
        apply H.
      + left.
        apply IHn.
        exists x, x0, x1.
        eexists ; [ Lia.lia | ].
        apply H.
  Qed.

  Obligation Tactic := (* try timeout 8 *) idtac.

  Lemma interface_hierarchy_foreach_shift :
    forall d k {index p} L,
    interface_hierarchy_foreach (fun n ℓ => (fset [(serialize_name n ℓ k index, p)])) L d.+1 =
      interface_foreach (fun n => fset [(serialize_name n O k index, p)]) L
        :|: interface_hierarchy_foreach (fun n ℓ => fset [(serialize_name n (ℓ.+1) k index,p ) ]) L d
  .
  Proof.
    intros.
    induction d.
    - simpl. reflexivity.
    - unfold interface_hierarchy_foreach at 2.
      unfold interface_hierarchy ; fold interface_hierarchy.
      fold (interface_hierarchy_foreach (λ n ℓ, fset [(serialize_name n ℓ.+1 k index, p)]) L).
      rewrite fsetUA.
      rewrite fsetUC.
      rewrite <- IHd.
      rewrite fsetUC.
      reflexivity.
  Qed.

  Program Definition XPD_ d k H_lt : package (L_K :|: L_L) [interface] (XPD_n d k) :=
    {package
       XPD_packages d k H_lt ∘
       (par
          (Ks d.+1 k (H_lt) (undup (XPR ++ XPR_parents)) false erefl ∘ Ls k (undup (XPR ++ XPR_parents)) F erefl)
          Hash)
       #with _
    }.
  (* Next Obligation. *)
  (*   intros. *)
  (*   apply trimmed_package_cons. *)
  (*   apply trimmed_package_cons. *)
  (*   apply trimmed_empty_package. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   simpl. *)
  (*   rewrite fset_cons. *)
  (*   rewrite fdisjointC. *)
  (*   rewrite fset_cons. *)
  (*   unfold idents. *)
  (*   solve_imfset_disjoint. *)
  (* Qed. *)
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
        unfold GET_n.
        unfold GET_ℓ.
        fold (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ k] : chXTRout → chGETout ]) XPR_parents).

        eapply valid_package_inject_export.
        2: apply pack_valid.

        rewrite fsetUC.
        apply subset_pair.
        - rewrite fsubUset.
          apply /andP.
          split.
          + rewrite interface_hierarchy_foreach_shift.
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

  Program Definition XPD_DH_XTR d k H_lt :
    package
      (L_K :|: L_L)
      [interface]
      (XPD_n d k :|: (DH_interface :|: XTR_n d k)) :=
    {package
       (par
          (XPD_ d k H_lt)
          (par (DH_package d k ∘ (Ks d k (ltnW H_lt) [DH] false erefl ∘ Ls k [DH] F erefl))
             (XTR_packages d k (ltnW H_lt) ∘ (Ks d k (ltnW H_lt) (undup (XTR_names ++ XTR_parent_names)) false erefl ∘ Ls k (undup (XTR_names ++ XTR_parent_names)) Z erefl))))
       ∘ (Ks d k (ltnW H_lt) O_star false erefl ∘ Ls k O_star Z (erefl))}.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply valid_link.
    2: eapply valid_link ; apply pack_valid.

    (* rewrite <- trimmed_xpd_package. *)
    rewrite <- trimmed_dh.
    (* rewrite <- trimmed_hash. *)
    rewrite <- trimmed_xtr_package.

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

        unfold XTR_n.
        unfold DH_interface.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        rewrite fset_cons.
        unfold idents.
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
        apply idents_disjoint_foreach_in.
        intros.
        rewrite fdisjointC.
        apply idents_disjoint_foreach_in.
        intros.
        unfold idents.
        solve_imfset_disjoint.

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
      (* rewrite !fset0U. *)
      (* fold SET_O_star_ℓ. *)
      (* fold GET_O_star_ℓ. *)

      (* apply required_O_subset. *)
    }
    apply fsubsetxx.
  Defined.

  Obligation Tactic := (* try timeout 8 *) idtac.
  Program Definition Gcore_real (d k : nat) H_lt :
    package (L_K :|: L_L)
            [interface]
      (* ((GET_XPD :|: SET_XPD) *)
      (*     :|: DH_Set_interface *)
      (*     :|: [interface #val #[ HASH ] : chHASHinp → chHASHout] *)
      (*    :|: (GET_XTR :|: SET_XTR)) *)
      ((* SET_O_star_ℓ d :|:  *) GET_O_star d k)
    (* ([interface #val #[SET_psk 0] : chSETinp → chSETout ; *)
    (*   #val #[DHGEN] : 'unit → 'unit ; *)
    (*   #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: XPD_n_ℓ d :|:  *)
    (*    GET_o_star_ℓ d) *)
    :=
    {package (Ks d k (ltnW H_lt) O_star false erefl ∘ Ls k O_star F erefl) ∘ XPD_DH_XTR d k H_lt}.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply valid_link.
    2: apply XPD_DH_XTR.
    eapply valid_link.
    - eapply valid_package_inject_export.
      2: apply (Ks _ _ _).
      unfold GET_O_star.
      apply fsubsetU.
      apply /orP.
      right.
      apply fsubsetxx.
    - eapply valid_package_inject_import.
      2: apply (Ls _ _ _).
      rewrite <- fset0E.
      solve_in_fset.
  Defined.
  Fail Next Obligation.

  Program Definition Gcore_ideal (d k : nat) H_lt (Score : Simulator d k) :
    package
      L_K
      ([interface
          #val #[ SET PSK 0 d ] : chSETinp → chSETout
        ] :|: DH_interface :|:
         XTR_n d k :|:
         XPD_n d k :|:
         GET_O_star d k)
      (GET_O_star d k) :=
    {package (Ks d k H_lt O_star true erefl ∘ Score) }.
  Final Obligation.
    intros.
    rewrite <- fsetUid.
    eapply (valid_link_upto L_K _ _ _ (UNQ_O_star k)).
    - epose (pack_valid (Ks d k H_lt O_star true erefl)).
      eapply valid_package_inject_export.
      2: apply v.
      unfold GET_O_star.
      solve_in_fset.
    - eapply valid_package_inject_import.
      2: apply (pack_valid Score).
      solve_in_fset.
    - solve_in_fset.
    - solve_in_fset.
  Defined.
  Fail Next Obligation.

End Core.
