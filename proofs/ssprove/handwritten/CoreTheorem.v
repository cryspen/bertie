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

  Definition Gacr (f : HashFunction) (b : bool) :
    package fset0
      [interface]
      [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout].
  Proof.
    (* refine [package *)
    (*           #def #[ HASH ] (t : chHASHinp) : chHASHout { *)
    (*             (* get_or_fn _ _ _ *) *)
    (*             d ← untag (f t) ;; *)
    (*             if b && d \in Hash *)
    (*             then fail *)
    (*             else Hash *)
    (*           } *)
    (*   ]. *)
    (* Qed. *)
  Admitted.

  (* Definition Gacr : *)
  (*   loc_GamePair *)
  (*     [interface *)
  (*        (* #val #[ ACR ] : 'unit → 'unit *) *)
  (*     ]. *)
  (* (* HASH(t) .. *) *)

  Definition R_cr :
    package fset0
      [interface]  (* #val #[ HASH ] : chHASHinp → chHASHout] *)
      [interface].
  Proof.
  Admitted.

  Definition R_Z (f : HashFunction) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Axiom R_D : package fset0 [interface] [interface].

  Axiom Gsodh :
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Ai : raw_package -> bool -> raw_package.
  Axiom R_sodh : package fset0 [interface] [interface].

  (* Definition Nk_package (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) : *)
  (*   package *)
  (*     L_K *)
  (*     [interface *)
  (*        #val #[ UNQ DH d ] : chUNQinp → chUNQout ; *)
  (*        #val #[ SET DH ℓ d ] : chSETinp → chSETout *)
  (*     ] *)
  (*     [interface *)
  (*        #val #[ GET DH ℓ d ] : chGETinp → chGETout *)
  (*     ]. *)

  Obligation Tactic := (* try timeout 8 *) idtac.
  Program Definition layer1 ℓ d (H_le : (ℓ <= d)%nat) :
    package fset0
      [interface]
      [interface
         #val #[ GET DH ℓ d ] : chGETinp → chGETout
      ] :=
    {package Nk_package ℓ d H_le ∘ (par (DH_package d d) (Ls d [DH] Z erefl)) #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_zero d k H_lt :
    package fset0
      [interface
         #val #[ SET PSK O k ] : chSETinp → chSETout
      ]
      [interface
         #val #[ GET PSK O k ] : chGETinp → chGETout
      ] :=
    {package Ks d k H_lt [PSK] false erefl ∘ Ls k [PSK] Z erefl #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_succ ℓ d k H_lt (H_le : (ℓ <= d)%nat) :
    package fset0
      [interface
         #val #[ SET PSK ℓ d ] : chSETinp → chSETout
      ]
      [interface
         #val #[ GET PSK ℓ d ] : chGETinp → chGETout
      ] :=
    {package Ks d k H_lt [PSK] false erefl ∘ Ls d [PSK] Z erefl #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_xpd ℓ k H_lt :
    package (L_K :|: L_L)
      [interface]
      (XPD_n_ℓ k ℓ) :=
    XPD_ ℓ k H_lt.
  Fail Next Obligation.

  Definition layer3 ℓ d (H_le : (ℓ <= d)%nat) := Hash.

  Program Definition layer4_salt d k H_lt :
    package (L_K :|: L_L)
      [interface]
      (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_SALT ℓ k ] : chGETinp → chGETout]) d) :=
    {package Ks d k H_lt [ZERO_SALT] false erefl ∘ Ls k [ZERO_SALT] Z erefl #with _}.
  Next Obligation.
    intros.
    eapply valid_link.
    2: apply pack_valid.

    eapply valid_package_inject_export.
    2: apply pack_valid.
    apply fsubsetU.
    apply /orP ; right.
    unfold interface_hierarchy_foreach.
    unfold interface_foreach.
    apply fsubsetxx.
  Qed.
  Fail Next Obligation.

  Program Definition layer4_ikm d k H_lt :
    package (L_K :|: L_L)
      [interface]
      (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_IKM ℓ k ] : chGETinp → chGETout]) d) :=
    {package Ks d k H_lt [ZERO_IKM] false erefl ∘ Ls k [ZERO_IKM] Z erefl #with _}.
    Next Obligation.
    intros.
    eapply valid_link.
    2: apply pack_valid.

    eapply valid_package_inject_export.
    2: apply pack_valid.
    apply fsubsetU.
    apply /orP ; right.
    unfold interface_hierarchy_foreach.
    unfold interface_foreach.
    apply fsubsetxx.
  Qed.
  Fail Next Obligation.

  Program Definition layer4_xtr ℓ d H_le :
    package fset0
      (XTR_n_ℓ d ℓ :|: GET_ℓ XTR_names d ℓ)
      (SET_ℓ XTR_names d ℓ) := xtr_level d ℓ H_le.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_check d k :
    package fset0
      (XPD_n d k)
      (XPD_n d k :|: interface_hierarchy (fun ℓ => [interface #val #[ GET BINDER ℓ d ] : chGETinp → chGETout ]) d) := _.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_xpd d k H_lt :
    package fset0
      (XPD_n d k :|: SET_n XPR d k)
      (GET_n XPR d k) := {package XPD_packages d k H_lt ∘ layer4_check d k #with _}.
  Admit Obligations.
  Fail Next Obligation.

  Definition core (d k : nat) (H_lt : (d < k)%nat) : package fset0
                              (interface_hierarchy (fun x => [interface]) d)
                              (GET_O_star d k).
  Proof.
  Admitted.

  (*   refine {package (pack _) #with valid_package_inject_export _ _ _ (GET_n all_names d k :|: SET_n all_names d k) _ _ _}. *)
  (*   2:{ *)
  (*     unfold GET_O_star. *)
  (*     unfold GET_n. *)
  (*     unfold SET_n. *)
  (*     rewrite interface_hierarchy_foreachU. *)

  (*     apply interface_hierarchy_foreach_subset. *)
  (*     intros. *)
  (*     apply interface_hierarchy_foreach_subsetR. *)
  (*     2: easy. *)
  (*     exists x. *)
  (*     assert (x \in all_names). *)
  (*     { *)
  (*       clear -H. *)
  (*       rewrite !in_cons in H. *)
  (*       unfold all_names. *)
  (*       rewrite !in_cons. *)
  (*       repeat (move: H => /orP [ /eqP ? | H ]) ; [ subst.. | discriminate ]. *)
  (*       all: now rewrite eqxx. *)
  (*     } *)
  (*     exists H1. *)
  (*     exists ℓ, H0. *)
  (*     apply fsubsetUl. *)
  (*   } *)

  (*   unfold GET_n. *)
  (*   unfold SET_n. *)
  (*   rewrite interface_hierarchy_foreachU. *)

  (*   refine (ℓ_packages d _ _ _). *)
  (*   (* 2:{ *) *)
  (*   (*   intros. *) *)
  (*   (*   apply idents_foreach_disjoint_foreach. *) *)
  (*   (*   intros. *) *)
  (*   (*   unfold idents. *) *)
  (*   (*   solve_imfset_disjoint. *) *)
  (*   (* } *) *)
    
  (*   Unshelve. *)
  (*   3:{ *)
  (*     intros n H. *)
      
  (*     epose (dh := layer1 n d H). *)
  (*     epose proof (layer2_xpd n k (ltac:(Lia.lia))). *)
  (*     epose (hash := layer3 n d H). *)
  (*     epose (salt0 := layer4_salt d k (ltnW H_lt)). *)
  (*     epose (ikm0 := layer4_ikm d k (ltnW H_lt)). *)
  (*     epose (check := layer4_check d k). *)
  (*     epose (xtr := layer4_xtr n d H). *)
  (*     epose (xpd := layer4_xpd d k H_lt). *)

  (*     epose (T := package fset0 *)
  (*                   [interface] *)
  (*                   (match n with *)
  (*                    | O => [interface] *)
  (*                    | S n => (interface_foreach (λ name, [interface #val #[GET name n k] : chDHEXPout → chGETout ] :|: [interface #val #[SET name n k] : chSETinp → chSETout ]) all_names) *)
  (*                    end)). *)

  (*     epose (set_xtr := fun psk (sub_packages : T) => {package *)
  (*                          xtr ∘ *)
  (*                          parallel_raw [ *)
  (*                            pack dh; *)
  (*                            pack psk; *)
  (*                            pack hash; *)
  (*                            pack salt0; *)
  (*                            pack ikm0; *)
  (*                            pack sub_packages] *)
  (*                          #with _} : package fset0 [interface] (SET_ℓ XTR_names k n)). *)
  (*     (* Unshelve. *) *)
  (*     (* { *) *)

  (*     (* } *) *)
      
  (*     epose (set_xpd := fun psk (sub_packages : T) => {package *)
  (*                          xpd ∘ *)
  (*                          parallel_raw [ *)
  (*                            pack dh; *)
  (*                            pack psk; *)
  (*                            pack hash; *)
  (*                            pack salt0; *)
  (*                            pack ikm0; *)
  (*                            pack sub_packages] *)
  (*                          #with _} : package fset0 [interface] (SET_ℓ XPR k n)). *)

  (*     (* epose (output := fun psk sub_packages => {package Ks d O_star false erefl ∘ *) *)
  (*     (*                                             (parallel_raw [ *) *)
  (*     (*                                                  pack (set_xtr psk sub_packages); *) *)
  (*     (*                                                  pack (set_xpd psk sub_packages); *) *)
  (*     (*                                                  pack (Ls d O_star Z _)]) #with _}). *) *)
  (*     epose (output := fun psk *)
  (*                        (sub_packages : T) => *)
  (*                        {package (parallel_package d all_names (fun name => K_package k name n _ false) _ _ _) ∘ *)
  (*                           (parallel_raw [ *)
  (*                                pack (set_xtr psk sub_packages); *)
  (*                                pack (set_xpd psk sub_packages); *)
  (*                                pack (Ls d all_names Z _)]) #with _}). *)


  (*     assert (package fset0 *)
  (*               [interface] *)
  (*               (interface_foreach (λ name, *)
  (*                    [interface #val #[GET name n k] : chDHEXPout → chGETout ] :|: [interface #val #[SET name n k] : chSETinp → chSETout ]) all_names)). *)
  (*     { *)
  (*       induction n as [ | ℓ ]. *)
  (*       - epose (psk0 := layer2_zero d k (ltnW H_lt)). *)
  (*         refine (output psk0 _). *)
  (*         refine {package emptym #with valid_empty_package _ _}. *)
  (*       - epose (pskS := layer2_succ (S ℓ) k k (leqnn k) _). *)
  (*         refine (output pskS _). *)
  (*         specialize (IHℓ (leq_trans H (leqnSn _))). *)
  (*         unfold T. *)
  (*         eapply IHℓ. *)
  (*     } *)

  (*     refine {package X0 #with _}. *)
  (*   } *)
  (*   { *)
  (*     intros. *)
  (*     unfold pack. *)
  (*     destruct n. *)
  (*     - unfold nat_rect. *)
  (*       eassert (forall n l d H0 H1, trimmed _ (K_package d n l H0 H1)). *)
  (*       { *)
  (*         intros. *)
  (*         apply trimmed_package_cons. *)
  (*         apply trimmed_package_cons. *)
  (*         apply trimmed_empty_package. *)
  (*       } *)
  (*       unfold parallel_package. *)
  (*       rewrite <- (trimmed_parallel_raw (f := (λ n : name, *)
  (*         [interface #val #[GET n 0 k] : chDHEXPout → chGETout ] *)
  (*         :|: [interface #val #[SET n 0 k] : chUNQinp → chDHEXPout ])) (I := all_names)). *)
  (*       { *)
  (*         rewrite !link_trim_commut. *)
  (*         apply trimmed_trim. *)
  (*       } *)
  (*       { *)
  (*         intros. *)
  (*         unfold idents. *)
  (*         try rewrite !imfsetU *)
  (*         ; try rewrite !fdisjointUr *)
  (*         ; try rewrite !fdisjointUl *)
  (*         ; try rewrite  <- !fset1E *)
  (*         ; try rewrite !imfset1 *)
  (*         ; try rewrite !fdisjoints1 *)
  (*         ; repeat (apply /andP ; split) *)
  (*         ; try (rewrite (ssrbool.introF (fset1P _ _)) ; [ reflexivity | ]). *)
  (*         all : try (now apply serialize_name_notin_all ; (now left ; split ; [ reflexivity | ((now right) || (now left)) ]) || (now right ; split ; [ discriminate | split ; [ Lia.lia | Lia.lia ] ])). *)
  (*         (* solve_imfset_disjoint. *) *)
  (*       } *)
  (*       { *)
  (*         reflexivity. *)
  (*       } *)
  (*       { *)
  (*         apply trimmed_pairs_map. *)
  (*         intros. *)
  (*         rewrite <- H. *)
  (*         set (K_package _ _ _ _ _). *)
  (*         rewrite fsetUC. *)
  (*         rewrite <- fset1E. *)
  (*         rewrite <- fset_cons. *)
  (*         apply trimmed_trim. *)
  (*       } *)
  (*     - unfold nat_rect. *)
  (*       eassert (forall n l d H0 H1, trimmed _ (K_package d n l H0 H1)). *)
  (*       { *)
  (*         intros. *)
  (*         apply trimmed_package_cons. *)
  (*         apply trimmed_package_cons. *)
  (*         apply trimmed_empty_package. *)
  (*       } *)
  (*       unfold parallel_package. *)
  (*       rewrite <- (trimmed_parallel_raw (f := (λ n0 : name, *)
  (*         [interface #val #[GET n0 n.+1 k] : chDHEXPout → chGETout ] *)
  (*         :|: [interface #val #[SET n0 n.+1 k] : chUNQinp → chDHEXPout ])) (I := all_names)). *)
  (*       { *)
  (*         rewrite !link_trim_commut. *)
  (*         apply trimmed_trim. *)
  (*       } *)
  (*       { *)
  (*         intros. *)
  (*         unfold idents. *)
  (*         try rewrite !imfsetU *)
  (*         ; try rewrite !fdisjointUr *)
  (*         ; try rewrite !fdisjointUl *)
  (*         ; try rewrite  <- !fset1E *)
  (*         ; try rewrite !imfset1 *)
  (*         ; try rewrite !fdisjoints1 *)
  (*         ; repeat (apply /andP ; split) *)
  (*         ; try (rewrite (ssrbool.introF (fset1P _ _)) ; [ reflexivity | ]). *)
  (*         all : try (now apply serialize_name_notin_all ; (now left ; split ; [ reflexivity | ((now right) || (now left)) ]) || (now right ; split ; [ discriminate | split ; [ Lia.lia | Lia.lia ] ])). *)
  (*         (* solve_imfset_disjoint. *) *)
  (*       } *)
  (*       { *)
  (*         reflexivity. *)
  (*       } *)
  (*       { *)
  (*         apply trimmed_pairs_map. *)
  (*         intros. *)
  (*         rewrite <- H. *)
  (*         set (K_package _ _ _ _ _). *)
  (*         rewrite fsetUC. *)
  (*         rewrite <- fset1E. *)
  (*         rewrite <- fset_cons. *)
  (*         apply trimmed_trim. *)
  (*       } *)
  (*   } *)
  (*   { *)
  (*     intros. *)
  (*     apply idents_foreach_disjoint_foreach. *)
  (*     intros. *)
  (*     unfold idents. *)
  (*     solve_imfset_disjoint. *)
  (*   } *)

  (*   Unshelve. *)
  (*   { *)
  (*     ssprove_valid. *)
  (*     1:{ *)
  (*       eapply valid_package_inject_import. *)
  (*       2:{ *)
  (*         unfold XTR_n_ℓ. *)
  (*         unfold GET_ℓ. *)
  (*         rewrite interface_foreach_U. *)

  (*         unfold parallel_raw, List.fold_left. *)
  (*         unfold XTR_names, interface_foreach. *)

  (*         (* apply (valid_parable [:: pack dh; pack psk; pack hash; pack salt0; pack ikm0; pack sub_packages]). *) *)
          
  (*         ssprove_valid. *)
  (*         all: try apply fsubsetxx. *)
  (*         1-5: admit. *)
  (*         admit. *)
  (*       } *)
  (*       rewrite <- !fset0E. *)
  (*       rewrite !fsetU0 ; rewrite !fset0U. *)
  (*       admit. *)
  (*     } *)
  (*     { *)
  (*       apply fsubsetxx. *)
  (*     } *)
  (*     { *)
  (*       rewrite !fsetU0 ; rewrite !fset0U. *)
  (*       rewrite fsetUid. *)
  (*       admit. *)
  (*     } *)
  (*   } *)
  (*   all: admit. *)
  (* Admitted. *)

  Lemma core_theorem :
    forall (d k : nat) H_lt,
    forall (Score : Simulator d k),
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE
         (Gcore_real d k H_lt)
         (Gcore_ideal d k (ltnW H_lt) Score) (A (* ∘ R d M H *))
       <= sumR_l [R_cr; (R_Z f_hash); R_D] (fun R => Advantage (Gacr f_hash) (A ∘ R))
         +maxR (fun i => Advantage Gsodh (Ai A i ∘ R_sodh) + AdvantageE (Gcore_sodh d) (Gcore_ideal d k (ltnW H_lt) Score) (Ai A i))
      )%R.
  Proof.
    intros.
    unfold sumR_l.
    rewrite addr0.
    rewrite addrA.

    unfold Gcore_real.
    unfold pack.

    epose Advantage_link.

    (* unfold Gacr. *)
    (* simpl. *)
    (* simpl. *)
  Admitted.

  Lemma equation20_lhs :
    forall (d k : nat),
    forall (Score : Simulator d k),
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (Gcore_sodh d) (Gcore_hyb d 0) (Ai A i) = 0)%R.
  Proof.
    intros.
  Admitted.

  Lemma equation20_rhs :
    forall (d k : nat),
    forall (Score : Simulator d k),
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (Gcore_ki d k) (Gcore_hyb d d) (Ai A i) = 0)%R.
  Proof.
    intros.
  Admitted.

  Lemma hyb_telescope :
    forall (d k : nat),
    forall (Score : Simulator d k),
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (Gcore_hyb d 0) (Gcore_hyb d d) (Ai A i)
       = sumR 0 d (leq0n d) (fun ℓ => AdvantageE (Gcore_hyb d ℓ) (Gcore_hyb d (ℓ+1)) (Ai A i))
      )%R.
  Proof.
    intros.
    set (d) at 1 2 6 7.
    generalize dependent n.
    induction d ; intros.
    - unfold sumR.
      simpl.
      unfold AdvantageE.
      rewrite subrr.
      rewrite Num.Theory.normr0.
      reflexivity.
    - rewrite sumR_succ.
      (* unfold Gcore_hyb. *)
  Admitted.

  Lemma equation20_eq :
    forall (d k : nat) H_lt,
    forall (Score : Simulator d k),
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (Gcore_sodh d) (Gcore_ideal d k H_lt Score) (Ai A i)
       <= AdvantageE (Gcore_ki d k) (Gcore_ideal d k H_lt Score) (Ai A i)
         +sumR 0 d (leq0n d) (fun ℓ => AdvantageE (Gcore_hyb d ℓ) (Gcore_hyb d (ℓ + 1)) (Ai A i))
      )%R.
  Proof.
    intros.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (Gcore_hyb d 0)).
    rewrite (equation20_lhs d k Score).
    rewrite add0r.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := Gcore_ki d k).
    rewrite addrC.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (Gcore_hyb d d)).

    epose (e := equation20_rhs d k Score).
    setoid_rewrite (Advantage_sym _ _) in e.
    rewrite e ; clear e.
    rewrite addr0.

    setoid_rewrite <- hyb_telescope ; easy.
  Qed.

End CoreTheorem.
