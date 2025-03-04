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
(* From KeyScheduleTheorem Require Import MapPackage. *)

(*** Core theorem *)

Section CoreTheorem.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  (* Definition Gcore_hyb : forall d (ℓ : nat), *)
  (*     package f_parameter_cursor_loc *)
  (*       ((GET_ℓ XPR d ℓ :|: SET_ℓ XPR d ℓ) *)
  (*          :|: (GET_DH_ℓ d ℓ :|: SET_DH_ℓ d ℓ) *)
  (*          :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout] *)
  (*          :|: (GET_ℓ XTR_names d ℓ :|: SET_ℓ XTR_names d ℓ)) *)
  (*       (SET_O_star_ℓ d ℓ :|: GET_O_star_ℓ d ℓ). *)
  (* Proof. *)
  (*   intros. *)
  (*   epose {package (Ks ℓ d _ O_star false erefl ∘ Ls ℓ O_star (fun x => F) erefl)}. *)
  (*   fold GET. *)
  (* Admitted. *)

  (* Definition Gcore_ki : forall d k, *)
  (*     package f_parameter_cursor_loc *)
  (*       ((GET_n XPR d k :|: SET_n XPR d k) *)
  (*          :|: (GET_DH d k :|: SET_DH d k) *)
  (*          :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout] *)
  (*          :|: (GET_n XTR_names d k :|: SET_n XTR_names d k)) *)
  (*       (SET_O_star d k :|: GET_O_star d k). *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  Axiom hash : nat -> nat.
  Definition Gacr (f : HashFunction) (b : bool) :
    package fset0
      [interface]
      [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout].
  (* Proof. *)
  (*   refine [package *)
  (*             #def #[ HASH ] (t : chHASHinp) : chHASHout { *)
  (*               ret fail *)
  (*               (* (* get_or_fn _ _ _ *) *) *)
  (*               (* d ← untag (match f with | f_hash | f_xtr => xtr t end) ;; *) *)
  (*               (* if b && d \in Hash *) *)
  (*               (* then fail *) *)
  (*               (* else *) *)
  (*               (*   ret d *) *)
  (*             } *)
  (*     ]. *)
  (*   Qed. *)
  Admitted.

  (* Definition Gacr : *)
  (*   loc_GamePair *)
  (*     [interface *)
  (*        (* #val #[ ACR ] : 'unit → 'unit *) *)
  (*     ]. *)
  (* (* HASH(t) .. *) *)

  Definition R_alg :
    package fset0
      [interface]  (* #val #[ HASH ] : chHASHinp → chHASHout] *)
      [interface].
  Proof.
  Admitted.

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

  Definition R_D (f : HashFunction) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition R_xtr (n : name) (ℓ : nat) :
    n \in XTR_names ->
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition R_xpd (n : name) (ℓ : nat) :
    n \in XPR ->
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition R_pi (L : list name) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Axiom Gsodh :
    forall (d k : nat),
      (d < k)%nat ->
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Gxtr :
    forall (d k : nat),
      (d < k)%nat ->
      forall (n : name) (ℓ : nat),
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Gxpd :
    forall (d k : nat),
      (d < k)%nat ->
      forall (n : name) (ℓ : nat),
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Gpi :
    forall (d k : nat),
      (d < k)%nat ->
      forall (L : list name)
      (f : ZAF),
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Ai : raw_package -> bool -> raw_package.
  Axiom R_sodh : package fset0 [interface] [interface].

  Obligation Tactic := (* try timeout 8 *) idtac.
  (* Program Definition layer1 ℓ d (H_le : (ℓ <= d)%nat) : *)
  (*   package fset0 *)
  (*     [interface] *)
  (*     [interface *)
  (*        #val #[ GET DH ℓ d ] : chGETinp → chGETout *)
  (*     ] := *)
  (*   {package Nk_package ℓ d H_le ∘ (par (DH_package d) (Ls d [DH] Z erefl)) #with _ }. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer2_zero d k H_lt : *)
  (*   package fset0 *)
  (*     [interface *)
  (*        #val #[ SET PSK O k ] : chSETinp → chSETout *)
  (*     ] *)
  (*     [interface *)
  (*        #val #[ GET PSK O k ] : chGETinp → chGETout *)
  (*     ] := *)
  (*   {package Ks d k H_lt [PSK] false erefl ∘ Ls k [PSK] Z erefl #with _ }. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer2_succ ℓ d k H_lt (H_le : (ℓ <= d)%nat) : *)
  (*   package fset0 *)
  (*     [interface *)
  (*        #val #[ SET PSK ℓ d ] : chSETinp → chSETout *)
  (*     ] *)
  (*     [interface *)
  (*        #val #[ GET PSK ℓ d ] : chGETinp → chGETout *)
  (*     ] := *)
  (*   {package Ks d k H_lt [PSK] false erefl ∘ Ls d [PSK] Z erefl #with _ }. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer2_xpd ℓ k H_lt : *)
  (*   package (L_K :|: L_L) *)
  (*     [interface] *)
  (*     (XPD_n_ℓ k ℓ) := *)
  (*   XPD_ ℓ k H_lt. *)
  (* Fail Next Obligation. *)

  (* Definition layer3 ℓ d (H_le : (ℓ <= d)%nat) := Hash. *)

  (* Program Definition layer4_salt d k H_lt : *)
  (*   package (L_K :|: L_L) *)
  (*     [interface] *)
  (*     (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_SALT ℓ k ] : chGETinp → chGETout]) d) := *)
  (*   {package Ks d k H_lt [ZERO_SALT] false erefl ∘ Ls k [ZERO_SALT] Z erefl #with _}. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   eapply valid_link. *)
  (*   2: apply pack_valid. *)

  (*   eapply valid_package_inject_export. *)
  (*   2: apply pack_valid. *)
  (*   apply fsubsetU. *)
  (*   apply /orP ; right. *)
  (*   unfold interface_hierarchy_foreach. *)
  (*   unfold interface_foreach. *)
  (*   apply fsubsetxx. *)
  (* Qed. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer4_ikm d k H_lt : *)
  (*   package (L_K :|: L_L) *)
  (*     [interface] *)
  (*     (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_IKM ℓ k ] : chGETinp → chGETout]) d) := *)
  (*   {package Ks d k H_lt [ZERO_IKM] false erefl ∘ Ls k [ZERO_IKM] Z erefl #with _}. *)
  (*   Next Obligation. *)
  (*   intros. *)
  (*   eapply valid_link. *)
  (*   2: apply pack_valid. *)

  (*   eapply valid_package_inject_export. *)
  (*   2: apply pack_valid. *)
  (*   apply fsubsetU. *)
  (*   apply /orP ; right. *)
  (*   unfold interface_hierarchy_foreach. *)
  (*   unfold interface_foreach. *)
  (*   apply fsubsetxx. *)
  (* Qed. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer4_xtr ℓ d b H_le : *)
  (*   package fset0 *)
  (*     (XTR_n_ℓ d ℓ :|: GET_ℓ XTR_names d ℓ) *)
  (*     (SET_ℓ XTR_names d ℓ) := xtr_level d ℓ b H_le. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer4_check d k : *)
  (*   package fset0 *)
  (*     (XPD_n d k) *)
  (*     (XPD_n d k :|: interface_hierarchy (fun ℓ => [interface #val #[ GET BINDER ℓ d ] : chGETinp → chGETout ]) d) := _. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Program Definition layer4_xpd d k H_lt : *)
  (*   package fset0 *)
  (*     (XPD_n d k :|: SET_n XPR d k) *)
  (*     (GET_n XPR d k) := {package XPD_packages d k H_lt ∘ layer4_check d k #with _}. *)
  (* Admit Obligations. *)
  (* Fail Next Obligation. *)

  (* Lemma interface_foreach_cat : forall {A} f L1 L2, *)
  (*     interface_foreach f (L1 ++ L2) = *)
  (*     interface_foreach (A := A) f L1 :|: interface_foreach (A := A) f L2. *)
  (* Proof. *)
  (*   induction L1 ; intros. *)
  (*   - simpl. *)
  (*     rewrite <- fset0E. *)
  (*     rewrite fset0U. *)
  (*     reflexivity. *)
  (*   - rewrite interface_foreach_cons. *)
  (*     rewrite <- fsetUA. *)
  (*     rewrite <- IHL1. *)
  (*     now rewrite <- interface_foreach_cons. *)
  (* Qed. *)

  (* Definition xpd_xpr_approximation *)
  (*   (d k : nat) (b : bool) (H_lt : (d < k)%nat) : *)
  (*   package (L_K :|: L_L) *)
  (*     [interface] *)
  (*     (XPD_n d k :|: XTR_n d k). *)
  (* Proof. *)
  (*   refine ({package par (XPD_ d k H_lt) (XTR_ d k b (ltnW H_lt))}). *)
  (*   unfold XPD_, XTR_. *)
  (*   unfold pack. *)

  (*   eapply valid_par_upto. *)
  (*   2: apply XPD_. *)
  (*   2: apply XTR_. *)
  (*   2:{ *)
  (*     rewrite fsetUid. *)
  (*     apply fsubsetxx. *)
  (*   } *)
  (*   3: apply fsubsetxx. *)
  (*   2:{ *)
  (*     rewrite <- fset0E. *)
  (*     rewrite fsetU0. *)
  (*     apply fsub0set. *)
  (*   } *)
  (*   rewrite <- trimmed_xpd_package. *)
  (*   rewrite <- trimmed_xtr_package. *)
  (*   rewrite !link_trim_commut. *)
  (*   solve_Parable. *)
  (*   unfold XPD_n, XTR_n. *)
  (*   apply idents_interface_hierachy3. *)
  (*   intros. *)
  (*   rewrite fdisjointC. *)
  (*   apply idents_interface_hierachy3. *)
  (*   intros. *)
  (*   unfold idents. *)
  (*   solve_imfset_disjoint. *)
  (* Defined. *)

  (* Definition core_approximation *)
  (*   (d k : nat) (b : bool) (H_lt : (d < k)%nat) : *)
  (*   package (L_K :|: L_L) *)
  (*     (GET_n O_star d k) *)
  (*     (XPD_n d k :|: XTR_n d k). *)
  (* Proof. *)
  (*   (* epose (Ks d k (ltnW H_lt) O_star false erefl). *) *)

  (*   refine ({package (par *)
  (*      (XPD_packages d k H_lt *)
  (*       ∘ par *)
  (*           (Ks d.+1 k H_lt (undup (XPR ++ XPR_parents)) false erefl *)
  (*            ∘ Ls k (undup (XPR ++ XPR_parents)) F erefl) Hash) *)
  (*      (XTR_packages d k b (ltnW (m:=d) (n:=k) H_lt) *)
  (*       ∘ Ks d k (ltnW (m:=d) (n:=k) H_lt) (undup (XTR_parent_names ++ XTR_names)) false erefl *)
  (*         ∘ Ls k (undup (XTR_parent_names ++ XTR_names)) Z erefl))}). *)
  (*   unfold XPD_, XTR_. *)
  (*   unfold pack. *)

  (*   eapply valid_par_upto. *)
  (*   2: apply XPD_. *)
  (*   2: apply XTR_. *)
  (*   2:{ *)
  (*     rewrite fsetUid. *)
  (*     apply fsubsetxx. *)
  (*   } *)
  (*   3: apply fsubsetxx. *)
  (*   2:{ *)
  (*     rewrite <- fset0E. *)
  (*     rewrite fsetU0. *)
  (*     apply fsub0set. *)
  (*   } *)
  (*   rewrite <- trimmed_xpd_package. *)
  (*   rewrite <- trimmed_xtr_package. *)
  (*   rewrite !link_trim_commut. *)

  (*   solve_Parable. *)
  (*   unfold XPD_n, XTR_n. *)
  (*   apply idents_interface_hierachy3. *)
  (*   intros. *)
  (*   rewrite fdisjointC. *)
  (*   apply idents_interface_hierachy3. *)
  (*   intros. *)
  (*   unfold idents. *)
  (*   solve_imfset_disjoint. *)
  (* Defined. *)

  (* Definition core (d k : nat) (b : bool) (H_lt : (d < k)%nat) : *)
  (*   package fset0 *)
  (*     (interface_hierarchy (fun x => [interface]) d) *)
  (*     (GET_O_star d k). *)
  (* Proof. *)
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
  (*     epose (xtr := layer4_xtr n d b H). *)
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
  (*     Show Proof. *)
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
  (*         (* set (parallel_raw _). *) *)
  (*         rewrite (* ! *)link_trim_commut. *)
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

  Notation " 'chXTRinp' " :=
    (chHandle × chHandle)
      (in custom pack_type at level 2).
  Notation " 'chXTRout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  (* Page 70 *)
  Program Definition G_core_Hash (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun _ => false) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => false) erefl ∘ Ls k all_names (fun _ => Z) erefl) (K_package k PSK d H_lt false ∘ L_package k PSK Z)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition G_core_D (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun _ => false) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => false) erefl ∘ Ls k all_names (fun _ => D) erefl) (K_package k PSK d H_lt false ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition G_core_R_esalt (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun _ => false) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => false) erefl ∘ Ls k all_names (fun name => match name with | ESALT => R | _ => D end) erefl) (K_package k PSK d H_lt false ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition G_core_SODH (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    (* Gcore_sodh d k false. *)
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun name => match name with HS => true | _ => false end) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => false) erefl ∘ Ls k all_names (fun name => match name with | ESALT => R | _ => D end) erefl) (K_package k PSK d H_lt false ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  HB.instance Definition _ : Equality.axioms_ name :=
    {|
      Equality.eqtype_hasDecEq_mixin :=
        {| hasDecEq.eq_op := name_eq; hasDecEq.eqP := name_equality |}
    |}.

  Definition N_star := all_names. (* TODO *)
  Program Definition G_core_hyb_ℓ (d k : nat) (H_lt : (d < k)%nat) (i : nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun name => match name with HS => true | _ => false end) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun ℓ name =>
                                                          if (name \in N_star) || (name == PSK)
                                                          then
                                                            if ℓ >=? i then false else true
                                                          else false) erefl
                            ∘ Ls k all_names (fun name => match name with | ESALT => R | _ => D end) erefl)
                       (K_package k PSK d H_lt (i == d) ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  (* Idealization order (hybridazation argument for a given level) *)
  Program Definition G_core_hyb_pred_ℓ_c (d k : nat) (H_lt : (d < k)%nat) (i : nat) (C : list name) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun name => match name with HS => true | _ => false end) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun ℓ name =>
                                                          if (name \in N_star) || (name == PSK)
                                                          then
                                                            if (ℓ + (name \in C)) >=? i then false else true
                                                          else false) erefl ∘ Ls k all_names (fun name => match name with | ESALT => R | _ => D end) erefl) (K_package k PSK d H_lt false ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  (* Idealization order (hybridazation argument for a given level) *)
  Program Definition G_core_ki (d k : nat) (H_lt : (d < k)%nat) :
    package (L_K :|: L_L)
            [interface]
            (XPD_n d k
               :|: DH_interface
               :|: SET_ℓ [PSK] k 0
               :|: XTR_n d k
               :|: GET_n O_star d k) :=
    {package
               (par (par (G_check d k (ltnW H_lt)) (par (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout])
                                              _ erefl _ _) (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)) ∘ (par
                                           (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout])
                                              _ erefl _ _)
                                           (G_XTR_XPD d k (fun name => match name with HS => true | _ => false end) H_lt)))
                  (par
                     (G_dh d k (ltnW H_lt))
                     (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout])
                        _ erefl _)

               ) ) ∘
               (par (par (Ks d k (ltnW H_lt) all_names (fun _ _ => true) erefl ∘ Ls k all_names (fun name => D) erefl) (K_package k PSK d H_lt true ∘ L_package k PSK D)) (Hash true))
    }.
  Admit Obligations.
  Fail Next Obligation.

  Lemma advantage_reflexivity :
    forall P A, AdvantageE P P A = 0%R.
  Proof.
    unfold AdvantageE.
    intros.
    rewrite subrr.
    rewrite Num.Theory.normr0.
    reflexivity.
  Qed.

  Lemma d2 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core d k false H_lt) (G_core d k true H_lt) A
       <= Advantage (Gacr f_hash) (A ∘ R_cr) +
         AdvantageE (G_core_Hash d k H_lt) (G_core d k true H_lt) A)%R.
  Proof.
    intros.
  Admitted.

  Lemma d3 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_Hash d k H_lt) (G_core_D d k H_lt) A
       <= Advantage (Gacr f_xtr) (A ∘ (R_Z f_xtr)) +
         Advantage (Gacr f_xpd) (A ∘ (R_Z f_xpd)) +
         Advantage (Gacr f_xtr) (A ∘ (R_D f_xtr)) +
         Advantage (Gacr f_xpd) (A ∘ (R_D f_xpd)))%R.
  Proof.
    intros.
  Admitted.

  (* Lemma d4 : *)
  (*   forall (d k : nat) H_lt, *)
  (*   (* forall (Score : Simulator d k), *) *)
  (*   forall (LA : {fset Location}) (A : raw_package), *)
  (*     ValidPackage LA (KS_interface d k) A_export A → *)
  (*     (AdvantageE (G_core_R_esalt d k H_lt) (G_core d k true H_lt) A *)
  (*      >= maxR (fun i => AdvantageE (G_core_Hash d k H_lt) (G_core_D d k H_lt) (Ai A i)))%R. *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  Lemma d4 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_R_esalt d k H_lt) (G_core d k true H_lt) A
       <= maxR (fun i => AdvantageE (G_core_D d k H_lt) (G_core d k true H_lt) (Ai A i)))%R.
  Proof.
    intros.
  Admitted.

  Lemma d5 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_R_esalt d k H_lt) (G_core_SODH d k H_lt) A
       = Advantage (Gsodh d k H_lt) (A ∘ R_sodh))%R.
  Proof.
    intros.
  Admitted.

  (* d6: Hybrid lemma *)
  Lemma d6 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    (* forall i, *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      forall ℓ, (ℓ <= d)%nat ->
      (AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt ℓ.+1) A
       <= Advantage (Gxtr d k H_lt ES ℓ) (A ∘ R_xtr ES ℓ erefl) +
         Advantage (Gxtr d k H_lt HS ℓ) (A ∘ R_xtr HS ℓ erefl) +
         Advantage (Gxtr d k H_lt AS ℓ) (A ∘ R_xtr AS ℓ erefl) +
           sumR_l_in_rel XPR XPR (fun _ H => H) (fun n H_in => Advantage (Gxpd d k H_lt n ℓ) (A ∘ R_xpd n ℓ H_in))%R
      )%R.
  Proof.
    intros.
  Admitted.

  Lemma hyb_telescope :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_hyb_ℓ d k H_lt 0) (G_core_hyb_ℓ d k H_lt d) (Ai A i)
       <= sumR 0 d (leq0n d) (fun ℓ => AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt (ℓ+1)) (Ai A i))
      )%R.
  Proof.
    intros.

    set d in H, H_lt |- * at 1 2 6 7.
    generalize dependent n.
    generalize dependent (leq0n d).
    induction d ; intros.
    - unfold sumR.
      (* simpl. *)
      simpl iota.
      unfold AdvantageE.
      unfold List.fold_left.
      rewrite subrr.

      apply eq_ler.
      rewrite Num.Theory.normr0.
      reflexivity.
      
      
      (* rewrite add0r. *)
      (* rewrite add0n. *)
    (* now apply eq_ler. *)
      
      (* reflexivity. *)
    (* rewrite subrr. *)
    (* rewrite Num.Theory.normr0. *)
    (* reflexivity. *)

    -

      rewrite sumR_succ.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (1 := (G_core_hyb_ℓ n k H_lt d)).

      eapply Order.le_trans.
      1:{
        apply Num.Theory.lerD ; [ | easy ].
        eapply (IHd _ _ H_lt).
        apply H.
      }

      rewrite addrC.
      apply Num.Theory.lerD ; [ | easy ].
      rewrite addn1.
      easy.
  Qed.

  Lemma equation20_lhs :
    forall (d k : nat) H_lt,
      (d > 0)%nat ->
    (* forall (Score : Simulator d k), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_SODH d k H_lt) (G_core_hyb_ℓ d k H_lt 0) (Ai A i) = 0)%R.
  Proof.
    intros.

    unfold G_core_SODH.
    unfold G_core_hyb_ℓ.

    unfold pack.
    rewrite <- !Advantage_link.

    rewrite <- (par_commut (Hash true)).
    2: admit.

    rewrite <- (par_commut (Hash true)).
    2: admit.

    setoid_rewrite (Advantage_par (Hash true)).
    2,3,4,5,6,7,8: admit.

    rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)).
    2: admit.

    rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)).
    2: admit.

    replace (0 == d)%nat with false by easy.
    
    (* setoid_rewrite (Advantage_par (K_package k PSK _ _ _ ∘ _)). *)
    (* 2,3,4,5,6,7,8: admit. *)

    replace (λ (ℓ : nat) (name : ExtraTypes.name),
              if (name \in N_star) || (name == PSK) then if ℓ >=? 0%N then false else true else false)
      with
      (λ (ℓ : nat) (name : ExtraTypes.name), false).
    2:{
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      destruct (_ || _) ; [ | reflexivity ].
      now destruct x.
    }

    apply advantage_reflexivity.
  Admitted.

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

  Lemma L_package_esalt_D_to_R :
    forall k A,
    AdvantageE
      (Ls k all_names (λ _ : name, D) erefl)
      (Ls k all_names
         (λ name : ExtraTypes.name,
             match name as name' return (name' = name → ZAF) with
             | BOT => λ _ : BOT = name, D
             | ES => λ _ : ES = name, D
             | EEM => λ _ : EEM = name, D
             | CET => λ _ : CET = name, D
             | BIND => λ _ : BIND = name, D
             | BINDER => λ _ : BINDER = name, D
             | HS => λ _ : HS = name, D
             | SHT => λ _ : SHT = name, D
             | CHT => λ _ : CHT = name, D
             | HSALT => λ _ : HSALT = name, D
             | AS => λ _ : AS = name, D
             | RM => λ _ : RM = name, D
             | CAT => λ _ : CAT = name, D
             | SAT => λ _ : SAT = name, D
             | EAM => λ _ : EAM = name, D
             | PSK => λ _ : PSK = name, D
             | ZERO_SALT => λ _ : ZERO_SALT = name, D
             | ESALT => λ _ : ESALT = name, R
             | DH => λ _ : DH = name, D
             | ZERO_IKM => λ _ : ZERO_IKM = name, D
             end erefl) erefl) A = 0%R.
  Proof.
    intros.
    unfold Ls.
    unfold all_names.
    unfold interface_foreach.
    unfold eq_rect_r.
    unfold eq_rect.
    destruct Logic.eq_sym.
    unfold parallel_package.
    unfold List.map.
    unfold parallel_raw.
    unfold List.fold_left.
    unfold pack.

    repeat (erewrite (Advantage_parR ) ; [ | admit.. ]).
    repeat (erewrite (Advantage_par ) ; [ | admit.. ]).

    eapply eq_rel_perf_ind_eq.
    1,2: apply pack_valid.
    2: admit.
    2,3: admit.

    unfold eq_up_to_inv.
    intros.

    rewrite in_fset in H.
    rewrite mem_seq1 in H.
    move/eqP: H => H ; inversion_clear H.
    
    unfold get_op_default.
    
    unfold L_package.
    unfold pack.

    (* lookup_op_squeeze. *)

    unfold lookup_op.
    rewrite !mkfmapE.
    unfold getm_def.
    unfold ".1", ".2".
    rewrite !eqxx.

    unfold mkdef.

    destruct choice_type_eqP.
    2: apply r_ret ; easy.

    destruct choice_type_eqP.
    2: apply r_ret ; easy.

    subst.
    rewrite !cast_fun_K.

    destruct x as [[]].

    eapply r_bind.
    2:{
      intros.
      instantiate (1 := fun '(_, s₀) '(_, s₁) => s₀ = s₁).
      hnf.
      unfold set_at.
      unfold bind.
      ssprove_sync_eq.
      now apply r_ret.
    }

    admit.
  Admitted.

  Lemma D_to_R_esalt_is_zero :
    forall d k H_lt A,
      AdvantageE (G_core_D d k H_lt) (G_core_R_esalt d k H_lt) A = 0%R.
  Proof.
    intros.

    unfold G_core_D.
    unfold G_core_R_esalt.

    unfold pack.
    rewrite <- !Advantage_link.

    setoid_rewrite (Advantage_parR (Hash true)).
    2: apply pack_valid.
    2,3,4,5,6,7: admit.

    erewrite <- interchange.
    2,3,4,5,6,7,8: admit.

    erewrite (Advantage_parR ).
    2,3,4,5,6,7,8: admit.

    rewrite <- !Advantage_link.
    apply L_package_esalt_D_to_R.
  Admitted.

  Lemma equation20_rhs :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_ki d k H_lt) (G_core_hyb_ℓ d k H_lt d) (Ai A i) = 0)%R.
  Proof.
    intros.

    unfold G_core_ki.
    unfold G_core_hyb_ℓ.

    unfold pack.
    rewrite <- !Advantage_link.

    rewrite <- (par_commut (Hash true)).
    2: admit.

    rewrite <- (par_commut (Hash true)).
    2: admit.

    setoid_rewrite (Advantage_par (Hash true)).
    2,3,4,5,6,7,8: admit.

    rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)).
    2: admit.

    rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)).
    2: admit.

    rewrite eqxx.

    (* setoid_rewrite (Advantage_par (K_package k PSK _ _ _ ∘ _)). *)
    (* 2,3,4,5,6,7,8: admit. *)

    replace (λ (ℓ : nat) (name : ExtraTypes.name),
              if (name \in N_star) || (name == PSK) then if ℓ >=? d then false else true else false)
      with
      (λ (ℓ : nat) (name : ExtraTypes.name), true).
    2:{
      admit.
    }

    erewrite (Advantage_par ).
    2,3,4,5,6,7,8: admit.

    erewrite <- interchange.
    2,3,4,5,6,7,8: admit.

    rewrite <- !Advantage_link.

    apply L_package_esalt_D_to_R.
  Admitted.

  Lemma equation20_eq :
    forall (d k : nat) H_lt,
      (d > 0)%nat ->
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_SODH d k H_lt) (G_core d k true H_lt) (Ai A i)
       <= AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)
         +sumR 0 d (leq0n d) (fun ℓ => AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt (ℓ + 1)) (Ai A i))
      )%R.
  Proof.
    intros.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (G_core_hyb_ℓ d k H_lt 0)).
    rewrite (equation20_lhs d k H_lt).
    2: easy.
    rewrite add0r.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := G_core_ki d k H_lt).
    rewrite <- (addrC (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)))%R.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (G_core_hyb_ℓ d k H_lt d)).

    epose (e := equation20_rhs d k (* Score *)).
    setoid_rewrite (Advantage_sym _ _) in e.

    rewrite e ; clear e.
    rewrite addr0.

    eapply hyb_telescope.
    apply H0.
  Qed.


  Lemma d7 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
      forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)
       <= Advantage (λ x : bool, Gpi d k H_lt [:: ESALT] R x) (Ai A i ∘ R_pi [:: ESALT]) +
   Advantage (λ x : bool, Gpi d k H_lt O_star R x) (Ai A i ∘ R_pi O_star)
      )%R.
  Proof.
    intros.
  Admitted.

  Axiom sumR_leq : forall l u H_range f g,
      (forall ℓ, (ℓ <= u)%nat -> f ℓ <= g ℓ)%R ->
      (sumR l u H_range f <= sumR l u H_range g)%R.

  Lemma core_theorem :
    forall (d k : nat) H_lt (H_gt : (0 < d)%nat),
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (forall i, ValidPackage LA (KS_interface d k) A_export (Ai A i)) →
      (AdvantageE
         (G_core d k false H_lt)
         (G_core d k true H_lt) (A (* ∘ R d M H *))
       <= sumR_l [(R_cr, f_hash); (R_Z f_xtr, f_xtr); (R_Z f_xpd, f_xpd); (R_D f_xtr, f_xtr); (R_D f_xpd, f_xpd)] (fun R_hash_fn => Advantage (Gacr (snd R_hash_fn)) (A ∘ (fst R_hash_fn)))
         +maxR (fun i =>
                  Advantage (Gsodh d k H_lt) (Ai A i ∘ R_sodh) +
                    Advantage (Gpi d k H_lt [ESALT] R) (Ai A i ∘ R_pi [ESALT]) +
                    Advantage (Gpi d k H_lt O_star R) (Ai A i ∘ R_pi O_star) +
                    sumR 0 d (leq0n d) (fun ℓ =>
                                          Advantage (Gxtr d k H_lt ES ℓ) (Ai A i ∘ R_xtr ES ℓ erefl) +
                                          Advantage (Gxtr d k H_lt HS ℓ) (Ai A i ∘ R_xtr HS ℓ erefl) +
                                          Advantage (Gxtr d k H_lt AS ℓ) (Ai A i ∘ R_xtr AS ℓ erefl) +
                                            sumR_l_in_rel XPR XPR (fun _ H => H) (fun n H_in => Advantage (Gxpd d k H_lt n ℓ) (Ai A i ∘ R_xpd n ℓ H_in))%R)
      ))%R.
  Proof.
    intros.
    unfold sumR_l.
    rewrite addr0.
    rewrite addrA.

    eapply Order.le_trans ; [ eapply d2 ; apply H | ].

    eapply Order.le_trans.
    1:{
      apply Num.Theory.lerD ; [ easy | ].
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      apply Num.Theory.lerD ; [ | easy ].
      eapply d3, H.
    }
    rewrite !addrA.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans.
    1:{
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := G_core_R_esalt d k H_lt).
      rewrite D_to_R_esalt_is_zero.
      rewrite add0r.
      eapply d4, H.
    }

    apply max_leq.
    intros i.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    eapply Order.le_trans.
    1:{
      instantiate (2 := (G_core_SODH d k H_lt)).
      apply Num.Theory.lerD ; [ | easy ].
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := (G_core_R_esalt d k H_lt)).
      apply Num.Theory.lerD ; [ easy | ].
      (* erewrite D_to_R_esalt_is_zero. *)
      (* rewrite add0r. *)
      erewrite d5 ; [ | apply H0 ].
      easy.
    }
    rewrite <- (addrC (Advantage (λ x : bool, Gsodh d k H_lt x) (Ai A i ∘ R_sodh))).
    rewrite <- !addrA.
    apply Num.Theory.lerD ; [ easy | ].
    rewrite addrA.

    eapply Order.le_trans.
    1:{
      apply Num.Theory.lerD ; [ easy | ].
      eapply Order.le_trans.
      1: eapply equation20_eq, H ; apply H_gt.

      apply Num.Theory.lerD ; [ easy | ].
      apply sumR_leq.
      intros.
      rewrite addn1.
      eapply d6 ; [ apply H0 | ].
      apply H1.
    }

    rewrite addrA.
    rewrite <- (addrC (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i))).
    rewrite <- (addrA (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i))).
    apply Num.Theory.lerD.
    1:{
      eapply Order.le_trans.
      1: eapply d7, H.
      easy.
    }

    rewrite D_to_R_esalt_is_zero.
    rewrite add0r.
    easy.
  Qed.

End CoreTheorem.

(* Why does this work with d = 0? *)
