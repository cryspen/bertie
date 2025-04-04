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

From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem Require Import Dependencies.

From KeyScheduleTheorem Require Import BasePackages.
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

From KeyScheduleTheorem Require Import Core.
From KeyScheduleTheorem Require Import KeySchedulePackages.
From KeyScheduleTheorem Require Import MapPackage.
From KeyScheduleTheorem Require Import CoreTheorem.

(*** Key Schedule theorem *)

Section MainTheorem.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

(* Definition KS : nat := 0%nat. *)

(* Fig. 12, p. 18 *)
(* Fig.29, P.63 *)


(* Fig 13-14. K key and log *)

Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit.

Axiom level : chHandle -> nat.

(* Definition L_package (n : chName) (Log_table : chHandle -> nat) (P : ZAF) : *)
(*   package *)
(*     fset0 *)
(*     [interface] *)
(*     UNQ_O_star. *)
(*   (* refine [package *) *)
(*   (*     #def #[ UNQ TODO (* n ℓ *) ] ('(h,hon,k) : chUNQinp) : chUNQout { *) *)
(*   (*        (* (exists_h_star (fun h_star =>  *) *) *)
(*   (*        (*   '(h',hon',k) ← get_or_fn (Log_table h_star) (chHandle × 'bool × chKey) (@fail _ ;; ret (chCanonical (chHandle × 'bool × chKey))) ;; *) *) *)
(*   (*        (*   r ← ret (level h) ;; *) *) *)
(*   (*        (*   r' ← ret (level h_star) ;; *) *) *)
(*   (*        (*   match P with *) *) *)
(*   (*        (*   | Z => ret Datatypes.tt *) *) *)
(*   (*        (*   | A => if Datatypes.andb (hon == hon' == false) (r == r' == false) *) *) *)
(*   (*        (*         then @fail _ ;; ret Datatypes.tt *) *) *)
(*   (*        (*         else ret Datatypes.tt *) *) *)
(*   (*        (*   | F => @fail _ ;; ret Datatypes.tt *) *) *)
(*   (*        (*   end)) ;; *) *) *)
(*   (*         set_at (Log_table h) (chHandle × 'bool × chKey) (h,hon,k) ;; *) *)
(*   (*         ret h *) *)
(*   (*     } *) *)
(*   (*   ]. *) *)
(* Admitted. *)
(* Admit Obligations. *)
(* Fail Next Obligation. *)

(* Fig 12. the real XPD and XTR games *)

Lemma main_reduction :
  forall d k H_lt,
  forall (Score : Simulator d k),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
    (AdvantageE
       (Gks_real d k H_lt)
       (Gks_ideal d k (ltnW H_lt) Score) A =
     AdvantageE
       (Gcore_real d k H_lt)
       (Gcore_ideal d k (ltnW H_lt) Score) (A ∘ R_ch_map d k (ltnW H_lt))
    )%R.
Proof.
  intros.
  rewrite (map_outro_c5 d k H_lt Score LA).

  
  unfold Gks_real_map , Gks_ideal_map , pack.
  unfold Gcore_real.

  epose (Advantage_link).
  rewrite <- Advantage_link.
  (* rewrite <- Advantage_link. *)
  unfold Gcore_ideal.
Admitted.
  (* reflexivity. *)
(* Qed. *)



Axiom ε_acr : R.
Axiom ε_sodh_ki : bool -> R.

Axiom R_es : nat -> package fset0 [interface] [interface].
Axiom Gxtr_es : nat -> loc_GamePair
      [interface
         (* #val #[ ES ] : 'unit → 'unit *)
      ].

Axiom R_as : nat -> package fset0 [interface] [interface].
Axiom Gxtr_as : nat -> loc_GamePair
      [interface
         (* #val #[ AS ] : 'unit → 'unit *)
      ].

Axiom R_hs : nat -> package fset0 [interface] [interface].
Axiom Gxtr_hs : nat -> loc_GamePair
      [interface
         (* #val #[ HS ] : 'unit → 'unit *)
      ].

(* Definition Gxpds : forall (ℓ : nat) (P : ZAF), *)
(*     (ℓ <= d)%N -> *)
(*       loc_GamePair *)
(*       (interface_foreach *)
(*           (λ n : name, [interface #val #[XPD n ℓ] : ((chKout) × ('bool)) × (chHASHout) → chKout ]) *)
(*           XPR). *)
(* Proof. *)
(*   intros. *)
(*   refine (fun b => {| locs := L_K :|: L_L ; *)
(*                   locs_pack := {package xpd_level _ H ∘ ((par (K_XPD b) hash) ∘ (Ls XPR P erefl)) } *)
(*                 |}). *)
(*   eapply valid_link_upto. *)
(*   1: apply (pack_valid (xpd_level _ _)). *)
(*   2: apply fsub0set. *)
(*   2: apply fsubsetxx. *)
(*   eapply valid_link_upto. *)
(*   2: apply Ls. *)
(*   3: apply fsubsetUr. *)
(*   2: apply fsubsetUl. *)
(*   eapply valid_par_upto. *)
(*   3: apply hash. *)
(*   3: rewrite fsetU0 ; apply fsubsetxx. *)
(*   3: rewrite <- fset0E ; rewrite fsetU0 ; apply fsubsetxx. *)
(*   3: apply fsubsetxx. *)
(*   1:{ *)
(*     rewrite <- trimmed_K_XPD. *)
(*     rewrite <- trimmed_hash. *)
(*     solve_Parable. *)
(*     unfold idents. *)
(*     rewrite imfsetU. *)
(*     rewrite fdisjointUl. *)
(*     apply /andP ; split. *)
(*     - unfold SET_XPD. *)
(*       unfold interface_hierarchy_foreach. *)
(*       rewrite fdisjointC. *)
(*       apply (idents_interface_hierachy2). *)
(*       intros. *)
(*       unfold idents. *)
(*       solve_imfset_disjoint. *)
(*       all: unfold HASH, SET, serialize_name ; Lia.lia. *)
(*     - unfold GET_XPD. *)
(*       unfold interface_hierarchy_foreach. *)
(*       rewrite fdisjointC. *)
(*       apply (idents_interface_hierachy2). *)
(*       intros. *)
(*       unfold idents. *)
(*       solve_imfset_disjoint. *)
(*       all: unfold HASH, GET, serialize_name ; Lia.lia. *)
(*   } *)
(*   eapply valid_package_inject_import. *)
(*   2: rewrite fsetUC ; apply (pack_valid (K_XPD b)). *)
(*   unfold UNQ_XPD. *)
(*   apply fsubsetxx. *)
(* Qed. *)

(* Goal forall d k (H_lt : (d < k)%nat), True. *)
(*   intros. *)
(*   epose (pack (XPD_ 1 k _)). *)
(*   unfold XPD_n in r. *)
(*   unfold interface_hierarchy_foreach in r. *)
(*   unfold interface_hierarchy in r. *)
(*   unfold XPD_ in r. *)
(*   unfold XPD_packages in r. *)
(*   unfold eq_rect_r in r. *)
(*   unfold eq_rect in r. *)
(*   destruct Logic.eq_sym in r. *)
(*   unfold pack in r. *)
(*   destruct Logic.eq_sym in r. *)
(*   destruct Logic.eq_sym in r. *)

(*   unfold ℓ_packages in r. *)
(*   unfold ℓ_raw_packages in r. *)
(*   unfold map_with_in_num_upper in r. *)

(*   par (par (Xpd PSK 0 k) (Xpd PSK 1 k)) *)
(*                           (par *)
(*                              (xpd_level_sub_psk 0 k *)
(*                                 (leq_trans (n:=1) (m:=0) (p:=k) *)
(*                                    (leq_trans (n:=1) (m:=0) (p:=1) (leqnSn 0) (leqnn 1)) *)
(*                                    (ltnW (m:=1) (n:=k) ?H_lt))) *)
(*                              (xpd_level_sub_psk 1 k *)
(*                                 (leq_trans (n:=1) (m:=1) (p:=k) (leqnn 1) (ltnW (m:=1) (n:=k) ?H_lt))))∘ par *)
(*            (Ks 2 k ?H_lt (undup (XPR ++ XPR_parents)) false erefl *)
(*             ∘ Ls k (undup (XPR ++ XPR_parents)) F erefl) Hash *)
  
(*   destruct ((XPD_interface_rewrite 0 k)) in p. *)

Definition Gxpd : forall d k (H_lt : (d < k)%nat)  (n : name) (ℓ : nat),
    (ℓ <= d)%N ->
    (n \in XPR) ->
      loc_GamePair
      ([interface #val #[XPD n ℓ k] : ((chSETout) × ('bool)) × (chHASHout) → chSETout ]).
Proof.
  intros.
  refine (fun b => {| locs := L_K :|: L_L ;
                  locs_pack :=
                    {package XPD_ d k H_lt #with _}
                |}).
  eapply valid_package_inject_export.
  2: apply pack_valid.
  {
    unfold XPD_n.
    apply interface_hierarchy_foreach_subsetR.
    2: easy.
    exists n, H0, ℓ, H.
    apply fsubsetxx.
  }
  Unshelve.
  apply DepInstance.
Qed.

Axiom R_ : name -> nat -> package fset0 [interface] [interface].

Ltac split_advantage O :=
  try apply (AdvantageE_le_0 _ _ _ ) ;
  eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
  replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
      symmetry ] ; revgoals.

Axiom ki_hybrid :
  forall d k H_lt (ℓ : nat) (H_le : (ℓ <= d)%nat),
  forall (LA : {fset Location}) (A : raw_package),
  forall i,
    ValidPackage LA ([interface #val #[SET PSK 0 d] : chSETinp → chSETout ; #val #[DHGEN] : 'unit → 'unit ;
                   #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d k :|: XPD_n_ℓ d k) A_export A →
  (AdvantageE (Gcore_hyb d ℓ) (Gcore_hyb d (ℓ + 1)) (Ai (A ∘ R_ch_map d k (ltnW H_lt)) i) <=
  Advantage (λ x : bool, Gxtr_es ℓ x) (Ai (A) i ∘ R_es ℓ) + Advantage (λ x : bool, Gxtr_hs ℓ x) (Ai (A) i ∘ R_hs ℓ) +
    Advantage (λ x : bool, Gxtr_as ℓ x) (Ai (A) i ∘ R_as ℓ) + sumR_l_in_rel XPR XPR (fun _ H => H) (λ n H_in, Advantage (λ x : bool, Gxpd d k H_lt n ℓ H_le H_in x  ) (Ai (A) i ∘ R_ n ℓ)))%R.

Lemma key_schedule_theorem :
  forall d k H_lt,
  forall (S : Simulator d k),
  forall (hash : nat),
  forall (LA : {fset Location}) (A : raw_package),
    ValidPackage LA (KS_interface d k) A_export A →
  forall (H_ε_acr : (sumR_l [:: R_cr; R_Z f_hash; R_D] (λ R : package f_parameter_cursor_loc (fset [::]) (fset [::]), Advantage (λ x : bool, Gacr f_hash x) ((A ∘ R_ch_map d k (ltnW H_lt)) ∘ R)) <= ε_acr)%R),
  forall (H_ε_sodh_ki : (forall i, Advantage (λ x : bool, Gsodh x) (Ai (A ∘ R_ch_map d k (ltnW H_lt)) i ∘ R_sodh) + AdvantageE (Gcore_ki d k) (Gcore_ideal d k (ltnW H_lt) S) (Ai (A ∘ R_ch_map d k (ltnW H_lt)) i) <= ε_sodh_ki i)%R),
    (AdvantageE
       (Gks_real d k H_lt)
       (Gks_ideal d k (ltnW H_lt) S) A <=
     ε_acr +
     maxR (fun i =>
      ε_sodh_ki i
      +sumR_H 0 (d) (ltac:(easy)) (fun ℓ H =>
         Advantage (Gxtr_es ℓ) (Ai A i ∘ R_es ℓ)
        +Advantage (Gxtr_hs ℓ) (Ai A i ∘ R_hs ℓ)
        +Advantage (Gxtr_as ℓ) (Ai A i ∘ R_as ℓ)
        +sumR_l_in_rel XPR XPR (fun _ H => H) (fun n H_in => Advantage (Gxpd d k H_lt n ℓ H H_in (* (ltac:(Lia.lia)) *)) (Ai A i ∘ R_ n ℓ)
       )))
    )%R.
Proof.
  intros.
  rewrite (main_reduction).

  eapply Order.le_trans.
  - eapply (core_theorem _ _ _).

    eapply valid_link_upto.
    1 :{
      apply H.
    }
    1:{
      eapply valid_package_inject_import.
      2: apply pack_valid.
      unfold KS_interface.
      solve_in_fset.
    }
    {
      apply fsubsetUl.
    }
    {
      apply fsubsetUr.
    }
  - admit.
Admitted.

End MainTheorem.

