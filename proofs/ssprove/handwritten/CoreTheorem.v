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
    {package Nk_package ℓ d H_le ∘ (par (DH_package d) (Ls d [DH] Z erefl)) #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_zero d :
    package fset0
      [interface
         #val #[ SET PSK O d ] : chSETinp → chSETout
      ]
      [interface
         #val #[ GET PSK O d ] : chGETinp → chGETout
      ] :=
    {package Ks d [PSK] false erefl ∘ Ls d [PSK] Z erefl #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_succ ℓ d (H_le : (ℓ <= d)%nat) :
    package fset0
      [interface
         #val #[ SET PSK ℓ d ] : chSETinp → chSETout
      ]
      [interface
         #val #[ GET PSK ℓ d ] : chGETinp → chGETout
      ] :=
    {package Ks d [PSK] false erefl ∘ Ls d [PSK] Z erefl #with _ }.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer2_xpd ℓ d (H_le : (ℓ <= d)%nat) :
    package fset0
      [interface]
      (XPD_n_ℓ d ℓ) :=
    xpd_level d ℓ H_le.
  Admit Obligations.
  Fail Next Obligation.

  Definition layer3 ℓ d (H_le : (ℓ <= d)%nat) := Hash.

  Program Definition layer4_salt d :
    package fset0
      [interface]
      (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_SALT ℓ d ] : chGETinp → chGETout]) d) :=
    {package Ks d [ZERO_SALT] false erefl ∘ Ls d [ZERO_SALT] Z erefl #with _}.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_ikm d :
    package fset0
      [interface]
      (interface_hierarchy (fun ℓ => [interface #val #[ GET ZERO_IKM ℓ d ] : chGETinp → chGETout]) d) :=
    {package Ks d [ZERO_IKM] false erefl ∘ Ls d [ZERO_IKM] Z erefl #with _}.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_xtr ℓ d H_le :
    package fset0
      (XTR_n_ℓ d ℓ :|: GET_XTR_ℓ d ℓ)
      (SET_XTR_ℓ d ℓ) := xtr_level d ℓ H_le.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_check d :
    package fset0
      (XPD_n d)
      (XPD_n d :|: interface_hierarchy (fun ℓ => [interface #val #[ GET BINDER ℓ d ] : chGETinp → chGETout ]) d) := _.
  Admit Obligations.
  Fail Next Obligation.

  Program Definition layer4_xpd d :
    package fset0
      (XPD_n d :|: SET_XPD d)
      (GET_XPD d) := {package XPD_packages d ∘ layer4_check d #with _}.
  Admit Obligations.
  Fail Next Obligation.

  Definition core (d : nat) : package fset0
                              (interface_hierarchy (fun x => [interface]) d)
                              (GET_O_star d).
  Proof.
    refine (ℓ_packages d _ _ _).
    Unshelve.
    3:{
      intros n H.
      epose (dh := layer1 n d H).
      epose (layer2_xpd n d H).
      epose (hash := layer3 n d H).
      epose (salt0 := layer4_salt d).
      epose (ikm0 := layer4_ikm d).
      epose (check := layer4_check d).
      epose (xtr := layer4_xtr n d H).
      epose (xpd := layer4_xpd d).

      epose (T := package fset0
                    [interface]
                    (match n with
                     | O => [interface]
                     | S n => (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ d] : chDHEXPout → chGETout ]) all_names n)
                     end)).

      epose (set_xtr := fun psk (sub_packages : T) => {package
                           xtr ∘
                           parallel_raw [
                             pack dh;
                             pack psk;
                             pack hash;
                             pack salt0;
                             pack ikm0;
                             pack sub_packages]
                           #with _} : package fset0 [interface] (SET_XTR_ℓ d n)).
      Unshelve.
      {

      }
      
      epose (set_xpd := fun psk (sub_packages : T) => {package
                           xpd ∘
                           parallel_raw [
                             pack dh;
                             pack psk;
                             pack hash;
                             pack salt0;
                             pack ikm0;
                             pack sub_packages]
                           #with _} : package fset0 [interface] (SET_XPD_ℓ d n)).

      (* epose (output := fun psk sub_packages => {package Ks d O_star false erefl ∘ *)
      (*                                             (parallel_raw [ *)
      (*                                                  pack (set_xtr psk sub_packages); *)
      (*                                                  pack (set_xpd psk sub_packages); *)
      (*                                                  pack (Ls d O_star Z _)]) #with _}). *)
      epose (output := fun psk
                         (sub_packages : T) =>
                         {package Ks d all_names false erefl ∘
                            (parallel_raw [
                                 pack (set_xtr psk sub_packages);
                                 pack (set_xpd psk sub_packages);
                                 pack (Ls d all_names Z _)]) #with _}).


      assert (package fset0
                [interface]
                (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ d] : chDHEXPout → chGETout ]) all_names n)).
      {
        induction n as [ | ℓ ].
        - epose (psk0 := layer2_zero d).
          refine (output psk0 _).
          unfold GET_XPD_ℓ.
          refine {package emptym #with valid_empty_package _ _}.
        - epose (pskS := layer2_succ (S ℓ) d H).
          refine (output pskS _).
          specialize (IHℓ (leq_trans H (leqnSn _))).
          apply IHℓ.
      }

      Unshelve.
      {
        simpl.
      
          (* refine {package (pack IHℓ) #with _}. *)
          (* apply (pack_valid IHℓ). *)

          (* apply (valid_package_inject_export _ _ _ (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET n ℓ d] : chDHEXPout → chGETout ]) *)
          (* all_names ℓ)). *)
          (* 2: apply (pack_valid IHℓ). *)

          (* unfold GET_XPD_ℓ. *)
          
          

          
            

          apply 

        Unshelve.
        {
          ssprove_valid.
          - epose valid_parable.
            
        }
        
    }
  Qed.

  Lemma core_theorem :
    forall (d : nat),
    forall (Score : Simulator d),
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d) A_export A →
      (AdvantageE
         (Gcore_real d)
         (Gcore_ideal d Score) (A (* ∘ R d M H *))
       <= sumR_l [R_cr; (R_Z f_hash); R_D] (fun R => Advantage (Gacr f_hash) (A ∘ R))
         +maxR (fun i => Advantage Gsodh (Ai A i ∘ R_sodh) + AdvantageE (Gcore_sodh d) (Gcore_ideal d Score) (Ai A i))
      )%R.
  Proof.
    intros.
    unfold sumR_l.
    rewrite addr0.
    rewrite addrA.

    unfold Gcore_real.
    unfold pack.
    
    
    (* unfold Gacr. *)
    (* simpl. *)
    (* simpl. *)
  Admitted.

  Lemma equation20_lhs :
    forall (d : nat),
    forall (Score : Simulator d),
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d) A_export A →
      (AdvantageE (Gcore_sodh d) (Gcore_hyb d 0) (Ai A i) = 0)%R.
  Proof. Admitted.

  Lemma equation20_rhs :
    forall (d : nat),
    forall (Score : Simulator d),
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d) A_export A →
      (AdvantageE (Gcore_ki d) (Gcore_hyb d d) (Ai A i) = 0)%R.
  Proof.
    intros.
  Admitted.

  Lemma hyb_telescope :
    forall (d : nat),
    forall (Score : Simulator d),
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d) A_export A →
      (AdvantageE (Gcore_hyb d 0) (Gcore_hyb d d) (Ai A i)
       = sumR 0 (d-1) (leq0n (d-1)) (fun ℓ => AdvantageE (Gcore_hyb d ℓ) (Gcore_hyb d (ℓ+1)) (Ai A i))
      )%R.
  Proof.
    intros.
    unfold sumR.
    induction d.
    - simpl.
      (* unfold Gcore_hyb. *)
  Admitted.

  Lemma equation20_eq :
    forall (d : nat),
    forall (Score : Simulator d),
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d) A_export A →
      (AdvantageE (Gcore_sodh d) (Gcore_ideal d Score) (Ai A i)
       <= AdvantageE (Gcore_ki d) (Gcore_ideal d Score) (Ai A i)
         +sumR 0 (d-1) (leq0n (d-1)) (fun ℓ => AdvantageE (Gcore_hyb d ℓ) (Gcore_hyb d (ℓ + 1)) (Ai A i))
      )%R.
  Proof.
    intros.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (Gcore_hyb d 0)).
    rewrite (equation20_lhs d Score).
    rewrite add0r.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := Gcore_ki d).
    rewrite addrC.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (Gcore_hyb d d)).

    epose (e := equation20_rhs d Score).
    setoid_rewrite (Advantage_sym _ _) in e.
    rewrite e ; clear e.
    rewrite addr0.

    setoid_rewrite <- hyb_telescope ; easy.
  Qed.

End CoreTheorem.
