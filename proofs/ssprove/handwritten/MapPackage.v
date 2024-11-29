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

From KeyScheduleTheorem Require Import Core.
From KeyScheduleTheorem Require Import KeySchedulePackages.

(*** Package *)

Axiom PrntIdx : name -> bitvec -> name × name.

Axiom XTR_LABAL_from_index : nat -> name.

Program Definition R_ch_map_XTR_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) :
  package fset0 (XTR_n_ℓ ℓ)
    [interface
       #val #[ XTR n ℓ ] : chXTRinp → chXTRout
    ]
  :=
  [package
     #def #[ XTR n ℓ ] ('(h1,h2) : chXTRinp) : chXTRout {
        '(i1,i2) ← ret (_ : chProd chName chName) (* (PrntIdx n d') *) ;;
        temp1 ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret _) ;;
        temp2 ← get_or_fn (M (nfto i2) h2) chHandle (@fail _ ;; ret _) ;;
        ℓ' ← (*choos*) ret ((ℓ-1)%nat : 'nat (* TODO *)) ;;
        #import {sig #[ XTR n ℓ' ] : chXTRinp → chXTRout }
        as XTR_fn ;;
        h ← xtr_angle n h1 h2 ;;
        h' ← XTR_fn (fto temp1, fto temp2) ;;
        set_at (M n h) chHandle h' ;;
        ret h
      }
  ].
Admit Obligations.
Fail Next Obligation.

Program Fixpoint R_ch_map_XTR_packages (d : nat) (M : chHandle -> nat) :
  package fset0 (XTR_n_ℓ d) (XTR_n_ℓ d) :=
  match d with
  | O => [package]
  | S d' => (fun x => _) (R_ch_map_XTR_packages d' M)
      (* {package (par _ )} *)
  end.
Next Obligation.
  intros.
  refine {package (par _ x)}.
  Unshelve.
  2:{
    epose (R_ch_map_XTR_package d' ES (fun _ => M)).
    epose (R_ch_map_XTR_package d' AS (fun _ => M)).
    epose (R_ch_map_XTR_package d' HS (fun _ => M)).

    epose (par (par p p0) p1).
    refine f.
  }
  unfold pack.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + eapply valid_par_upto.
      * admit.
      * apply (R_ch_map_XTR_package d' ES (λ _, M)).
      * apply (R_ch_map_XTR_package d' AS (λ _, M)).
      * solve_in_fset.
      * apply fsubsetxx.
      * apply fsubsetxx.
    + apply (R_ch_map_XTR_package d' HS (λ _, M)).
    + apply fsubsetxx.
    + apply fsubsetxx.
    + apply fsubsetxx.
  - apply x.
  - rewrite !fsetU0.
    apply fsubsetxx.
  - rewrite !fsetUid.
    unfold XTR_n_ℓ ; fold XTR_n_ℓ.
    apply fsubsetUr.
  - rewrite <- !fset_cat. simpl.
    apply fsubsetxx.
Admitted.
Fail Next Obligation.


Axiom XPN_LABAL_from_index : nat -> name.

Definition R_ch_map_XPD_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) (M_ℓ : name -> nat -> chHandle -> nat) (Labels : name -> bool -> raw_code label_ty) :
  package fset0 (XPD_n_ℓ ℓ)
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  refine [package
     #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
        '(i1,_) ← ret (_ : chProd chName chName) (* (PrntIdx n d') *) ;;
        temp ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret (chCanonical chHandle)) ;;
        ℓ1 ← (*choos*) ret ((ℓ-1)%nat : 'nat (* TODO *)) ;;
        #import {sig #[ XPD n ℓ1 ] : chXPDinp → chXPDout }
        as XPD_fn ;;
        label ← Labels n r ;;
        h ← xpd_angle n label h1 args ;;
        h' ← XPD_fn (temp, r, args) ;;
        ℓ ← ret (if xpn_eq n PSK then (ℓ + 1)%nat else ℓ) ;;
        set_at (M_ℓ n ℓ h) chHandle (h') ;;
        ret h
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

Program Fixpoint R_ch_map_XPD_packages (d : nat) (M : chHandle -> nat) (Labels : name -> bool -> raw_code label_ty) :
  package fset0 (XPD_n_ℓ d) (XPD_n_ℓ d) :=
  match d with
  | O => [package]
  | S d' =>
      _ (R_ch_map_XPD_packages d' M Labels)
      (* {package (par _ (R_ch_map_XPD_packages d' M)) #with valid_par_upto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ } *)
      (* {package (par _ )} *)
  end.
Next Obligation.
  intros.
  refine {package (par _ x)}.
  Unshelve.
  2:{
    epose (R_ch_map_XPD_package d' N (fun _ => M) (fun _ _ => M) Labels).
    epose (R_ch_map_XPD_package d' PSK (fun _ => M) (fun _ _ => M) Labels).
    epose (R_ch_map_XPD_package d' ESALT (fun _ => M) (fun _ _ => M) Labels).

    epose (par (par p p0) p1).
    refine f.
  }
  unfold pack.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + eapply valid_par_upto.
      * admit.
      * apply (R_ch_map_XPD_package d' N (λ _, M) (λ _ _, M)).
      * apply (R_ch_map_XPD_package d' PSK (λ _, M) (λ _ _, M)).
      * solve_in_fset.
      * apply fsubsetxx.
      * apply fsubsetxx.
    + apply (R_ch_map_XPD_package d' ESALT (λ _, M) (λ _ _, M)).
    + apply fsubsetxx.
    + apply fsubsetxx.
    + apply fsubsetxx.
  - apply x.
  - rewrite !fsetU0.
    apply fsubsetxx.
  - rewrite !fsetUid.
    apply fsubsetUr.
  - rewrite <- !fset_cat. simpl.
    apply fsubsetxx.
Admitted.

(* R_ch_map, fig.25, Fig. 27, Fig. 29 *)
Program Definition R_ch_map (d : nat) (M : chHandle -> nat) :
  package fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
  :=
  let base_package : package fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d) ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ])
  :=
    [package
     #def #[ SET_psk 0 ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ SET_psk 0 ] : chSETinp → chSETout }
        as set_fn ;;
        nh ← set_fn (h, hon, k) ;;
        set_at (M h) chHandle nh ;;
        ret h
      } ;
   #def #[ DHGEN ] (t : 'unit) : 'unit {
        #import {sig #[ DHGEN ] : 'unit → 'unit }
        as dhgen ;;
        dhgen Datatypes.tt
      } ;
     #def #[ DHEXP ] (t : 'unit) : 'unit {
        ret (Datatypes.tt : 'unit)
      }
    ]
  in
  {package
     par (base_package
     ) (R_ch_map_XTR_packages _ _) }.
Admit Obligations.
Fail Next Obligation.

Program Definition Gks_real_map (d : nat) (M : chHandle -> nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
  :
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout
    ] :|:
    GET_o_star_ℓ d)
    [interface] :=
  {package ((par (par (XPD_packages d PrntN Labels) (XTR_packages d PrntN Labels)) DH_package ) ∘ R_ch_map d M ∘ Gcore_real d PrntN Labels) }.
Admit Obligations.
Fail Next Obligation.

Program Definition Gks_ideal_map (d : nat) (M : chHandle -> nat) (Score : Simulator d)
    (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
:
  package
    fset0
    ([interface
       #val #[ SET_psk 0 ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d :|:
    GET_o_star_ℓ d)
    [interface
    ] := {package ((par (par (XPD_packages d PrntN Labels) (XTR_packages d PrntN Labels)) DH_package ) ∘ R_ch_map d M ∘ Gcore_ideal d Score) }.
Admit Obligations.
Fail Next Obligation.

Lemma map_intro_c2 :
  forall (d : nat) (M : chHandle -> nat),
  forall (PrntN : name -> raw_code (chName × chName)) (Labels : name -> bool -> raw_code label_ty),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real d PrntN Labels)
       (Gks_real_map d M PrntN Labels) A = 0
    )%R.
Proof.
  intros.

  unfold Gks_real.
  unfold Gks_real_map.
  unfold pack.
  rewrite <- Advantage_link.

  apply: eq_rel_perf_ind_ignore.
  2: {
    eapply valid_link.
    - apply (pack_valid (R_ch_map d M)).
    - refine (pack_valid (Gcore_real d _ _)).
  }
  1: apply (pack_valid (Gcore_real d _ _)).
  1: apply fsubsetxx.
  2:{
    admit.
  }
  2: apply fdisjoints0.
  2: rewrite fsetU0 ; apply fdisjoints0.

  induction d.
  - unfold XTR_n_ℓ. unfold XPD_n_ℓ. simpl.
    rewrite <- fset0E. rewrite !fsetU0.
    unfold eq_up_to_inv.
    simplify_eq_rel inp_unit.
    + admit. (* SET PSK 0 *)
    + admit. (* DHGEN *)
    + admit. (* DHEXP *)
  -
    assert (forall {n} (x : Simulator (S n)), Simulator n).
    {
      clear.
      intros.
      unfold Simulator in *.
      refine {package (pack x)}.
      eapply (valid_package_inject_import _ _ _ _ _ _ (pack_valid x)).
    }
    specialize (IHd (X _ Score)). clear X.

    unfold eq_up_to_inv.
    intros.

    eassert ([interface #val #[SET_psk 0] : chSETinp → chSETout ; #val #[DHGEN] : 'unit → 'unit ;
                        #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d.+1 :|: 
               XPD_n_ℓ d.+1 :|: GET_o_star_ℓ d.+1 =
              ([interface #val #[SET_psk 0] : chSETinp → chSETout ; #val #[DHGEN] : 'unit → 'unit ;
               #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|: 
              XPD_n_ℓ d :|: GET_o_star_ℓ d) :|: _
            ).
    {
      unfold XTR_n_ℓ ; unfold interface_hierarchy ; fold interface_hierarchy ; fold (@XTR_n_ℓ d).
      unfold XPD_n_ℓ ; unfold interface_hierarchy ; fold interface_hierarchy ; fold (@XPD_n_ℓ d).
      unfold GET_o_star_ℓ ; fold GET_o_star_ℓ.
      rewrite <- !fsetUA.
      f_equal.
      rewrite fsetUC.
      rewrite <- !fsetUA.
      f_equal.
      rewrite fsetUC.
      rewrite <- !fsetUA.
      f_equal.
      rewrite fsetUC.
      rewrite <- !fsetUA.
      f_equal.
    }
    rewrite H1 in H0. clear H1.
    rewrite in_fsetU in H0.
    apply (ssrbool.elimT orP) in H0.
    destruct H0.
    + specialize (IHd id S T x H0).
      clear H0.

      replace (get_op_default
       (par (par (XPD_packages d.+1 _ _) (XTR_packages d.+1 _ _)) DH_package
        ∘ DH_package ∘ Gcore_hyb d.+1) (id, (S, T))) with
        (get_op_default
       (par (par (XPD_packages d PrntN Labels) (XTR_packages d PrntN Labels)) DH_package
        ∘ DH_package ∘ Gcore_hyb d) (id, (S, T))) by admit.
      replace (get_op_default (R_ch_map d.+1 _ ∘ Gcore_real d.+1 _ _) (id, (S, T))) with
        (get_op_default (R_ch_map d M ∘ Gcore_real d PrntN Labels) (id, (S, T))) by admit.

      apply IHd.
    + rewrite <- !fset_cat in H0.
      simpl in H0.
      generalize dependent H0.
      generalize dependent x.
      generalize dependent T.
      generalize dependent S.
      generalize dependent id.
      simplify_eq_rel inp_unit.
      * admit. (* XTR ES d *)
      * admit. (* XTR HS d *)
      * admit. (* XTR AS d *)
      * admit. (* XPD N d *)
      * admit. (* XPD PSK d *)
      * admit. (* XPD ESALT d *)
      * admit. (* GET_o_star TODO d *)
Admitted.

Axiom AdvantageFrame : forall G0 G1 G2 G3 A,
    (AdvantageE G0 G1 A = 0)%R ->
    (AdvantageE G2 G3 A = 0)%R ->
    AdvantageE G0 G2 A = AdvantageE G1 G3 A.

Lemma map_outro_c5 :
  forall (d : nat) (M : chHandle -> nat),
  forall (PrntN : name -> raw_code (chName × chName)) (Labels : name -> bool -> raw_code label_ty),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real d PrntN Labels)
       (Gks_ideal d Score PrntN Labels) (A) =
     AdvantageE
       (Gks_real_map d M PrntN Labels)
       (Gks_ideal_map d M Score PrntN Labels) A
    )%R.
Proof.
  intros.
  unfold Gks_real.
  unfold Gks_real_map.
  unfold pack.

  apply AdvantageFrame ; [ now rewrite map_intro_c2 | ].

  (* epose AdvantageE_equiv. *)
  (* epose (map_intro_c2 d M Score LA A H). *)
  (* epose (AdvantageE_equiv _ ). *)

  (* apply eq_ler. *)

  (* rewrite c2. *)

  unfold Gks_ideal.
  unfold Gks_ideal_map.
  unfold pack.
  rewrite <- Advantage_link.
  (* rewrite <- Advantage_link. *)
  (* rewrite <- Advantage_link. *)

  unfold Gcore_ideal.
  (* reflexivity. *)
Admitted.
