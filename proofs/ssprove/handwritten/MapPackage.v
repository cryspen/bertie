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

(*** Helper definitions *)

(*** Package *)

Context (L_M : {fset Location} ).
Axiom PrntIdx : name -> forall (ℓ : bitvec), code fset0 [interface] (chProd chName chName).

Axiom XTR_LABAL_from_index : nat -> name.
Axiom level : chHandle -> code fset0 [interface] (chOption chNat).

(* fig. 29 *)
Definition R_ch_map_XTR_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) :
  (List.In n XTR_names) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  package L_M (XTR_n_ℓ ℓ.+1)
    [interface
       #val #[ XTR n ℓ ] : chXTRinp → chXTRout
    ].
Proof.
  intros.
  refine [package
     #def #[ XTR n ℓ ] ('(h1,h2) : chXTRinp) : chXTRout {
        '(i1,i2) ← PrntIdx n ℓ ;;
        temp1 ← get_or_fn (M (nfto i1) h1) fin_handle (@fail chHandle ;; ret (chCanonical _)) ;;
        temp2 ← get_or_fn (M (nfto i2) h2) fin_handle (@fail chHandle ;; ret (chCanonical _)) ;;

        (* choose = assign first if not ⊥, otherwise second *)
        ℓ_temp ← level temp1 ;;
        ℓ' ← match ℓ_temp with
          | Some ℓ => ret ℓ
          | None =>
            ℓ_temp2 ← level temp2 ;;
            (match ℓ_temp2 with
            | Some ℓ => ret ℓ
            | None => @fail 'nat ;; ret (chCanonical 'nat) (* fail? *)
            end)
          end ;;
        (* *)

        assertD (ℓ' <? ℓ)%nat (fun H =>
        #import {sig #[ XTR n ℓ' ] : chXTRinp → chXTRout }
        as XTR_fn ;;
        h ← XTR_XPD.xtr_angle n h1 h2 ;;
        h' ← XTR_fn (temp1, temp2) ;;
        set_at (H := pos_handle) (M n h) fin_handle (otf h') ;;
        ret h
          )
      }
    ].
  ssprove_valid.
  {
    apply valid_scheme.
    apply PrntIdx.
  }
  {
    unfold get_or_fn.
    ssprove_valid.
  }
  {
    unfold get_or_fn.
    ssprove_valid.
  }
  {
    apply valid_scheme.
    apply level.
  }
  {
    apply valid_scheme.
    apply level.
  }
  {
    apply valid_scheme.
    rewrite <- fset0E.
    apply XTR_XPD.xtr_angle.
  }
  {
    unfold XTR_n_ℓ.
    set (o := mkopsig _ _ _) ; pattern x2 in o ; subst o.
    apply lower_level_in_interface.
    2: Lia.lia.

    simpl.
    unfold XTR, serialize_name.
    unfold mkopsig.
    destruct n.
    all: try (unfold XTR_names in H ; repeat (destruct H ; [ discriminate | ] || contradiction)).
    all : rewrite <- !fset_cat ; simpl ; rewrite !in_fset ; unfold "\in" ; simpl ; rewrite eqxx.
    all: simpl.
    all: try reflexivity.
    all: now rewrite !Bool.orb_true_r.
  }
  {
    unfold set_at.
    ssprove_valid.
  }
Defined.
Fail Next Obligation.

Definition R_ch_map_XTR_packages (d : nat) (M : chHandle -> nat) (H_inLM : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M) :
  package L_M (XTR_n_ℓ d) (XTR_n_ℓ d).
  refine (ℓ_packages
            d
    (fun ℓ H => {package parallel_raw (map_with_in XTR_names (fun x H0 => pack (R_ch_map_XTR_package d x (fun _ => M) H0 H_inLM))) #with _ })
    _ _ _ ).
  Unshelve.

  - intros.
    unfold pack.
    admit.
  - intros.
    unfold pack.
    unfold XTR_names.
    unfold List.map.
    unfold parallel_raw.
    unfold List.fold_left.
    admit.
  - intros.
    simpl.
    unfold XTR, serialize_name.
    solve_imfset_disjoint.

    Unshelve.
    ssprove_valid.
    admit.
Admitted.
Fail Next Obligation.


Context (PrntN: name -> code fset0 fset0 (chName × chName)).
Context (Labels : name -> bool -> code fset0 [interface] chLabel).

Axiom XPN_LABAL_from_index : nat -> name.

Definition R_ch_map_XPD_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) (M_ℓ : name -> nat -> chHandle -> nat) :
  (List.In n XPR) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  (forall s1 s k, ('option ('fin #|fin_handle|); M_ℓ s1 s k) \in L_M) ->
  package L_M (XPD_n_ℓ ℓ.+1)
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  intros.
  refine [package
     #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
        '(i1,_) ← PrntIdx n ℓ ;;
        temp ← get_or_fn (M (nfto i1) h1) fin_handle (@fail chHandle ;; ret (chCanonical chHandle)) ;;
        label ← Labels n r ;;

        (*  *)
        ℓ_temp ← level temp ;;
        ℓ1 ← (match ℓ_temp with
            | Some ℓ => ret ℓ
            | None => @fail 'nat ;; ret (chCanonical 'nat) (* fail? *)
            end) ;;
        (* *)
        assertD (ℓ1 < ℓ)%nat (fun H =>
            h ← XTR_XPD.xpd_angle n label h1 args ;;

            #import {sig #[ XPD n ℓ1 ] : chXPDinp → chXPDout }
            as XPD_fn ;;
            h' ← XPD_fn (temp, r, args) ;;
            ℓ ← ret (if xpn_eq n PSK then (ℓ + 1)%nat else ℓ) ;;
            set_at (M_ℓ n ℓ h) fin_handle (otf h') ;;
            ret h
          )
      }
    ].
  unfold get_or_fn.
  unfold set_at.
  ssprove_valid.
  - apply valid_scheme.
    apply PrntIdx.
  - apply valid_scheme.
    apply Labels.
  - apply valid_scheme.
    apply level.
  - apply valid_scheme. rewrite <- fset0E. apply (prog_valid (XTR_XPD.xpd_angle _ _ _ _)).
  - unfold XPD_n_ℓ.
    set (o := mkopsig _ _ _) ; pattern x2 in o ; subst o.
    apply lower_level_in_interface.
    2: Lia.lia.

    simpl.
    unfold XPD, serialize_name.
    unfold mkopsig.
    destruct n.
    all: try (unfold XPR in H ; repeat (destruct H ; [ discriminate | ] || contradiction)).
    all : rewrite <- !fset_cat ; simpl ; rewrite !in_fset ; unfold "\in" ; simpl ; rewrite eqxx.
    all: simpl.
    all: try reflexivity.
    all: now rewrite !Bool.orb_true_r.
Defined.
Fail Next Obligation.

Lemma trimmed_R_ch_map_XPD_package : forall n d M1 M2 A B C, trimmed [interface
       #val #[ XPD n d ] : chXPDinp → chXPDout
    ] (R_ch_map_XPD_package d n M1 M2 A B C).
Proof.
  intros.

  unfold R_ch_map_XPD_package.
  unfold pack.
  apply trimmed_package_cons.
  apply trimmed_empty_package.
Qed.

Lemma trimmed_parallel_raw_R_ch_map_XPD :
  forall (d : nat),
  forall (M : chHandle → nat),
  forall (H_L_M : ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M),
    trimmed (interface_foreach (fun n => [interface
       #val #[ XPD n d ] : chXPDinp → chXPDout
    ]) XPR) (parallel_raw
       (map_with_in XPR
          (λ (x : name) (H0 : List.In x XPR),
             pack (R_ch_map_XPD_package d x (λ _ : name, M) (λ (_ : name) (_ : nat), M) H0
                     (λ _ : name, H_L_M) (λ (_ : name) (_ : nat), H_L_M))))).
Proof.
  intros.

  apply trimmed_parallel_raw.
  {
    simpl.
    repeat split.
    all: unfold XPD, serialize_name, idents.
    all: solve_imfset_disjoint.
  }
  {
    (* unfold XPD, serialize_name, idents. *)
    unfold XPR.
    unfold "++".
    unfold List.map.
    unfold map_with_in.
    unfold eq_ind.
    unfold trimmed_pairs.

    repeat split.
    all: apply trimmed_R_ch_map_XPD_package.
  }
Qed.

Definition R_ch_map_XPD_packages (d : nat) (M : chHandle -> nat) :
  (forall s, ('option ('fin #|fin_handle|); M s) \in L_M) ->
  package fset0 (XPD_n_ℓ d) (XPD_n_ℓ d).
  intros H_L_M.
  refine (ℓ_packages
            d (fun ℓ H => {package parallel_raw (map_with_in XPR (fun x H => pack (R_ch_map_XPD_package ℓ x (fun _ => M) (fun _ _ => M) H (fun _ => H_L_M) (fun _ _ => H_L_M)))) #with _ })
    _ _ _).

  2: intros ; apply trimmed_parallel_raw_R_ch_map_XPD.
  2: now apply interface_foreach_idents_XPD.

  intros.
  ssprove_valid.

  Unshelve.
  admit.
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
