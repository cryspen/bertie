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

(* (* Not needed? *) *)
From KeyScheduleTheorem Require Import KeyPackages.

(* (** Extra imports *) *)
(* From SMTCoq Require Import SMTCoq. *)

(*** XTR / XPD *)

Section XTR_XPD.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  (* p. 5,6 *)
  (* Context {xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle}. *)
  (* Context {xtr : chKey -> chKey -> code fset0 fset0 chKey}. *)

  (* Xtr *)

  Notation " 'chXTRinp' " :=
    (chHandle × chHandle)
      (in custom pack_type at level 2).
  Notation " 'chXTRout' " :=
    (chHandle)
      (in custom pack_type at level 2).


  Definition XTR (n : name) (ℓ (* 0 .. d *) : nat) (d : nat) : nat := serialize_name n ℓ d 2.

  Definition Xtr
    (n : name) (ℓ : nat) (d : nat) (b : bool)
    {GET : nat} {SET : nat}
    :
    package
      fset0
      [interface
         #val #[ GET ] : chGETinp → chGETout ;
       #val #[ SET ] : chSETinp → chSETout
      ]
      [interface
         #val #[ XTR n ℓ d ] : chXTRinp → chXTRout
      ].
    refine [package
              #def #[ XTR n ℓ d ] ('(h1,h2) : chXTRinp) : chXTRout {
                #import {sig #[ SET ] : chSETinp → chSETout }
                as set_fn ;;
                #import {sig #[ GET ] : chGETinp → chGETout }
                as get_fn ;;
                '(n1,n2) ← PrntN n ;;
                (if Datatypes.andb (xpn_eq (nfto (alg2 h1)) BOT) (xpn_eq (nfto (alg2 h2)) BOT)
                 then assert ( xpn_eq (nfto (alg2 h1)) (nfto (alg2 h2)) )
                 else ret Datatypes.tt) ;;
                (* temp1 ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret _) ;; *)
                h ← xtr_angle n h1 h2 ;;
                '(k1,hon1) ← get_fn (h1) ;;
                '(k2,hon2) ← get_fn (h2) ;;
                k ← xtr k1 k2 ;;
                hon ← ret (Datatypes.orb hon1 hon2) ;;
                k ← (if Datatypes.andb b hon2
                     then
                       k_star ← sample (uniform #| fin_name |) ;;
                       ret (tag (alg k) (k_star : chName))
                     else ret k) ;;
                h ← set_fn (h, hon, k) ;;
                ret h
              }
      ].
    ssprove_valid ; ssprove_valid'_2.
    Unshelve.
    all: apply DepInstance.
  Defined.
  Fail Next Obligation.

  Definition XTR_names := [ES; HS; AS].

  Definition GET_XTR_ℓ d ℓ := interface_foreach (fun n => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) XTR_names.

  Definition GET_XTR d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (XTR_names) d.

  Definition SET_XTR_ℓ d ℓ := interface_foreach (fun n => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) XTR_names.

  Definition SET_XTR d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (XTR_names) d.

  Definition XTR_n d :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ XTR n ℓ d ] : chXTRinp → chXTRout]) XTR_names d.

  Definition XTR_n_ℓ d ℓ :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ XTR n ℓ d ] : chXTRinp → chXTRout]) XTR_names ℓ.

  Lemma trimmed_Xtr : forall ℓ n d,
      trimmed
        [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout ]
        (Xtr n ℓ d false (GET := GET n ℓ d) (SET := SET n ℓ d)).
  Proof.
    intros.
    unfold trimmed.
    trim_is_interface.
  Qed.

  Definition xtr_level_raw (ℓ : nat) (d : nat) :=
    parallel_raw (List.map (fun n => pack (Xtr n ℓ d false (GET := GET n ℓ d) (SET := SET n ℓ d))) XTR_names).

  Lemma valid_xtr_level :
    forall d ℓ,
      (ℓ <= d)%N ->
      ValidPackage f_parameter_cursor_loc
        (GET_XTR_ℓ d ℓ :|: SET_XTR_ℓ d ℓ)
        (interface_foreach (fun n => [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout]) XTR_names)
        (xtr_level_raw ℓ d).
  Proof.
    intros.

    rewrite interface_foreach_U.
    apply (valid_forall
             (L := fset0)
             (λ (n : name),
               [interface #val #[GET n ℓ d] : chXTRout → chGETout ]
                 :|: [interface #val #[SET n ℓ d] : chSETinp → chSETout ])
             (λ n : name, [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout ])
             (λ ℓ (n : name), pack (Xtr n ℓ d false (GET := GET n ℓ d) (SET := SET n ℓ d)))
             XTR_names
             d
             ℓ
             H
          ).
    - intros.
      unfold idents.
      solve_imfset_disjoint.
    - reflexivity.
    -
      unfold XTR.
      unfold XTR_names.
      unfold map.
      unfold trimmed_pairs.
      hnf.

      repeat split ;  apply trimmed_Xtr.
    -
      setoid_rewrite <- fset_cat.

      set (fun x => fset _).
      simpl in f.
      subst f.

      unfold XTR_names, valid_pairs, List.map.
      repeat split ;
        apply (pack_valid (@Xtr _ ℓ d false (GET _ ℓ d) (SET _ ℓ d))).
  Qed.

  Definition xtr_level d ℓ (H : (ℓ <= d)%N) :=
    {package (xtr_level_raw ℓ d) #with (valid_xtr_level d ℓ H)}.

  Lemma trimmed_xtr_level d ℓ (H : (ℓ <= d)%N) :
    trimmed
      (interface_foreach (fun n => [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout]) XTR_names)
      (xtr_level d ℓ H).
  Proof.
    apply (trimmed_parallel_raw).
    - intros ; unfold idents ; solve_imfset_disjoint.
    - reflexivity.
    - repeat split ; apply trimmed_Xtr.
  Qed.

  Definition XTR_packages (d : nat) :
    package fset0 (GET_XTR d :|: SET_XTR d) (XTR_n (d)).
  Proof.
    unfold GET_XTR.
    rewrite interface_hierarchy_U.
    refine (ℓ_packages d (g := fun ℓ => GET_XTR_ℓ d ℓ :|: SET_XTR_ℓ d ℓ) (fun ℓ H => xtr_level d ℓ H) _ _).
    {
      intros ℓ ?.
      apply trimmed_xtr_level.
    }
    {
      intros.
      simpl.
      unfold idents, XTR ; solve_imfset_disjoint.
    }
  Defined.

  (* Xpd *)

  Notation " 'chXPDinp' " :=
    (chHandle × 'bool × bitvec)
      (in custom pack_type at level 2).
  Notation " 'chXPDout' " :=
    (chHandle)
      (in custom pack_type at level 2).
  Definition XPD (n : name) (ℓ : nat) (d : nat) : nat := serialize_name n ℓ d 2.

  Definition Xpd
    (n : name) (ℓ : nat) (d : nat)
    {GET : nat} {SET : nat} {HASH : nat}
    :
    package
      fset0
      [interface
         #val #[ GET ] : chGETinp → chGETout ;
       #val #[ SET ] : chSETinp → chSETout ;
       #val #[ HASH ] : chHASHinp → chHASHout
      ]
      [interface
         #val #[ XPD n ℓ d ] : chXPDinp → chXPDout
      ].
    refine [package
              #def #[ XPD n ℓ d ] ('(h1,r,args) : chXPDinp) : chXPDout {
                #import {sig #[ SET ] : chSETinp → chSETout }
                as set_fn ;;
                #import {sig #[ GET ] : chGETinp → chGETout }
                as get_fn ;;
                #import {sig #[ HASH ] : chHASHinp → chHASHout }
                as hash_fn ;;
                '(n1,_) ← PrntN n ;;
                label ← Labels n r ;;
                h ← xpd_angle n label h1 args ;;
                '(k1,hon) ← get_fn h1 ;;
                k ← (if xpn_eq n PSK
                     then
                       ℓ ← ret (ℓ + 1) ;;
                       xpd k1 (label, args)
                     else
                       d ← hash_fn args ;;
                       xpd k1 (label, d) ) ;;
                h ← set_fn (h, hon, k) ;;
                ret h
              }
      ].
    ssprove_valid ; ssprove_valid'_2.
    Unshelve.
    all: apply DepInstance.
  Defined.
  Fail Next Obligation.

  Definition XPR :=
    [PSK; ESALT] ++
      [EEM; CET; BIND; BINDER; SHT; CHT; HSALT; RM; CAT; SAT; EAM] ++ (* has a single parent *)
      [] (* or exactly on sibling of n is contained in XPR *).

  Definition XPD_n (d : nat) :=
    interface_hierarchy_foreach (fun n ℓ => [interface
                                             #val #[ XPD n ℓ d ] : chXPDinp → chXPDout
      ]) XPR d.

  Definition XPD_n_ℓ d ℓ :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ XPD n ℓ d ] : chXPDinp → chXPDout]) XPR ℓ.

  Definition GET_XPD d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (XPR) d.

  Definition GET_XPD_ℓ d ℓ : Interface :=
    interface_foreach (fun n => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (XPR).

  Definition SET_XPD d : Interface :=
    interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (XPR) d.

  Definition SET_XPD_ℓ d ℓ : Interface :=
    interface_foreach (fun n => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (XPR).

  Lemma trimmed_Xpd : forall ℓ n d,
      trimmed
        [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout ]
        (Xpd n ℓ d (GET := GET n ℓ d) (SET := SET n ℓ d) (HASH := HASH)).
  Proof.
    intros.
    unfold trimmed.
    trim_is_interface.
  Qed.

  Definition xpd_level_raw (ℓ : nat) (d : nat) :=
    parallel_raw (List.map (fun n => pack (Xpd n ℓ d (GET := GET n ℓ d) (SET := SET n ℓ d) (HASH := HASH))) XPR).

  Lemma valid_xpd_level :
    forall d ℓ,
      (ℓ <= d)%nat ->
      ValidPackage f_parameter_cursor_loc
        (GET_XPD_ℓ d ℓ :|: SET_XPD_ℓ d ℓ :|: [interface #val #[ HASH ] : chHASHinp → chHASHout])
        (interface_foreach (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout]) XPR)
        (xpd_level_raw ℓ d).
  Proof.
    intros.

    rewrite (interface_foreach_trivial [interface #val #[HASH] : chHASHout → chHASHout ] XPR).
    2: easy.
    rewrite !interface_foreach_U.

    apply (valid_forall
             (λ (n : name),
               [interface #val #[GET n ℓ d] : chXPDout → chGETout ]
                 :|: [interface #val #[SET n ℓ d] : chSETinp → chSETout ]
                 :|: [interface #val #[HASH] : chHASHout → chHASHout ])
             (λ n : name, [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout ])
             (λ ℓ (n : name), _)
             XPR
             d
             ℓ
             H
          ).
    - intros.
      unfold idents.
      solve_imfset_disjoint.
    - reflexivity.
    -
      unfold XPR.
      unfold "++".
      unfold List.map.
      unfold trimmed_pairs.
      hnf.

      repeat split ; apply (trimmed_Xpd ℓ).
    - unfold XPR, serialize_name, "++", valid_pairs, List.map.
      rewrite <- !fset_cat ; simpl fset.
      repeat split ; apply (pack_valid (@Xpd _ ℓ d (GET _ ℓ d) (SET _ ℓ d) HASH)).
  Qed.

  Definition xpd_level d ℓ H :=
    {package (xpd_level_raw ℓ d) #with (valid_xpd_level d ℓ H)}.

  Lemma trimmed_xpd_level d ℓ H :
    trimmed
      (interface_foreach (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout]) XPR)
      (xpd_level d ℓ H).
  Proof.
    intros.
    apply (trimmed_parallel_raw).
    - intros ; unfold idents ; solve_imfset_disjoint.
    - reflexivity.
    - repeat split ; apply trimmed_Xpd.
  Qed.

  Definition XPD_packages (d : nat) :
    package fset0 ((GET_XPD d :|: SET_XPD d) :|:
                     [interface #val #[ HASH ] : chHASHinp → chHASHout]) (XPD_n d).
  Proof.
    rewrite (interface_hierarchy_trivial [interface #val #[HASH] : chHASHout → chHASHout ] d).
    rewrite !interface_hierarchy_U.

    refine (ℓ_packages d (xpd_level d) _ _).
    {
      intros.
      apply trimmed_xpd_level.
    }
    {
      intros.
      apply idents_foreach_disjoint_foreach.
      intros.
      unfold idents.
      solve_imfset_disjoint.
    }
  Defined.

  (** ****************** *)

  Definition SET_DH d : Interface :=
    interface_hierarchy (fun ℓ => [interface #val #[ SET DH ℓ d ] : chSETinp → chSETout]) d.

  Definition GET_DH d : Interface :=
    interface_hierarchy (fun ℓ => [interface #val #[ GET DH ℓ d ] : chGETinp → chGETout]) d.

  Definition DH_interface :=
    [interface
     #val #[DHGEN] : chDHGENout → chDHGENout ;
     #val #[DHEXP] : chDHEXPinp → chXPDout ].

  Definition DH_package d :
    (* (G : {fset finGroupType}) *)
    package
      fset0
      (SET_DH d)
      DH_interface.
    intros.
    refine [package
              #def #[ DHGEN ] (grp : chDHGENinp) : chDHGENout {
                                                       DHGEN_function grp
                                                     } ;
            #def #[ DHEXP ] ('(X,Y) : chDHEXPinp) : chDHEXPout {
                                                        DHEXP_function X Y
                                                      }
      ].
    ssprove_valid ; ssprove_valid'_2.
    Unshelve.
    all: apply DepInstance.
  Defined.
  Fail Next Obligation.

  Lemma trimmed_dh d : trimmed DH_interface (pack (DH_package d)).
  Proof.
    intros.
    unfold DH_package.
    unfold pack.
    apply trimmed_package_cons.
    apply trimmed_package_cons.
    apply trimmed_empty_package.
  Qed.

  Lemma domm_trim_disjoint_is_ident :
    forall E1 E2 p1 p2, idents E1 :#: idents E2 -> domm (trim E1 p1) :#: domm (trim E2 p2).
  Proof.
    intros.
    eapply fdisjoint_trans.
    1: apply domm_trim.
    rewrite fdisjointC.
    eapply fdisjoint_trans.
    1: apply domm_trim.
    rewrite fdisjointC.
    apply H.
  Qed.

  Lemma trimmed_trim : forall I p, trimmed I (trim I p).
  Proof.
    intros. unfold trimmed. now rewrite trim_idemp.
  Qed.

  Lemma trimmed_xpd_package : forall (d : nat),
    trimmed (XPD_n d) (XPD_packages d).
  Proof.
    intros.
    simpl.
    unfold XPD_packages.
    unfold eq_rect_r.
    destruct (Logic.eq_sym (interface_hierarchy_trivial [interface #val #[HASH] : chHASHout → chHASHout ] d)).
    unfold eq_rect.
    destruct (Logic.eq_sym _).
    unfold eq_rect.
    destruct (Logic.eq_sym _).
    erewrite <- (ℓ_raw_package_trimmed d ([eta xpd_level] d)).
    2:{
      intros ℓ.
      apply (trimmed_xpd_level d ℓ).
    }
    2:{
      intros n ℓ ? ?.
      apply idents_foreach_disjoint_foreach.
      intros.
      unfold idents.
      solve_imfset_disjoint.
    }
    apply trimmed_trim.
  Qed.

  Lemma trimmed_xtr_package : forall (d : nat),
    trimmed (XTR_n d) (XTR_packages d).
  Proof.
    intros.
    simpl.
    unfold XTR_packages.
    unfold eq_rect_r.
    destruct (Logic.eq_sym _).
    erewrite <- (ℓ_raw_package_trimmed d ([eta xtr_level] d)).
    2:{
      intros ℓ.
      apply (trimmed_xtr_level d ℓ).
    }
    2:{
      intros n ℓ ? ?.
      unfold idents, XTR ; solve_imfset_disjoint.
    }
    apply trimmed_trim.
  Qed.

  Notation " 'chUNQinp' " :=
    (chHandle × 'bool × chKey)
      (in custom pack_type at level 2).
  Notation " 'chUNQout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  Definition UNQ_XPD d : Interface :=
    interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (XPR).

  Definition UNQ_XTR d : Interface :=
    interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (XTR_names).

  Definition UNQ_DH d : Interface :=
    interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) ([DH]).

End XTR_XPD.
