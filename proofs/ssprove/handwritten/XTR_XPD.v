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

(**  This file develops a formal framework for verifying interface-based component
 systems, focusing on ensuring disjointness and minimality (trimmedness) of
 component interfaces. The development uses math-comp's ssreflect style to
 model hierarchical and modular systems, with applications to structured
 protocol or system designs. Key contributions include:

 - Definitions of hierarchical interfaces (e.g., [XPD], [XTR], [DH]) parameterized
   over component identifiers and protocol phases, constructed using
   [interface_hierarchy] and [interface_foreach].
 - Package constructions ([XPD_packages], [XTR_packages], [DH_package]) that
   bundle interfaces with implementations while ensuring well-formedness.
 - Proofs of trimmedness properties ([trimmed_xpd_package], [trimmed_xtr_package])
   guaranteeing that component interfaces are minimal and non-overlapping.
 - Lemmas establishing domain-disjointness ([domm_trim_disjoint_is_ident]) and
   correctness of hierarchical interface compositions.

 The framework supports modular reasoning about systems with layered
 components, such as cryptographic protocols or distributed systems, where
 interface isolation is critical. It leverages math-comp's [fset] and [section]
 mechanisms for precise control over domain interactions.

 Key definitions and notations include:
   - [XPD_n d k]: A hierarchical interface for extended components at depth [d].
   - [DH_interface]: A Diffie-Hellman (DH) protocol interface with [DHGEN] and
     [DHEXP] operations.
   - [trimmed I p]: A property asserting that package [p] has domain exactly [I].
   - [interface_hierarchy f]: A constructor for interfaces with layered operations.

 This module is part of a larger effort to formalize system designs with
 rigorous guarantees about component isolation and compositional validity.           **)

From KeyScheduleTheorem Require Import Types.
From KeyScheduleTheorem Require Import ExtraTypes.
From KeyScheduleTheorem Require Import Utility.

From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem Require Import Dependencies.

From KeyScheduleTheorem Require Import BasePackages.

(** * XTR / XPD *)

Section XTR_XPD.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

  (* p. 5, 6 *)
  (* Xtr *)

  Notation " 'chXTRinp' " :=
    (chHandle × chHandle)
      (in custom pack_type at level 2).
  Notation " 'chXTRout' " :=
    (chHandle)
      (in custom pack_type at level 2).

  Definition XTR (n : name) (ℓ (* 0 .. d *) : nat) (d : nat) : nat :=
    serialize_name n ℓ d 2.

  Definition Xtr
    (n : name) (ℓ : nat) (d : nat) (b : bool) :
    package
      fset0
      [interface
        #val #[ GET (nfto (fst (PrntN n))) ℓ d ] : chGETinp → chGETout ;
        #val #[ GET (nfto (snd (PrntN n))) ℓ d ] : chGETinp → chGETout ;
        #val #[ SET n ℓ d ] : chSETinp → chSETout
      ]
      [interface
        #val #[ XTR n ℓ d ] : chXTRinp → chXTRout
      ].
    refine [package
              #def #[ XTR n ℓ d ] ('(h1,h2) : chXTRinp) : chXTRout {
                #import {sig #[ SET n ℓ d ] : chSETinp → chSETout }
                as set_fn ;;
                '(n1,n2) ← ret (PrntN n : (chProd chName chName)) ;;
                assertD (n1 == fst (PrntN n)) (fun _ =>
                #import {sig #[ GET (nfto n1) ℓ d ] : chGETinp → chGETout }
                as get_fn1 ;;
                assertD (n2 == snd (PrntN n)) (fun _ =>
                #import {sig #[ GET (nfto n2) ℓ d ] : chGETinp → chGETout }
                as get_fn2 ;;
                (if Datatypes.andb (name_eq (nfto (alg2 h1)) BOT) (name_eq (nfto (alg2 h2)) BOT)
                 then assert ( name_eq (nfto (alg2 h1)) (nfto (alg2 h2)) )
                 else ret Datatypes.tt) ;;
                (* temp1 ← get_or_fn (M (nfto i1) h1) chHandle (@fail _ ;; ret _) ;; *)
                h ← xtr_angle n h1 h2 ;;
                '(k1,hon1) ← get_fn1 (h1) ;;
                '(k2,hon2) ← get_fn2 (h2) ;;
                k ← xtr k1 k2 ;;
                hon ← ret (Datatypes.orb hon1 hon2) ;;
                k ← (if Datatypes.andb b hon2
                     then
                       k_star ← sample (uniform #| fin_name |) ;;
                       ret (tag (alg k) (k_star : chName))
                     else ret k) ;;
                h ← set_fn (h, hon, k) ;;
                ret h
              ))}
      ].
    ssprove_valid ; ssprove_valid'_2.
    {
      move: x => /eqP ? ; subst.
      rewrite in_cons.
      apply /orP. now left.
    }
    {
      move: x0 => /eqP ? ; subst.
      rewrite in_cons.
      apply /orP. right.
      rewrite in_cons.
      apply /orP. now left.
    }

    Unshelve.
    all: apply DepInstance.
  Defined.
  Fail Next Obligation.

  Definition XTR_names := [ES; HS; AS].
  Definition XTR_parent_names :=
    [:: ZERO_SALT; PSK; ESALT; DH; HSALT; ZERO_IKM].
  Lemma XTR_parent_names_correct : XTR_parent_names =
    undup (List.fold_left
             (fun y x =>
                y ++ [nfto (fst (PrntN x)); nfto (snd (PrntN x))])
             XTR_names
             []).
  Proof.
    intros.
    now simpl ; rewrite !nfto_name_to_chName_cancel.
  Qed.

  Lemma xtr_parents_is_f_xtr_names :
    forall d ℓ,
    GET_ℓ XTR_parent_names d ℓ =
      (interface_foreach (λ (n : name),
           [interface
              #val #[GET (nfto (fst (PrntN n))) ℓ d] : chXTRout → chGETout ;
              #val #[GET (nfto (snd (PrntN n))) ℓ d] : chXTRout → chGETout])
         XTR_names
      ).
  Proof.
    intros.
    unfold GET_ℓ.
    unfold XTR_names, XTR_parent_names, interface_foreach.
    rewrite !(fset_cons (GET (nfto _.1) ℓ d, _)).
    rewrite !fset1E.
    rewrite !fsetUA.
    simpl.
    rewrite !nfto_name_to_chName_cancel.
    reflexivity.
  Qed.

  Definition XTR_n_ℓ_f d n ℓ :=
    [interface #val #[ XTR n ℓ d ] : chXTRinp → chXTRout].

  Definition XTR_n d k :=
    interface_hierarchy_foreach (XTR_n_ℓ_f k) XTR_names d.

  Definition XTR_n_ℓ d ℓ :=
    interface_foreach (fun n => XTR_n_ℓ_f d n ℓ) XTR_names.

  Lemma trimmed_Xtr : forall ℓ n d b,
      trimmed
        (XTR_n_ℓ_f d n ℓ)
        (Xtr n ℓ d b).
  Proof.
    intros.
    unfold trimmed.
    unfold XTR_n_ℓ_f.
    trim_is_interface.
  Qed.

  Definition xtr_level_raw (ℓ : nat) (d : nat) (b : name -> bool) :=
    parallel_raw (List.map (fun n => pack (Xtr n ℓ d (b n))) XTR_names).

  Lemma valid_xtr_level :
    forall d ℓ b,
      (ℓ <= d)%N ->
      ValidPackage f_parameter_cursor_loc
        (GET_ℓ XTR_parent_names d ℓ :|: SET_ℓ XTR_names d ℓ)
        (interface_foreach
           (fun n =>
              [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout])
           XTR_names)
        (xtr_level_raw ℓ d b).
  Proof.
    intros.

    rewrite xtr_parents_is_f_xtr_names.
    rewrite interface_foreach_U.

    apply (valid_forall
             (L := fset0)
             (λ (n : name),
               [interface
                #val #[GET (nfto (fst (PrntN n))) ℓ d] : chXTRout → chGETout ;
                #val #[GET (nfto (snd (PrntN n))) ℓ d] : chXTRout → chGETout]
                 :|: [interface #val #[SET n ℓ d] : chSETinp → chSETout ])
             (λ n : name, [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout ])
             (λ ℓ (n : name), pack (Xtr n ℓ d (b n)))
             XTR_names
             d
             ℓ
             H
          ).
    - intros.
      unfold idents.
      solve_imfset_disjoint.
    - reflexivity.
    - unfold XTR.
      unfold XTR_names.
      unfold map.
      unfold trimmed_pairs.
      hnf.

      repeat split ;  apply trimmed_Xtr.
    - set (fun x => fset _).
      simpl in f.
      subst f.

      unfold XTR_names, valid_pairs, List.map.
      setoid_rewrite <- fset_cat.
      repeat split  ; match goal with
                     | |- context [ Xtr ?n _ _ ] => apply (pack_valid (@Xtr _ ℓ d (b n)))
                      end.
  Qed.

  Definition xtr_level d ℓ b (H : (ℓ <= d)%N) :=
    {package (xtr_level_raw ℓ d b)
       #with (valid_xtr_level d ℓ b H)}.

  Lemma trimmed_xtr_level d ℓ b (H : (ℓ <= d)%N) :
    trimmed
      (interface_foreach
         (fun n =>
            [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout])
         XTR_names)
      (xtr_level d ℓ b H).
  Proof.
    apply (trimmed_parallel_raw).
    - intros ; unfold idents ; solve_imfset_disjoint.
    - reflexivity.
    - repeat split ; apply trimmed_Xtr.
  Qed.

  Definition XTR_packages
    (d k : nat) (b : name -> bool) (H_lt : (d <= k)%nat)
    : package
        fset0
        (GET_n XTR_parent_names d k :|: SET_n XTR_names d k)
        (XTR_n d k).
  Proof.
    unfold GET_n.
    rewrite interface_hierarchy_U.
    refine (ℓ_packages d (g := fun ℓ => GET_ℓ XTR_parent_names k ℓ :|: SET_ℓ XTR_names k ℓ) (fun ℓ H => xtr_level k ℓ b (leq_trans H H_lt)) _ _).
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
  Definition XPD (n : name) (ℓ : nat) (d : nat) : nat :=
    serialize_name n ℓ d 2.

  Definition Xpd
    (n : name) (ℓ : nat) (d : nat)
    : package
        fset0
        [interface
          #val #[ GET (nfto (fst (PrntN n))) ℓ d ] : chGETinp → chGETout ;
          #val #[ SET n (ℓ + name_eq n PSK)%nat d ] : chSETinp → chSETout ;
          #val #[ HASH f_hash ] : chHASHinp → chHASHout
        ]
        [interface
          #val #[ XPD n ℓ d ] : chXPDinp → chXPDout
        ].
    refine (
          [package
              #def #[ XPD n ℓ d ] ('(h1,r,args) : chXPDinp) : chXPDout {
                #import {sig #[ HASH f_hash ] : chHASHinp → chHASHout }
                as hash_fn ;;
                '(n1,_) ← ret (PrntN n) ;;
                assertD (n1 == fst (PrntN n)) (fun _ =>
                #import {sig #[ GET (nfto n1) ℓ d ] : chGETinp → chGETout }
                as get_fn ;;
                label ← Labels n r ;;
                h ← xpd_angle n label h1 args ;;
                '(k1,hon) ← get_fn h1 ;;
                h ← (if name_eq n PSK
                     then
                       k ← xpd k1 (label, args) ;;
                       #import {sig #[ SET n (ℓ+1) d ] : chSETinp → chSETout }
                       as set_fn ;;
                       set_fn (h, hon, k)
                     else
                       digest ← hash_fn args ;;
                       k ← xpd k1 (label, digest) ;;
                       #import {sig #[ SET n ℓ d ] : chSETinp → chSETout }
                       as set_fn ;;
                       set_fn (h, hon, k)) ;;
                ret h
              )}
      ]).
    (* *)
    ssprove_valid ; ssprove_valid'_2.
    {
      move: x => /eqP ? ; subst.
      rewrite in_cons.
      apply /orP. now left.
    }
    {
      (* move: x2 => /eqP ? ; subst. *)
      rewrite in_cons.
      apply /orP. right.
      rewrite in_cons.
      apply /orP. left.
      (* *)
      rewrite addn0.
      now apply /eqP.
    }
    (* *)
    Unshelve.
    all: apply DepInstance.
  Defined.
  Fail Next Obligation.

  Definition XPR_sub_PSK :=
    [ESALT] ++
      [EEM; CET; BIND; BINDER; SHT; CHT; HSALT; RM; CAT; SAT; EAM] ++ (* has a single parent *)
      [] (* or exactly on sibling of n is contained in XPR *).
  Definition XPR_sub_PSK_parents := [ES; BIND; HS; AS].
  Lemma XPR_sub_PSK_parent_correct :
    XPR_sub_PSK_parents =
      undup (List.map (fun x => nfto (fst (PrntN x))) XPR_sub_PSK).
  Proof.
    intros.
    unfold XPR_sub_PSK, List.map, "++" ; rewrite !nfto_name_to_chName_cancel.
    simpl.
    reflexivity.
  Qed.

  Lemma xpr_sub_psk_parents_is_f_xpr_sub_psk :
    forall d ℓ,
    GET_ℓ XPR_sub_PSK_parents d ℓ =
      (interface_foreach (λ (n : name),
           [interface
              #val #[GET (nfto (fst (PrntN n))) ℓ d] : chXTRout → chGETout])
         XPR_sub_PSK).
  Proof.
    intros.
    unfold GET_ℓ.
    unfold XPR_sub_PSK, XPR_sub_PSK_parents, interface_foreach, "++".
    simpl.
    rewrite !nfto_name_to_chName_cancel.
    repeat (try rewrite !fsetUid ; rewrite !fsetUA ; try rewrite !fsetUid ; f_equal ; rewrite <- !fsetUA).
  Qed.

  Lemma xpr_sub_psk_parents_is_f_xpr_sub_psk_set :
    forall d ℓ,
      SET_ℓ XPR_sub_PSK d ℓ =
      interface_foreach
        (λ n : name,
            [interface #val #[SET n (ℓ + name_eq n PSK) d] : chUNQinp → chXPDout ])
        XPR_sub_PSK.
  Proof.
    intros.
    unfold SET_ℓ.
    unfold XPR_sub_PSK, interface_foreach, "++".
    simpl.
    rewrite addn0.
    repeat (try rewrite !fsetUid ; rewrite !fsetUA ; try rewrite !fsetUid ; f_equal ; rewrite <- !fsetUA).
  Qed.

  Definition XPR :=
    PSK :: XPR_sub_PSK.
  Definition XPR_parents := [RM; ES; BIND; HS; AS].
  Lemma XPR_parent_correct :
    XPR_parents =
      undup (List.map (fun x => nfto (fst (PrntN x))) XPR).
  Proof.
    intros.
    unfold XPR, XPR_sub_PSK, List.map, "++" ; rewrite !nfto_name_to_chName_cancel.
    simpl.
    reflexivity.
  Qed.

  Lemma xpr_parents_is_f_xpr :
    forall d ℓ,
    GET_ℓ XPR_parents d ℓ =
        (interface_foreach (λ (n : name),
             [interface
                #val #[GET (nfto (fst (PrntN n))) ℓ d] : chXTRout → chGETout])
           XPR).
  Proof.
    intros.
    unfold GET_ℓ.
    unfold XPR, XPR_sub_PSK, XPR_sub_PSK_parents, interface_foreach, "++".
    simpl.
    rewrite !nfto_name_to_chName_cancel.
    repeat (try rewrite !fsetUid ; rewrite !fsetUA ; try rewrite !fsetUid ; f_equal ; rewrite <- !fsetUA).
    f_equal.
    rewrite !fsetUA.
    rewrite !fsetUid.
    reflexivity.
  Qed.

  Definition XPD_n_ℓ_f d n ℓ :=
    [interface #val #[ XPD n ℓ d ] : chXPDinp → chXPDout].

  Definition XPD_n (d k : nat) :=
    interface_hierarchy_foreach (XPD_n_ℓ_f k) XPR d.

  Definition XPD_n_ℓ d ℓ :=
    interface_hierarchy_foreach (XPD_n_ℓ_f d) XPR ℓ.

  Lemma trimmed_Xpd : forall n ℓ d,
      trimmed
        (XPD_n_ℓ_f d n ℓ)
        (Xpd n ℓ d).
  Proof.
    intros.
    unfold trimmed.
    unfold XPD_n_ℓ_f.
    trim_is_interface.
  Qed.

  Definition xpd_level_sub_psk_raw (ℓ : nat) (d : nat) : raw_package :=
    parallel_raw (List.map (fun n => pack (Xpd n ℓ d)) XPR_sub_PSK).

  Lemma valid_xpd_level_sub_psk :
    forall ℓ d,
      (ℓ <= d)%nat ->
      ValidPackage
        fset0
        (GET_ℓ XPR_sub_PSK_parents d ℓ
           :|: SET_ℓ XPR_sub_PSK d ℓ
           :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout])
        (interface_foreach
           (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout])
           XPR_sub_PSK)
        (xpd_level_sub_psk_raw ℓ d).
  Proof.
    intros.

    rewrite (interface_foreach_trivial [interface #val #[HASH f_hash] : chHASHout → chHASHout ] XPR_sub_PSK).
    2: easy.

    rewrite <- (addn0 ℓ) at 2.
    rewrite xpr_sub_psk_parents_is_f_xpr_sub_psk.
    rewrite !interface_foreach_U.

    apply (valid_forall
             (λ (n : name),
               [interface #val #[GET (nfto (fst (PrntN n))) ℓ d] : chGETinp → chGETout ]
                 :|: [interface #val #[SET n (ℓ + 0)%nat d] : chSETinp → chSETout ]
                 :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ])
             (λ n : name, [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout ])
             (λ ℓ (n : name), _)
             XPR_sub_PSK
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

      repeat split ; apply (trimmed_Xpd _ ℓ).
    - unfold XPR_sub_PSK, serialize_name, "++", valid_pairs, List.map.
      rewrite <- !fset_cat ; simpl fset.
      (* rewrite !nfto_name_to_chName_cancel. *)
      repeat split ; match goal with
                     | |- context [ Xpd ?n _ _ ] => try apply (pack_valid (@Xpd n ℓ d))
                     end.
  Qed.

  Definition xpd_level_sub_psk ℓ d H :=
    {package (xpd_level_sub_psk_raw ℓ d)
       #with (valid_xpd_level_sub_psk ℓ d H)}.

  Lemma trimmed_xpd_level_sub_psk ℓ d (H : (ℓ <= d)%nat) :
    trimmed
      (interface_foreach
         (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout])
         XPR_sub_PSK)
      (xpd_level_sub_psk ℓ d H).
  Proof.
    intros.
    apply (trimmed_parallel_raw).
    - intros ; unfold idents ; solve_imfset_disjoint.
    - reflexivity.
    - repeat split ; apply trimmed_Xpd.
  Qed.

  Lemma reindex_interface_hierarchy_PSK :
    forall d,
      (interface_hierarchy
         (λ n : nat,
             [interface #val #[SET PSK n d.+1] : chUNQinp → chXPDout ])
         d.+1)
     =
      ([interface #val #[SET PSK 0 d.+1] : chUNQinp → chXPDout ]
         :|: interface_hierarchy (λ n : nat,
               [interface #val #[SET PSK (n.+1) d.+1] : chUNQinp → chXPDout ])
               d).
  Proof.
    intros.
    symmetry.
    set d.+1 at 1 2 3.
    generalize dependent n.
    induction d ; intros.
    - simpl.
      reflexivity.
    - simpl.
      rewrite fsetUA.
      rewrite  IHd.
      reflexivity.
  Qed.

  Lemma set_ℓ_XPR_split :
    forall d k,
      interface_hierarchy_foreach (fun n ℓ =>
        [interface #val #[ SET n (ℓ + name_eq n PSK) k ] : chSETinp → chSETout])
        XPR d =
      interface_hierarchy (fun ℓ =>
        [interface #val #[ SET PSK (ℓ.+1) k ] : chSETinp → chSETout])
        d
        :|: SET_n XPR_sub_PSK d k.
  Proof.
    intros.

    rewrite interface_hierarchy_foreach_cons.
    unfold SET_n.
    (* set d at 1 3 5 7. *)
    generalize dependent k.
    induction d ; intros.
    - reflexivity.
    - simpl.
      rewrite (fsetUC _ [interface #val #[SET PSK d.+2 k] : chUNQinp → chXPDout ]).
      rewrite fsetUA.
      rewrite (fsetUC _ (SET_ℓ XPR_sub_PSK k d.+1)).
      rewrite fsetUA.
      rewrite fsetUA.
      rewrite <- fsetUA.
      rewrite <- fsetUA.
      rewrite <- IHd.

      simpl (_ + _)%nat.
      symmetry.
      rewrite fsetUC.
      rewrite <- !fsetUA.
      f_equal.
      rewrite fsetUC.
      rewrite (fsetUC _ [interface #val #[SET PSK d.+2 k] : chUNQinp → chXPDout ]).
      rewrite <- !fsetUA.
      f_equal ; [ now rewrite addn1 | ].
      rewrite fsetUC.
      unfold interface_hierarchy_foreach.
      unfold interface_hierarchy at 2 ; fold interface_hierarchy.
      f_equal.
      unfold SET_ℓ.
      simpl.
      rewrite addn0.
      reflexivity.
  Qed.

  Lemma XPD_interface_rewrite :
    forall d k,
      (interface_hierarchy (GET_ℓ XPR_parents k) d
         :|: (interface_hierarchy (fun ℓ => [interface #val #[ SET PSK (ℓ.+1) k ] : chSETinp → chSETout]) d
                :|: SET_n XPR_sub_PSK d k) )
        :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout]
      = interface_hierarchy
          (λ n : nat,
              [interface #val #[GET (nfto (PrntN PSK).1) n k] : chXPDout → chGETout ]
                :|: [interface #val #[SET PSK (n + name_eq PSK PSK) k] : chUNQinp → chXPDout ]
                :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ]) d
          :|: interface_hierarchy
          (λ n : nat,
              GET_ℓ XPR_sub_PSK_parents k n
                :|: SET_ℓ XPR_sub_PSK k n
                :|: [interface #val #[HASH f_hash] : chHASHout → chHASHout ]) d.
  Proof.
    intros.
    match goal with | |- context [ _ = ?rhs ] => set (RHS := rhs) end.
    unfold GET_n. rewrite (functional_extensionality _ _ (xpr_parents_is_f_xpr k)). (* unfold GET_ℓ. *)
    unfold SET_n. rewrite <- set_ℓ_XPR_split. (* unfold SET_ℓ. *)

    fold (interface_hierarchy_foreach (λ n ℓ, [interface #val #[GET (nfto (PrntN n).1) ℓ k] : chXPDout → chGETout ]) XPR d).

    rewrite interface_hierarchy_foreachU.
    rewrite interface_hierarchy_foreach_cons.

    rewrite <- (fsetUid [interface #val #[HASH f_hash] : chHASHout → chHASHout ]).
    rewrite fsetUA.
    rewrite fsetUC.
    rewrite !fsetUA.
    rewrite (fsetUC [interface #val #[HASH f_hash] : chHASHout → chHASHout ]).

    rewrite (interface_hierarchy_trivial [interface #val #[HASH f_hash] : chHASHout → chHASHout ] d).

    rewrite interface_hierarchy_U.
    rewrite <- fsetUA.

    rewrite <- interface_hierarchy_foreachU.
    unfold interface_hierarchy_foreach.
    rewrite <- (functional_extensionality _ _ (xpr_sub_psk_parents_is_f_xpr_sub_psk_set k)).
    rewrite <- (functional_extensionality _ _ (xpr_sub_psk_parents_is_f_xpr_sub_psk k)).
    rewrite interface_hierarchy_U.
    rewrite interface_hierarchy_U.

    subst RHS.
    reflexivity.
  Qed.

  Definition XPD_packages (d k : nat) (H : (d < k)%nat) :
    package
      fset0
      ((GET_n XPR_parents d k
          :|: (interface_hierarchy (fun ℓ =>
                 [interface #val #[ SET PSK (ℓ.+1) k ] : chSETinp → chSETout]) d
                 :|: SET_n XPR_sub_PSK d k) )
         :|: [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout])
      (XPD_n d k).
  Proof.
    rewrite XPD_interface_rewrite.

    unfold XPD_n.
    rewrite interface_hierarchy_foreach_cons.

    refine {package par _ _ #with _}.
    Unshelve.
    2:{
      refine (ℓ_packages d (fun ℓ _ => Xpd PSK ℓ k) _ _).
      {
        intros.
        apply trimmed_package_cons.
        apply trimmed_empty_package.
      }
      {
        intros.
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    2:{
      refine (ℓ_packages d (fun ℓ H_le => xpd_level_sub_psk ℓ k (leq_trans H_le (ltnW H))) _ _).
      {
        intros.
        apply trimmed_xpd_level_sub_psk.
      }
      {
        intros.
        apply idents_foreach_disjoint_foreach.
        intros.
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    {
      rewrite <- fsetUid.
      eapply valid_par.
      3: apply pack_valid.
      2:{
        rewrite <- function_fset_cat_l.
        rewrite <- function_fset_cat.
        simpl fset.

        apply pack_valid.
      }
      rewrite <- trimmed_ℓ_packages.
      set (ℓ_packages _).
      rewrite <- trimmed_ℓ_packages.
      solve_Parable.
      apply idents_interface_hierachy3.
      intros.
      rewrite fdisjointC.
      apply idents_interface_hierachy3.
      intros.
      unfold idents.
      solve_imfset_disjoint.
    }
  Defined.

  Definition SET_DH d k : Interface :=
    interface_hierarchy (fun ℓ =>
      [interface #val #[ SET DH ℓ k ] : chSETinp → chSETout]) d.

  Definition SET_DH_ℓ d ℓ : Interface :=
    [interface #val #[ SET DH ℓ d ] : chSETinp → chSETout].

  Definition GET_DH d k : Interface :=
    interface_hierarchy (fun ℓ =>
      [interface #val #[ GET DH ℓ k ] : chGETinp → chGETout]) d.

  Definition GET_DH_ℓ d ℓ : Interface :=
    [interface #val #[ GET DH ℓ d ] : chGETinp → chGETout].

  Definition DH_interface :=
    [interface
     #val #[DHGEN] : chDHGENout → chDHGENout ;
     #val #[DHEXP] : chDHEXPinp → chXPDout ].

  Definition DH_package k :
    (* (G : {fset finGroupType}) *)
    package
      fset0
      (SET_DH 0 k)
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

  Lemma trimmed_dh k : trimmed DH_interface (pack (DH_package k)).
  Proof.
    intros.
    unfold DH_package.
    unfold pack.
    apply trimmed_package_cons.
    apply trimmed_package_cons.
    apply trimmed_empty_package.
  Qed.

  Lemma domm_trim_disjoint_is_ident :
    forall E1 E2 p1 p2,
      idents E1 :#: idents E2 ->
      domm (trim E1 p1) :#: domm (trim E2 p2).
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

  Lemma trimmed_xpd_package : forall (d k : nat) (H_lt : (d < k)%nat),
    trimmed (XPD_n d k) (XPD_packages d k H_lt).
  Proof.
    intros.
    simpl.
    unfold XPD_packages.
    unfold eq_rect_r.
    unfold eq_rect.
    destruct (Logic.eq_sym _).
    destruct (Logic.eq_sym _).
    unfold pack.
    unfold XPD_n.
    rewrite interface_hierarchy_foreach_cons.
    apply trimmed_par.
    {
      apply idents_interface_hierachy3.
      intros.
      rewrite fdisjointC.
      apply idents_interface_hierachy3.
      intros.
      unfold idents ; unfold XPD_n_ℓ_f.
      solve_imfset_disjoint.
    }
    {
      apply trimmed_ℓ_packages.
    }
    {
      apply trimmed_ℓ_packages.
    }
  Qed.

  Lemma trimmed_xtr_package : forall (d k : nat) b H_lt,
    trimmed (XTR_n d k) (XTR_packages d k b H_lt).
  Proof.
    intros.
    simpl.
    unfold XTR_packages.
    unfold eq_rect_r.
    destruct (Logic.eq_sym _).
    erewrite <- (ℓ_raw_package_trimmed d (fun ℓ H => [eta xtr_level] k ℓ b (leq_trans H H_lt))).
    2:{
      intros ℓ ?.
      apply (trimmed_xtr_level k ℓ).
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
    interface_foreach (fun n =>
      [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (XPR).

  Definition UNQ_XTR d : Interface :=
    interface_foreach (fun n =>
      [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (XTR_names).

  Definition UNQ_DH d : Interface :=
    interface_foreach (fun n =>
      [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) ([DH]).

End XTR_XPD.
