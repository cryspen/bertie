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

(* (** Extra imports *) *)
(* From SMTCoq Require Import SMTCoq. *)

(*** XTR / XPD *)

Section XTR_XPD.
  
Context {PrntN: name -> code fset0 fset0 (chName × chName)}.
Context {Labels : name -> bool -> code fset0 fset0 chLabel}.

(* p. 5,6 *)
Context {xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle}.
Context {xtr : chKey -> chKey -> code fset0 fset0 chKey}.

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
Defined.
Fail Next Obligation.

Definition GET_n_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (all_names) d.

Definition SET_n_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (all_names) d.

Definition XTR_names := [ES; HS; AS].

Definition GET_XTR (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (XTR_names) d.

Definition SET_XTR (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (XTR_names) d.

Definition XTR_n_ℓ d :=
  interface_hierarchy_foreach (fun n d' => [interface #val #[ XTR n d' d ] : chXTRinp → chXTRout]) XTR_names d.

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
    ValidPackage f_parameter_cursor_loc (GET_XTR d.+1 :|: SET_XTR d.+1)
      (interface_foreach (fun n => [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout]) XTR_names)
      (xtr_level_raw ℓ d).
Proof.
  intros.

  rewrite interface_hierarchy_foreachU.
  apply (valid_forall
           (λ (n : name) (ℓ : nat),
                [interface #val #[GET n ℓ d.+1] : chXTRout → chGETout ]
                  :|: [interface #val #[SET n ℓ d.+1] : chSETinp → chXTRout ])
           (λ n : name, [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout ])
           (λ ℓ (n : name), _)
           XTR_names
           d.+1
           ℓ
        ).
  - apply H.
  -
    simpl.
    repeat split.
    all: unfold idents, XTR, serialize_name ; solve_imfset_disjoint.
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
    split.
    {
      epose (pack_valid (@Xtr ES ℓ d false (GET ES ℓ d) (SET ES ℓ d))).
      Set Printing Implicit.
      apply valid_package_from_class.
      admit.
    }
    admit.
(* Qed. *)
Admitted.

Definition xtr_level d ℓ (H : (ℓ <= d)%N) :=
  {package (xtr_level_raw ℓ d) #with (valid_xtr_level d ℓ H)}.

Lemma trimmed_xtr_level d ℓ (H : (ℓ <= d)%N) :
  trimmed
    (interface_foreach (fun n => [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout]) XTR_names)
    (xtr_level d ℓ H).
Proof.
  intros.
  
  unfold xtr_level, xtr_level_raw, parallel_raw, XTR_names, List.map, interface_foreach, List.fold_left.
  unfold pack.

  rewrite <- (trimmed_Xtr ℓ HS).
  rewrite <- (trimmed_Xtr ℓ AS).
  rewrite <- (trimmed_Xtr ℓ ES).

  unfold XTR, serialize_name.
  solve_trimmed.
Qed.

(* Lemma XTR_Parable_ℓ (d : nat) : *)
(*   Parable {package par (par (Xtr ES d false) (Xtr HS d false)) (Xtr AS d false) } *)
(*     (ℓ_raw_packages *)
(*        (λ n : nat, {package par (par (Xtr ES n false) (Xtr HS n false)) (Xtr AS n false) }) d). *)

Definition XTR_packages (d : nat) :
  package fset0 (GET_XTR (d.+1) :|: SET_XTR (d.+1)) (XTR_n_ℓ (d)).
Proof.
  refine (ℓ_packages d (fun y i => xtr_level _ _ _) _ _ _).
  {
    intros.
    apply trimmed_xtr_level.
  }
  {
    intros.
    simpl.
    unfold idents, XTR, serialize_name ; solve_imfset_disjoint.
  }
Defined.

(* Xpd *)

Context {xpd : chKey -> (chLabel * bitvec) -> code fset0 fset0 chKey}.
Context {xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle}.

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
Defined.
Fail Next Obligation.

Definition XPR :=
  [PSK; ESALT] ++
    [EEM; CET; BIND; BINDER; SHT; CHT; HSALT; RM; CAT; SAT; EAM] ++ (* has a single parent *)
    [] (* or exactly on sibling of n is contained in XPR *).

Definition XPD_n_ℓ (d : nat) :=
  interface_hierarchy_foreach (fun n d' => [interface
       #val #[ XPD n d' d ] : chXPDinp → chXPDout
      ]) XPR d.

Definition GET_XPD (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (XPR) d.

Definition SET_XPD (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (XPR) d.

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

Lemma interface_hierarchy_trivial : forall i L d,
  L <> [] ->
  i = (interface_hierarchy_foreach (λ (n : name) (d0 : nat), i) L d.+1 ).
Proof.
  intros.

  unfold interface_hierarchy_foreach.
  simpl.

  induction d.
  {
    simpl.
    rewrite <- fset0E.
    rewrite fsetU0.
    induction L.
    {
      contradiction.
    }
    {
      destruct L.
      {
        reflexivity.
      }
      {
        rewrite interface_foreach_cons.
        rewrite <- IHL.
        2: easy.
        rewrite fsetUid.
        reflexivity.
      }
    }
  }
  {
    simpl.
    rewrite fsetUA.
    rewrite fsetUid.
    apply IHd.
  }
Qed.

Lemma valid_xpd_level :
  forall d ℓ,
    (ℓ <= d)%N ->
  ValidPackage f_parameter_cursor_loc (GET_XPD d.+1 :|: SET_XPD d.+1 :|: [interface #val #[ HASH ] : chHASHinp → chHASHout])
   (interface_foreach (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout]) XPR)
   (xpd_level_raw ℓ d).
Proof.
  intros.

  unfold XPR.
  unfold "++".
  rewrite (interface_hierarchy_trivial [interface #val #[HASH] : chHASHout → chHASHout ] XPR d).
  2: easy.
  rewrite interface_hierarchy_foreachU.

  setoid_rewrite interface_hierarchy_foreachU.

  apply (valid_forall
           (λ (n : name) (d0 : nat),
             [interface #val #[GET n d0 d.+1] : chXPDout → chGETout ]
          :|: [interface #val #[SET n d0 d.+1] : chSETinp → chXPDout ]
          :|: [interface #val #[HASH] : chHASHout → chHASHout ])
           (λ n : name, [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout ])
           (λ ℓ (n : name), _)
           XPR
           d.+1
           ℓ
        ).
  - apply H.
  -
    simpl.
    repeat split.
    all: unfold idents, XPD, serialize_name ; solve_imfset_disjoint.
  -
    unfold XPR.
    unfold "++".
    unfold List.map.
    unfold trimmed_pairs.
    hnf.

    repeat split ;  apply trimmed_Xpd.
  - unfold XPR, serialize_name, "++", valid_pairs, List.map.
    repeat split.
    1:{
      rewrite <- fset_cat ; simpl fset. epose (@Xpd PSK ℓ d (GET PSK ℓ d) (SET PSK ℓ d) HASH).
      admit.
    }
    (* all: do 2 rewrite <- fset_cat ; simpl fset ; apply Xpd. *)
    all: admit.
(* Qed. (* Slow? solve_in_rewrite? Issue with all? *) *)
Admitted.

Definition xpd_level d ℓ H :=
  {package (xpd_level_raw ℓ d) #with (valid_xpd_level d ℓ H)}.

Lemma trimmed_xpd_level d ℓ H :
  trimmed
    (interface_foreach (fun n => [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout]) XPR)
    (xpd_level d ℓ H).
Proof.
  intros.
  
  unfold xpd_level, xpd_level_raw, parallel_raw, XPR, List.map, interface_foreach, List.fold_left, "++".
  unfold pack.

  rewrite <- (trimmed_Xpd ℓ PSK).
  rewrite <- (trimmed_Xpd ℓ ESALT).
  rewrite <- (trimmed_Xpd ℓ EEM).
  rewrite <- (trimmed_Xpd ℓ CET).
  rewrite <- (trimmed_Xpd ℓ BIND).
  rewrite <- (trimmed_Xpd ℓ BINDER).
  rewrite <- (trimmed_Xpd ℓ SHT).
  rewrite <- (trimmed_Xpd ℓ CHT).
  rewrite <- (trimmed_Xpd ℓ HSALT).
  rewrite <- (trimmed_Xpd ℓ RM).
  rewrite <- (trimmed_Xpd ℓ CAT).
  rewrite <- (trimmed_Xpd ℓ SAT).
  rewrite <- (trimmed_Xpd ℓ EAM).

  unfold XPD, serialize_name.

  solve_trimmed.
Qed.

(* Lemma serialize_name_notin2 : *)
(*   forall (ℓ1 ℓ2 : nat), *)
(*     (ℓ2 >= ℓ1.+1)%N -> *)
(*     forall  (n1 n2 : name), *)
(*       forall index, *)
(*            serialize_name n1 ℓ1 index \notin *)
(*              fset1 (T:=Datatypes_nat__canonical__Ord_Ord) (serialize_name n2 ℓ2 index). *)
(* Proof. *)
(*   intros. *)
(*   now apply serialize_name_notin. *)
(*   unfold "\notin". *)
(*   rewrite !ifF ; [ reflexivity | ]. *)
(*   unfold "\in"; simpl; unfold "\in"; simpl. *)
(*   destruct n1, n2 ; unfold serialize_name. *)
(*   all: Lia.lia. *)
(* Qed. *)

Lemma interface_foreach_idents_XPD : forall n ℓ d,
    (ℓ < n)%N ->
    idents (interface_foreach (λ n0 : name, [interface #val #[XPD n0 n d] : chXPDinp → chXPDout ]) XPR)
  :#: idents
  (interface_foreach (λ n0 : name, [interface #val #[XPD n0 ℓ d] : chXPDinp → chXPDout ]) XPR).
Proof.
  intros.

  (* unfold XPR, XPD, serialize_name, idents. *)
  (* simpl. *)

  unfold XPR, idents.
  unfold "++".
  unfold interface_foreach.
  unfold List.fold_left.

  try rewrite  <- !fset1E
  ; try rewrite !imfsetU
  ; try rewrite !imfset1
  ; try rewrite !fdisjointUr
  ; repeat (apply /andP ; split)
  ; try rewrite !fdisjointUl
  ; try rewrite !fdisjoints1.

  all: repeat (apply /andP ; split).
  all: now apply serialize_name_notin.
Qed. (* Slow .. *)

Definition XPD_packages (d : nat)
:
package fset0 ((GET_XPD (d.+1) :|: SET_XPD (d.+1)) :|: [interface
     #val #[ HASH ] : chHASHinp → chHASHout
  ]) (XPD_n_ℓ d).
Proof.
  refine (ℓ_packages d (fun y i => xpd_level _ _ _) _ _ _).
  {
    intros.
    apply trimmed_xpd_level.
  }
  {
    intros.
    now apply interface_foreach_idents_XPD.
  }
Defined.

(** ****************** *)

Axiom chGroup : choice_type.
Axiom chGroup_is_finGroup : FinGroup chGroup.
Definition chFinGroup : finGroupType :=
  {| FinGroup.sort := chGroup; FinGroup.class := chGroup_is_finGroup |}.

Notation " 'chDHGENinp' " :=
  (chGroup)
    (in custom pack_type at level 2).
Notation " 'chDHGENout' " :=
  (chGroup)
    (in custom pack_type at level 2).
Definition DHGEN : nat := 11.

Notation " 'chDHEXPinp' " :=
  (chGroup × chGroup)
    (in custom pack_type at level 2).
Notation " 'chDHEXPout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition DHEXP : nat := 12.

Axiom gen : chGroup -> code fset0 fset0 chGroup.
Definition SET_DH : nat := 13.

Axiom DHGEN_function : forall (ord : chGroup → nat) (E : nat -> nat), chGroup -> code fset0 fset0 chGroup.
Axiom DHEXP_function : forall (ord : chGroup → nat) (E : nat -> nat), chGroup -> chGroup -> code fset0 fset0 chHandle.

Definition DH_interface := [interface #val #[DHGEN] : chDHGENout → chDHGENout ; #val #[DHEXP] : chDHEXPinp → chXPDout ].
Definition DH_Set_interface := [interface #val #[ SET_DH ] : chSETinp → chSETout].

Definition DH_package :
  (* (G : {fset finGroupType}) *)
  forall (ord : chGroup → nat)
  (E : nat -> nat),
  package
    fset0
    DH_Set_interface
    DH_interface.
  intros.
  refine [package
      #def #[ DHGEN ] (grp : chDHGENinp) : chDHGENout {
        DHGEN_function ord E grp
      } ;
      #def #[ DHEXP ] ('(X,Y) : chDHEXPinp) : chDHEXPout {
        DHEXP_function ord E X Y
      }
    ].
  ssprove_valid ; ssprove_valid'_2.
Defined.
Admit Obligations.
Fail Next Obligation.

(*   refine [package *)
(*       #def #[ DHGEN ] (grp : chDHGENinp) : chDHGENout { *)
(*         g ← ret (<[grp : t ]> : chGroup) ;; *)
(*         x ← sample uniform #|'I_(ord(grp))| ;; *)
(*         X ← ret ((g ^+ otf x) : t) ;; *)
(*         ret X *)
(*       } ; *)
(*       #def #[ DHEXP ] ('(X,Y) : chDHEXPinp) : chDHEXPout { *)
(*         _ *)
(*       } *)
(*     ]. *)
(* Admitted. *)
(* Admit Obligations. *)
(* Fail Next Obligation. *)

(* Program Definition DH_package := DH _ _ _. *)
(* Admit Obligations. *)
(* Fail Next Obligation. *)

Lemma trimmed_dh :
  forall {ord E}, trimmed DH_interface (pack (DH_package ord E)).
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
    trimmed (XPD_n_ℓ d) (XPD_packages d).
Proof.
  intros.
  simpl.
  rewrite <- (ℓ_raw_package_trimmed d ([eta xpd_level] d)).
  2:{
    intros ℓ.
    apply (trimmed_xpd_level d ℓ).
  }
  2:{
    intros n ℓ ?.
    now apply interface_foreach_idents_XPD.
  }
  apply trimmed_trim.
Qed.

Lemma trimmed_xtr_package : forall (d : nat),
    trimmed (XTR_n_ℓ d) (XTR_packages d).
Proof.
  intros.
  simpl.
  rewrite <- (ℓ_raw_package_trimmed d ([eta xtr_level] d)).
  2:{
    intros ℓ.
    apply (trimmed_xtr_level d ℓ).
  }
  2:{
    intros n ℓ ?.
    unfold idents, XTR, serialize_name ; solve_imfset_disjoint.
  }
  apply trimmed_trim.
Qed.

End XTR_XPD.
