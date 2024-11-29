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

From KeyScheduleTheorem Require Import BasePackages.
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

From KeyScheduleTheorem Require Import Core.
From KeyScheduleTheorem Require Import KeySchedulePackages.
From KeyScheduleTheorem Require Import MapPackage.
From KeyScheduleTheorem Require Import CoreTheorem.


(*** Key Schedule theorem *)

Notation " 'chTranscript' " :=
  (t_Handle)
    (in custom pack_type at level 2).

Definition KS : nat := 0%nat.

(* Fig. 12, p. 18 *)
(* Fig.29, P.63 *)



Notation " 'chKinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chKout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition K (n : chName) (ℓ : nat) := 10%nat.

(* Fig 13-14. K key and log *)

Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit.
Inductive ZAF := | Z | A | F.

Axiom level : chHandle -> nat.

Definition L_package (n : chName) (Log_table : chHandle -> nat) (P : ZAF) :
  package
    fset0
    [interface]
    [interface
       #val #[ UNQ TODO ] : chUNQinp → chUNQout
    ].
  refine [package
      #def #[ UNQ TODO (* n ℓ *) ] ('(h,hon,k) : chUNQinp) : chUNQout {
         (* (exists_h_star (fun h_star =>  *)
         (*   '(h',hon',k) ← get_or_fn (Log_table h_star) (chHandle × 'bool × chKey) (@fail _ ;; ret (chCanonical (chHandle × 'bool × chKey))) ;; *)
         (*   r ← ret (level h) ;; *)
         (*   r' ← ret (level h_star) ;; *)
         (*   match P with *)
         (*   | Z => ret Datatypes.tt *)
         (*   | A => if Datatypes.andb (hon == hon' == false) (r == r' == false) *)
         (*         then @fail _ ;; ret Datatypes.tt *)
         (*         else ret Datatypes.tt *)
         (*   | F => @fail _ ;; ret Datatypes.tt *)
         (*   end)) ;; *)
          set_at (Log_table h) (chHandle × 'bool × chKey) (h,hon,k) ;;
          ret h
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

(* Fig 12. the real XPD and XTR games *)



Lemma main_reduction :
  forall (d : nat) (M : chHandle -> nat),
  forall (PrntN : name -> raw_code (chName × chName)) (Labels : name -> bool -> raw_code label_ty),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real d PrntN Labels)
       (Gks_ideal d Score PrntN Labels) A =
     AdvantageE
       (Gcore_real d PrntN Labels)
       (Gcore_ideal d Score) (A ∘ R_ch_map d M)
    )%R.
Proof.
  intros.
  rewrite (map_outro_c5 d M PrntN Labels Score LA).
  unfold Gks_real_map , Gks_ideal_map , pack.
  rewrite <- Advantage_link.
  rewrite <- Advantage_link.
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

Axiom Gxpd : XPR -> nat -> loc_GamePair
      [interface
         (* #val #[ ES ] : 'unit → 'unit *)
      ].


Axiom R_ : XPR -> nat -> package fset0 [interface] [interface].

Ltac split_advantage O :=
  try apply (AdvantageE_le_0 _ _ _ ) ;
  eapply Order.le_trans ; [ apply Advantage_triangle with (R := O) | ] ;
  replace (AdvantageE _ _ _) with (@GRing.zero R) ; [
      replace (AdvantageE _ _ _) with (@GRing.zero R) ; [ rewrite add0r ; easy | symmetry ] |
      symmetry ] ; revgoals.

Axiom ki_hybrid :
  forall (ℓ : nat),
  forall (LA : {fset Location}) (A : raw_package),
  forall i,
    ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
  (AdvantageE (Gcore_hyb ℓ) (Gcore_hyb (ℓ + 1)) (Ai A i) <=
  Advantage (λ x : bool, Gxtr_es ℓ x) (Ai A i ∘ R_es ℓ) + Advantage (λ x : bool, Gxtr_hs ℓ x) (Ai A i ∘ R_hs ℓ) +
    Advantage (λ x : bool, Gxtr_as ℓ x) (Ai A i ∘ R_as ℓ) + sumR_l [:: XPR_N; XPR_PSK; XPR_ESALT] (λ n : XPR, Advantage (λ x : bool, Gxpd n ℓ x) (Ai A i ∘ R_ n ℓ)))%R.

Lemma key_schedule_theorem :
  forall (d : nat) (M : chHandle -> nat),
  forall (PrntN : name -> raw_code (chName × chName)) (Labels : name -> bool -> raw_code label_ty),
  forall (S : Simulator d),
  forall (hash : nat),
  forall (LA : {fset Location}) (A : raw_package),
    ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
  forall (H_ε_acr : (sumR_l [:: R_cr; R_Z; R_D] (λ R : package f_parameter_cursor_loc (fset [::]) (fset [::]), Advantage (λ x : bool, Gacr x) (A ∘ R)) <= ε_acr)%R),
  forall (H_ε_sodh_ki : (forall i, Advantage (λ x : bool, Gsodh x) (Ai A i ∘ R_sodh) + AdvantageE Gcore_ki (Gcore_ideal d S) (Ai A i) <= ε_sodh_ki i)%R),
    (AdvantageE
       (Gks_real d PrntN Labels)
       (Gks_ideal d S PrntN Labels) A <=
     ε_acr +
     maxR (fun i =>
      ε_sodh_ki i
      +sumR 0 (d-1) (fun ℓ =>
         Advantage (Gxtr_es ℓ) (Ai A i ∘ R_es ℓ)
        +Advantage (Gxtr_hs ℓ) (Ai A i ∘ R_hs ℓ)
        +Advantage (Gxtr_as ℓ) (Ai A i ∘ R_as ℓ)
        +sumR_l [XPR_N; XPR_PSK; XPR_ESALT] (fun n => Advantage (Gxpd n ℓ) (Ai A i ∘ R_ n ℓ)
       )))
    )%R.
Proof.
  intros.
  rewrite (main_reduction d M).

  eapply Order.le_trans.
  - eapply (core_theorem _ _ _ _ _).
    apply H.
  - apply Num.Theory.lerD ; [ apply H_ε_acr | ].
    apply max_leq.
    intros i.

    eapply Order.le_trans.
    + apply Num.Theory.lerD ; [ easy | ].
      epose (equation20_eq d S i).
      eapply i0.
      easy.
    + rewrite addrA.
      apply Num.Theory.lerD ; [ apply H_ε_sodh_ki | ].
      apply sumR_le.
      intros ℓ.
      eapply ki_hybrid.
      easy.
Qed.

(* (*** Concrete instance *) *)

(* Theorem Advantage_xtr_es : *)
(*   forall A ℓ i ε_dt, *)
(*     Advantage (Gxtr_es ℓ) (Ai A i ∘ R_es ℓ) <= ε_dt. *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)
