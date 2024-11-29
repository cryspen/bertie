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

From KeyScheduleTheorem Require Import ssp_helper.

(*** XTR / XPD *)

(* p. 5,6 *)
Axiom xtr_angle : name -> chHandle -> chHandle -> raw_code chHandle.

Axiom xtr : chKey -> chKey -> raw_code chKey.

(* Xtr *)

Notation " 'chXTRinp' " :=
  (chHandle × chHandle)
    (in custom pack_type at level 2).
Notation " 'chXTRout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition XTR (n : name) (ℓ (* 0 .. d *) : nat) : nat := 13.

Definition Xtr
  (n : name) (ℓ : nat) (b : bool)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
  :
  package
    fset0
    [interface
      #val #[ GET ] : chGETinp → chGETout ;
      #val #[ SET ] : chSETinp → chSETout
    ]
    [interface
       #val #[ XTR n ℓ ] : chXTRinp → chXTRout
    ].
  refine [package
     #def #[ XTR n ℓ ] ('(h1,h2) : chXTRinp) : chXTRout {
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
               k_star ← sample (uniform (H := pos_chName) #| chName |) ;;
               ret (tag (alg k) (otf k_star : chName))
             else ret k) ;;
        h ← set_fn (h, hon, k) ;;
        ret h
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

Fixpoint interface_hierarchy (f : nat -> Interface) (ℓ : nat) : Interface :=
  match ℓ with
  | O => [interface]
  | S n => f n :|: interface_hierarchy f n
  end.

Fixpoint ℓ_raw_packages
  (p : forall (n : nat), raw_package)
  (d : nat)
  {struct d}:
  raw_package :=
  match d with
  | O => emptym
  | S d' =>
      par (p d') (@ℓ_raw_packages p d')
  end.
Program Definition ℓ_packages {L I}
  {f : nat -> Interface}
  (p : forall (n : nat), package L I (f n))
  (H : forall d, Parable (p d) (ℓ_raw_packages p d))
  (d : nat)
  : package L I (interface_hierarchy f d) :=
  {package ℓ_raw_packages p d}.
Next Obligation.
  induction d.
  - apply valid_empty_package.
  - simpl.
    rewrite <- (fsetUid L).
    rewrite <- (fsetUid I).
    apply valid_par.
    + apply H.
    + apply p.
    + apply IHd.
Defined.

Definition XTR_n_ℓ d :=
  interface_hierarchy (fun d' => [interface
       #val #[ XTR ES d' ] : chXTRinp → chXTRout ;
       #val #[ XTR HS d' ] : chXTRinp → chXTRout ;
       #val #[ XTR AS d' ] : chXTRinp → chXTRout]) d.

Program Definition XTR_packages
  (d : nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
  :
  package fset0 [interface
      #val #[ GET ] : chGETinp → chGETout ;
      #val #[ SET ] : chSETinp → chSETout
    ] (XTR_n_ℓ d) :=
  ℓ_packages (fun d' =>
      {package (par
         (par
            (Xtr ES d' false PrntN Labels)
            (Xtr AS d' false PrntN Labels))
          (Xtr HS d' false PrntN Labels))}) _ d.
Next Obligation.
  intros.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + apply (Xtr ES d' false PrntN Labels).
    + apply (Xtr AS d' false PrntN Labels).
    + rewrite fsetUid. apply fsubsetxx.
    + rewrite fsetUid. apply fsubsetxx.
    + apply fsubsetxx.
  - apply (Xtr HS d' false PrntN Labels).
  - rewrite fsetUid. apply fsubsetxx.
  - rewrite fsetUid. apply fsubsetxx.
  - rewrite <- !fset_cat. simpl.
    apply fsubsetxx.
Admitted.
Next Obligation.
Admitted.
Fail Next Obligation.


(* Xpd *)

Axiom xpd : chKey -> (label_ty * bitvec) -> raw_code chKey.

Notation " 'chXPDinp' " :=
  (chHandle × 'bool × bitvec)
    (in custom pack_type at level 2).
Notation " 'chXPDout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition XPD (n : name) (ℓ : nat) : nat := 13.

Definition Xpd
  (n : name) (ℓ : nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
  :
  package
    fset0
    [interface
     #val #[ GET ] : chGETinp → chGETout ;
     #val #[ SET ] : chSETinp → chSETout ;
     #val #[ HASH ] : chHASHinp → chHASHout
    ]
    [interface
       #val #[ XPD n ℓ ] : chXPDinp → chXPDout
    ].
  refine [package
      #def #[ XPD n ℓ ] ('(h1,r,args) : chXPDinp) : chXPDout {
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
Admitted.
Admit Obligations.
Fail Next Obligation.

Definition XPD_n_ℓ (d : nat) :=
  interface_hierarchy (fun d' => [interface
       #val #[ XPD N d' ] : chXPDinp → chXPDout ;
       #val #[ XPD PSK d' ] : chXPDinp → chXPDout ;
       #val #[ XPD ESALT d' ] : chXPDinp → chXPDout
      ]) d.

Program Definition XPD_packages (d : nat)
  (PrntN : name -> raw_code (chName × chName))
  (Labels : name -> bool -> raw_code label_ty)
:
  package fset0 [interface
      #val #[ GET ] : chGETinp → chGETout ;
      #val #[ SET ] : chSETinp → chSETout ;
      #val #[ HASH ] : chHASHinp → chHASHout
    ] (XPD_n_ℓ d) :=
  ℓ_packages (fun d' =>
      {package (par
         (par
            (Xpd N d' PrntN Labels)
            (Xpd PSK d' PrntN Labels))
          (Xpd ESALT d' PrntN Labels))}) _ d.
Next Obligation.
  intros.
  unfold pack.
  eapply valid_par_upto.
  - admit.
  - eapply valid_par_upto.
    + admit.
    + apply (Xpd N d' PrntN Labels).
    + apply (Xpd PSK d' PrntN Labels).
    + solve_in_fset.
    + apply fsubsetxx.
    + apply fsubsetxx.
  - apply (Xpd ESALT d' PrntN Labels).
  - rewrite fsetU0. apply fsubsetxx.
  - rewrite !fsetUid. apply fsubsetxx.
  - rewrite <- !fset_cat. simpl. apply fsubsetxx.
Admitted.
Next Obligation.
Admitted.
Fail Next Obligation.

