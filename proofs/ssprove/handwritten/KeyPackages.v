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

(*** Key packages *)

Notation " 'chUNQinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chUNQout' " :=
  (chHandle)
    (in custom pack_type at level 2).

Definition UNQ (n : O_star) : nat := 14.

Definition UNQ_o_star :=
  [interface
     #val #[ UNQ TODO ] : 'unit → 'unit
  ].

Definition K_package (n : chName) (ℓ : nat) (b : bool) (K_table : chHandle -> nat) :
  package
    fset0
    [interface
       #val #[ UNQ TODO ] : chUNQinp → chUNQout
    ]
    [interface].
  refine [package
      #def #[ SET (* n ℓ *) ] ('(h,hon,k_star) : chSETinp) : chSETout {
        #import {sig #[ UNQ TODO ] : chUNQinp → chUNQout }
        as unq_fn ;;
        (* #import {sig #[ GET ] : chGETinp → chGETout } *)
           get_or_fn (K_table h) chHandle (
               k ← ret (untag k_star) ;;
               k ←
                 (if Datatypes.andb b hon
                  then
                    x ← sample uniform #| _ | ;;
                    ret (otf x)
                  else
                    ret k) ;;
               unq_fn (h, hon, k) ;;
               set_at (K_table h) (chKey × 'bool) (k, hon) ;;
               ret h
             )
      } ;
      #def #[ GET (* n ℓ *) ] (h : chGETinp) : chGETout {
        '(k_star, hon) ← get_or_fn (K_table h) (chKey × 'bool) _ (* (@fail _ ;; ret (chKey × 'bool)) *) ;;
        k ← ret (tag _ _) ;;
        ret (k, hon)
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

Definition Nk_package (n : chName) (K_table : chHandle -> nat) :
  package
    fset0
    [interface
       #val #[ UNQ TODO ] : chUNQinp → chUNQout
    ]
    [interface].
  refine [package
      #def #[ SET (* n ℓ *) ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ UNQ TODO ] : chUNQinp → chUNQout }
        as unq_fn ;;
        (* #import {sig #[ GET ] : chGETinp → chGETout } *)
           get_or_fn (K_table h) chHandle (
               unq_fn (h, hon, k) ;;
               set_at (K_table h) (chKey × 'bool) (k, hon) ;;
               ret h
             )
      } ;
      #def #[ GET (* n ℓ *) ] (h : chGETinp) : chGETout {
        '(k, hon) ← get_or_fn (K_table h) (chKey × 'bool) _ (* (@fail _ ;; ret (chKey × 'bool)) *) ;;
        ret (k, hon)
      }
    ].
Admitted.
Admit Obligations.
Fail Next Obligation.

(* R-M-Pr-io^xpd - Interesting Fig 45., Fig.51-55 *)

Axiom Key_o_star_ideal : forall (d : nat), package
    fset0
    (GET_o_star_ℓ d)
    (UNQ_o_star).


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
