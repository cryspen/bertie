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

Section KeyPackages.

Context {O_star : list name}.

Notation " 'chUNQinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chUNQout' " :=
  (chHandle)
    (in custom pack_type at level 2).

Definition UNQ (n : name) : nat := 14.

Definition UNQ_O_star : Interface :=
  interface_foreach (fun n => [interface #val #[ UNQ n ] : chUNQinp → chUNQout]) (O_star).

Definition SET_O_star_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (O_star) d.

Definition GET_O_star_ℓ (d : nat) : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (O_star) d.

(* Fig 13-14. K key and log *)

Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit.
Inductive ZAF := | Z | A | F.

Axiom level : chHandle -> nat.

Definition fin_Log_table : finType :=
  Casts.prod_finType (Casts.prod_finType fin_handle 'bool) fin_key.
Definition chLog_table := chFin (mkpos #|fin_Log_table|).

Definition fset_Log_table (Log_table : chHandle -> nat) : {fset Location}. Admitted.
Lemma in_Log_table : forall Log_table x, ('option chLog_table; Log_table x) \in fset_Log_table Log_table.
Proof. Admitted.

(* Fig 13 *)
Definition L_package (n : name) (Log_table : chHandle -> nat) (P : ZAF) :
  package
    (fset_Log_table Log_table)
    [interface]
    [interface
       #val #[ UNQ n ] : chUNQinp → chUNQout
    ].
  refine [package
      #def #[ UNQ n (* n ℓ *) ] ('(h,hon,k) : chUNQinp) : chUNQout {
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
         set_at (Log_table h) fin_Log_table (otf h, hon, otf k) ;;
         ret h
      }
    ].

  unfold set_at.
  ssprove_valid ; apply (in_Log_table Log_table).
Qed.
Fail Next Obligation.

(* Fig 14 *)

Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool.
Definition chK_table := chFin (mkpos #|fin_K_table|).

Definition fset_K_table (K_table : chHandle -> nat) : {fset Location}. Admitted.
Lemma in_K_table : forall K_table x, ('option chK_table; K_table x) \in fset_K_table K_table.
Proof. Admitted.

Definition K_package (n : name) (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) (b : bool) (K_table : chHandle -> nat) :
  package
    (fset_K_table K_table)
    [interface
       #val #[ UNQ n ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k_star) : chSETinp) : chSETout {
        #import {sig #[ UNQ n ] : chUNQinp → chUNQout }
        as unq_fn ;;
        (* #import {sig #[ GET ] : chGETinp → chGETout } *)
        get_or_case_fn (H := _) (K_table h) fin_K_table chHandle (
            k ← ret (untag k_star) ;;
            k ←
              (if Datatypes.andb b hon
               then
                 x ← sample (uniform (H := pos_key) #|fin_key|) ;;
                 ret x
               else
                 ret k) ;;
            unq_fn (h, hon, k) ;;
            set_at (H := pos_prod pos_key pos_bool) (K_table h) (Casts.prod_finType fin_key 'bool) (otf k, hon) ;;
            ret h
          )
          (fun _ => ret h)
      } ;
      #def #[ GET n ℓ d ] (h : chGETinp) : chGETout {
        p ← get_or_fn (H := pos_prod pos_key pos_bool) (K_table h) fin_K_table
          (@fail _ ;; ret (chCanonical chK_table)) ;;
        let (k_star, hon) := (fto (fst (otf p)) , snd (otf p) : 'bool) : (chProd chKey 'bool) in
        k ← ret (tag (chHandle_to_chHash h) (chKey_to_chName k_star)) ;;
        ret (k, hon)
      }
    ].

  unfold get_or_fn.
  unfold get_or_case_fn.
  unfold set_at.

  ssprove_valid ; try apply (in_K_table K_table _).
  simpl.
  unfold SET.
  unfold GET.
  apply serialize_name_notin_different_index.

  all: easy.

  Unshelve.
  apply 'unit.
Defined.
Fail Next Obligation.

Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition K_O_star (d : nat) (b : bool) (K_table : chHandle -> nat) :
  package
  (fset_K_table K_table)
  (UNQ_O_star)
  (SET_O_star_ℓ d :|: GET_O_star_ℓ d) :=
  eq_rect_r [eta package (fset_K_table K_table) UNQ_O_star] (ℓ_packages d (fun n H => {package parallel_raw (List.map (fun y => pack (K_package y n d H b K_table)) O_star) #with valid_parable _ _ _ _ _ _ _ _ _}) _ _ _)
        (interface_hierarchy_foreachU
           (λ (n : name) (ℓ : nat), [interface #val #[SET n ℓ d] : chUNQinp → chUNQout ])
           (λ (n : name) (ℓ : nat), [interface #val #[GET n ℓ d] : chUNQout → chGETout ]) O_star d).
Next Obligation.
  intros.
  admit.
Admitted.
Next Obligation.
  intros.
  admit.
Admitted.
Next Obligation.
  intros.
  admit.
Admitted.
Next Obligation.
  intros.
  apply trimmed_parallel_raw.
  - admit.
  - admit.
Admitted.
Final Obligation.
  intros.
  admit.
Admitted.
Fail Next Obligation.

(* Fig 15 *)

Definition Nk_package (n : name) (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) (K_table : chHandle -> nat) :
  package
    (fset_K_table K_table)
    [interface
       #val #[ UNQ n ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ UNQ n ] : chUNQinp → chUNQout }
        as unq_fn ;;
        get_or_case_fn (K_table h) fin_K_table chHandle (
            unq_fn (h, hon, k) ;;
            set_at (K_table h) fin_K_table (otf k, hon) ;;
            ret h
          ) (fun _ => ret h)
      } ;
      #def #[ GET n ℓ d ] (h : chGETinp) : chGETout {
        p ← get_or_fail (K_table h) fin_K_table ;;
        let (k, hon) :=
          (fto (fst (otf p)) , snd (otf p) : 'bool) : (chProd chKey 'bool)
        in
        ret (k, hon)
      }
    ].

  unfold get_or_fn.
  unfold get_or_case_fn.
  unfold get_or_fail.
  unfold set_at.

  ssprove_valid ; try apply (in_K_table K_table _).
  apply serialize_name_notin_different_index.
  all: easy.
Defined.
Fail Next Obligation.

(* R-M-Pr-io^xpd - Interesting Fig 45., Fig.51-55 *)

Notation " 'chKinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chKout' " :=
  (chHandle)
    (in custom pack_type at level 2).
Definition K (n : chName) (ℓ : nat) := 10%nat.

(**** *)

Definition K_psk_1_0 K_table := K_package PSK 0 true K_table.
Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition K_psk_0_d (K_table : chHandle -> nat) (Sd : nat) :
  package (fset_K_table K_table) [interface #val #[UNQ PSK] : chKinp → chKout ]
       (interface_hierarchy
          (λ n : nat,
             [interface #val #[SET PSK n Sd] : chKinp → chKout ; #val #[GET PSK n Sd] : chKout → chGETout ])
          Sd) :=
  (ℓ_packages Sd (fun n H => K_package PSK n Sd H false K_table) _ _ _).
Next Obligation.
  intros.
  admit.
Admitted.
Next Obligation.
  intros.
  admit.
Admitted.

  (* := *)
  (* match Sd with *)
  (* | O => [package] *)
  (* | S d => {package (par (K_package PSK Sd false K_table) (K_psk_0_d K_table d))} *)
  (* end. *)
Fail Next Obligation.

End KeyPackages.
