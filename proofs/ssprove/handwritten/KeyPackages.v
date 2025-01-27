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

(*** Key packages *)

Section KeyPackages.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

Notation " 'chUNQinp' " :=
  (chHandle × 'bool × chKey)
    (in custom pack_type at level 2).
Notation " 'chUNQout' " :=
  (chHandle)
    (in custom pack_type at level 2).

Definition UNQ (n : name) : nat := 14.

Definition UNQ_O_star : Interface :=
  interface_foreach (fun n => [interface #val #[ UNQ n ] : chUNQinp → chUNQout]) (O_star).

Definition SET_O_star_ℓ : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d.+1 ] : chSETinp → chSETout]) (O_star) d.+1.

Definition GET_O_star_ℓ : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d.+1 ] : chGETinp → chGETout]) (O_star) d.+1.

(* Fig 13-14. K key and log *)

Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit.
Inductive ZAF := | Z | A | F.

(* Axiom level : chHandle -> nat. *)

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

(* Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool. *)
(* Definition chK_table := chFin (mkpos #|fin_K_table|). *)

(* Definition fset_K_table : {fset Location}. Admitted. *)
(* Lemma in_K_table : forall x, ('option chK_table; K_table x) \in fset_K_table. *)
(* Proof. Admitted. *)

Definition K_package (n : name) (ℓ : nat) (* (d : nat) *) (_ : (ℓ <= d.+1)%nat) (b : bool) :
  package
    L_K
    [interface
       #val #[ UNQ n ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d.+1 ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d.+1 ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d.+1 ] ('(h,hon,k_star) : chSETinp) : chSETout {
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
      #def #[ GET n ℓ d.+1 ] (h : chGETinp) : chGETout {
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

  ssprove_valid ; try apply (in_K_table _).
  simpl.
  unfold SET.
  unfold GET.
  apply serialize_name_notin_different_index.

  all: easy.

  Unshelve.
  apply 'unit.
Defined.
Fail Next Obligation.

(* Lemma interface_foreach_idents_names : forall n ℓ (* d *) f L, *)
(*     (ℓ < n)%N -> *)
(*     idents (interface_foreach f L) *)
(*   :#: idents *)
(*   (interface_foreach f L). *)
(* Proof. *)
(*   intros. *)

Ltac solve_idents_for_K_O_star := try unfold idents ; rewrite !imfsetU ; solve_imfset_disjoint ; repeat (apply /andP ; split); ((try now apply serialize_name_notin_different_index) ; (try now apply serialize_name_notin_different_name)).

Theorem all_O_star_disjoint :
  forall n,
    (n <= d.+1)%nat ->
  all_idents_disjoint
    (λ n0 : name,
       [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout ;
        #val #[GET n0 n d.+1] : chUNQout → chGETout ]) O_star.
Proof.
  intros.

  replace (λ n0 : name,
       [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout ;
        #val #[GET n0 n d.+1] : chUNQout → chGETout ]) with
    (λ n0 : name,
       [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout] :|: [interface
                                                                      #val #[GET n0 n d.+1] : chUNQout → chGETout ]) by now setoid_rewrite <- fset_cat.

  simpl.
  repeat split.

  all: try unfold idents ; rewrite !imfsetU.
  all: rewrite !fdisjointUr.
  all: repeat (apply /andP ; split).
  all: rewrite !fdisjointUl.
  all: repeat (apply /andP ; split).
  all: rewrite <- !fset1E.
  all: rewrite !imfset1.
  all: try rewrite !fdisjoints1.

  all:
    match goal with
    | [ |- context [ SET ?name ?ℓ ?d \notin fset1 (GET ?name ?n ?d) ] ] =>
        now apply serialize_name_notin_different_index
    | [ |- context [ SET ?name1 ?ℓ ?d \notin fset1 (SET ?name2 ?n ?d) ] ] =>
        now apply serialize_name_notin_different_name
    | [ |- context [ SET ?name1 ?ℓ ?d \notin fset1 (GET ?name2 ?n ?d) ] ] =>
        now apply serialize_name_notin_different_index
    | [ |- context [ GET ?name ?ℓ ?d \notin fset1 (SET ?name ?n ?d) ] ] =>
        now apply serialize_name_notin_different_index
    | [ |- context [ GET ?name1 ?ℓ ?d \notin fset1 (SET ?name2 ?n ?d) ] ] =>
        now apply serialize_name_notin_different_index
    | [ |- context [ GET ?name1 ?ℓ ?d \notin fset1 (GET ?name2 ?n ?d) ] ] =>
        now apply serialize_name_notin_different_name
    end.
Qed.

Theorem trimmed_pairs_O_star :
  forall n b H,
  trimmed_pairs
    (@List.map name Interface
       (fun n0 : name =>
        @fset
          (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
             (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                choice_type_choice_type__canonical__Ord_Ord))
          (@cons (prod nat (prod choice_type choice_type))
             (@pair nat (prod choice_type choice_type) (SET n0 n (S (@d DepInstance)))
                (@pair choice_type choice_type (chProd (chProd chHandle chBool) chKey) chHandle))
             (@cons (prod nat (prod choice_type choice_type))
                (@pair nat (prod choice_type choice_type) (GET n0 n (S (@d DepInstance)))
                   (@pair choice_type choice_type chHandle (chProd chKey chBool)))
                (@nil (prod nat (prod choice_type choice_type)))))) O_star)
    (@List.map name raw_package (fun y : name => @pack _ _ _ (K_package y n H b)) O_star).
Proof.
  intros.
  unfold O_star.
  unfold List.map.
  unfold trimmed_pairs.
  repeat split.
  all: repeat (apply trimmed_empty_package || apply trimmed_package_cons).
Qed.

Theorem valid_pairs_O_star :
  forall n b H,
  valid_pairs (@L_K DepInstance)
    (@List.map name Interface
       (fun n0 : name =>
        @fset
          (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
             (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                choice_type_choice_type__canonical__Ord_Ord))
          (@cons (prod nat (prod choice_type choice_type))
             (@pair nat (prod choice_type choice_type) (UNQ n0)
                (@pair choice_type choice_type (chProd (chProd chHandle chBool) chKey) chHandle))
             (@nil (prod nat (prod choice_type choice_type))))) O_star)
    (@List.map name Interface
       (fun n0 : name =>
        @fset
          (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
             (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                choice_type_choice_type__canonical__Ord_Ord))
          (@cons (prod nat (prod choice_type choice_type))
             (@pair nat (prod choice_type choice_type) (SET n0 n (S (@d DepInstance)))
                (@pair choice_type choice_type (chProd (chProd chHandle chBool) chKey) chHandle))
             (@cons (prod nat (prod choice_type choice_type))
                (@pair nat (prod choice_type choice_type) (GET n0 n (S (@d DepInstance)))
                   (@pair choice_type choice_type chHandle (chProd chKey chBool)))
                (@nil (prod nat (prod choice_type choice_type)))))) O_star)
    (@List.map name raw_package (fun y : name => @pack _ _ _ (K_package y n H b)) O_star).
Proof.
  intros.
  unfold O_star.
  unfold List.map.
  unfold valid_pairs.
  repeat split.
  all: apply K_package.
Qed.

Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition K_O_star (b : bool) :
  package
  (L_K)
  (UNQ_O_star)
  (SET_O_star_ℓ :|: GET_O_star_ℓ).

rewrite interface_hierarchy_foreachU.
replace ((λ (n : name) (ℓ : nat),
           [interface #val #[SET n ℓ d.+1] : chUNQinp → chUNQout ]
             :|: [interface #val #[GET n ℓ d.+1] : chUNQout → chGETout ]))
  with ((λ (n : name) (ℓ : nat),
          [interface #val #[SET n ℓ d.+1] : chUNQinp → chUNQout ;
           #val #[GET n ℓ d.+1] : chUNQout → chGETout ])) by now setoid_rewrite <- fset_cat.

(* assert (fun n H => valid_pairs L_K (List.map (λ n0 : name, [interface #val #[UNQ n0] : chUNQinp → chUNQout ]) O_star) *)
(*     (List.map *)
(*        (λ n0 : name, *)
(*           [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout ; *)
(*                      #val #[GET n0 n d.+1] : chUNQout → chGETout ]) O_star) *)
(*     (List.map (λ y : name, K_package y n H b) O_star)). *)

refine (ℓ_packages d.+1 (fun n H => {package parallel_raw (List.map (fun y => pack (K_package y n H b)) O_star) #with valid_parable _ _ _ _ _ _ (all_O_star_disjoint _ H) (trimmed_pairs_O_star _ _ _) (valid_pairs_O_star n b H)}) _ (fun _ H => trimmed_parallel_raw _ _ _ (all_O_star_disjoint _ H) (trimmed_pairs_O_star _ _ _)) _).
1:{
  intros.

  (* unfold XPR, XPD, serialize_name, idents. *)
  (* simpl. *)

  replace (λ n0 : name,
       [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout ;
        #val #[GET n0 n d.+1] : chUNQout → chGETout ]) with
    (λ n0 : name,
       [interface #val #[SET n0 n d.+1] : chUNQinp → chUNQout] :|: [interface
                                                                      #val #[GET n0 n d.+1] : chUNQout → chGETout ]) by now setoid_rewrite <- fset_cat.

  replace (λ n0 : name,
       [interface #val #[SET n0 ℓ d.+1] : chUNQinp → chUNQout ;
        #val #[GET n0 ℓ d.+1] : chUNQout → chGETout ]) with
    (λ n0 : name,
       [interface #val #[SET n0 ℓ d.+1] : chUNQinp → chUNQout] :|: [interface
                                                                      #val #[GET n0 ℓ d.+1] : chUNQout → chGETout ]) by now setoid_rewrite <- fset_cat.

  unfold O_star, idents.
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
  all: try now apply serialize_name_notin.
  all: now apply serialize_name_notin_different_index.
}
Defined. (* Slow .. *)
Fail Next Obligation.

(* Fig 15 *)

Definition Nk_package (n : name) (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) :
  package
    L_K
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

  ssprove_valid ; try apply (in_K_table _).
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

Definition K_psk_1_0 := K_package PSK 0 (ltac:(Lia.lia)) true.
Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition K_psk_0_d :
  package (L_K) [interface #val #[UNQ PSK] : chKinp → chKout ]
       (interface_hierarchy
          (λ n : nat,
             [interface #val #[SET PSK n d.+1] : chKinp → chKout ; #val #[GET PSK n d.+1] : chKout → chGETout ])
          d.+1) :=
  (ℓ_packages d.+1 (fun n H => K_package PSK n H false) _ _ _).
Next Obligation.
  intros.
  repeat (apply trimmed_empty_package || apply trimmed_package_cons).
Qed.
Next Obligation.
  intros.

  all: try unfold idents.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  all: rewrite !fdisjointUr.
  all: repeat (apply /andP ; split).
  all: rewrite !fdisjointUl.
  all: repeat (apply /andP ; split).
  all: rewrite !imfset1.
  all: try rewrite !fdisjoints1.

  all: try now apply serialize_name_notin.
  all: try now apply serialize_name_notin_different_index.
Qed.
Fail Next Obligation.

End KeyPackages.
