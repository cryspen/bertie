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

(*** Helper *)


(*** Key packages *)

Section KeyPackages.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

Definition UNQ_O_star : Interface :=
  interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) (O_star).

Definition SET_O_star_ℓ : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (O_star) d.

Definition GET_O_star_ℓ : Interface :=
  interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (O_star) d.

(* Fig 13-14. K key and log *)

(* Axiom exists_h_star : (chHandle -> raw_code 'unit) -> raw_code 'unit. *)
Inductive ZAF := | Z | A | F.

(* Axiom level : chHandle -> nat. *)

(* Fig 13 *)
Definition L_package (n : name) (P : ZAF) :
  package
    (* (fset_Log_table Log_table) *)
    L_L
    [interface]
    [interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ].
  refine [package
      #def #[ UNQ n d (* n ℓ *) ] ('(h,hon,k) : chUNQinp) : chUNQout {
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
         set_at (L_table h) fin_L_table (otf h, hon, otf k) ;;
         ret h
      }
    ].

  unfold set_at.
  ssprove_valid ; apply (in_L_table _).
Defined.
Fail Next Obligation.

(* Fig 14 *)

(* Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool. *)
(* Definition chK_table := chFin (mkpos #|fin_K_table|). *)

(* Definition fset_K_table : {fset Location}. Admitted. *)
(* Lemma in_K_table : forall x, ('option chK_table; K_table x) \in fset_K_table. *)
(* Proof. Admitted. *)

Definition K_package (n : name) (ℓ : nat) (* (d : nat) *) (_ : (ℓ <= d)%nat) (b : bool) :
  package
    L_K
    [interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k_star) : chSETinp) : chSETout {
        #import {sig #[ UNQ n d ] : chUNQinp → chUNQout }
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
            set_at (H := pos_prod pos_key pos_bool) (K_table h) fin_K_table (otf k, hon) ;;
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

  ssprove_valid ; try apply (in_K_table _).
  simpl.
  unfold SET.
  unfold GET.
  rewrite notin_cons. rewrite Bool.andb_true_r.
  apply /eqP.
  now apply serialize_name_notin_different_index.

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

Theorem all_set_get_disjoint :
  forall n,
    (n <= d)%nat ->
  ∀ x y : ExtraTypes_name__canonical__eqtype_Equality,
    x ≠ y
    → idents
        [interface #val #[SET x n d] : chSETinp → chSETout ;
                   #val #[GET x n d] : chGETinp → chGETout ]
      :#: idents
            [interface #val #[SET y n d] : chSETinp → chSETout ;
                       #val #[GET y n d] : chGETinp → chGETout ].
Proof.
  intros.
  intros.
  replace ([interface #val #[SET x n d] : chSETinp → chSETout ; #val #[GET x n d] : chGETinp → chGETout ]) with
    ([interface #val #[SET x n d] : chSETinp → chSETout] :|: [interface #val #[GET x n d] : chGETinp → chGETout ]) by now rewrite <- fset_cat.
  replace ([interface #val #[SET y n d] : chSETinp → chSETout ; #val #[GET y n d] : chGETinp → chGETout ]) with
    ([interface #val #[SET y n d] : chSETinp → chSETout] :|: [interface #val #[GET y n d] : chGETinp → chGETout ]) by now rewrite <- fset_cat.

  unfold idents.
  rewrite !imfsetU.
  solve_imfset_disjoint.
Qed.

Theorem trimmed_pairs_list (Names : list name) :
  forall n b H,
  trimmed_pairs
    (@List.map name Interface
       (fun n0 : name =>
        [interface #val #[ SET n0 n ((@d DepInstance)) ] : chSETinp → chSETout ;
               #val #[ (GET n0 n ((@d DepInstance))) ] : chGETinp → chGETout ]) Names)
    (@List.map name raw_package (fun y : name => @pack _ _ _ (K_package y n H b)) Names).
Proof.
  intros.
  unfold List.map.
  induction Names.
  - easy.
  - unfold List.map.
    unfold trimmed_pairs ; fold trimmed_pairs.

    assert (trimmed
    [interface #val #[SET a n d] : chUNQinp → chUNQout ; #val #[GET a n d] : chUNQout → chGETout ]
    (K_package a n H b)).
    {
      clear IHNames.
      apply trimmed_package_cons.
      apply trimmed_package_cons.
      apply trimmed_empty_package.
    }

    destruct Names ; [ apply H0 | split ; [ apply H0  | apply IHNames ] ].
Qed.

Theorem valid_pairs_K_list (Names : list name) :
  forall n b H,
  valid_pairs (@L_K DepInstance)
    (@List.map name Interface
       (fun n0 : name =>
          [interface #val #[ UNQ n0 d ] : chSETinp → chSETout ]) Names)
    (@List.map name Interface
       (fun n0 : name =>
          [interface
             #val #[ SET n0 n ((@d DepInstance)) ] : chSETinp → chSETout ;
             #val #[ (GET n0 n ((@d DepInstance))) ] : chGETinp → chGETout ]) Names)
    (@List.map name raw_package (fun y : name => @pack _ _ _ (K_package y n H b)) Names).
Proof.
  intros.
  induction Names.
  - easy.
  - unfold List.map.
    unfold valid_pairs ; fold valid_pairs.

    assert (valid_package L_K [interface #val #[UNQ a d] : chUNQinp → chUNQout ]
        [interface #val #[SET a n d] : chUNQinp → chUNQout ; #val #[GET a n d] : chUNQout → chGETout ]
        (K_package a n H b)).
    {
      apply K_package.
    }

    destruct Names ; [ apply H0 | split ; [ apply H0  | apply IHNames ] ].
Qed.

Definition Ls (Names : list name) (P : ZAF) :
  uniq Names ->
  package
    (L_L)
    [interface]
    (interface_foreach (fun n =>[interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ]) Names).
Proof.
  intros.
  epose ({package parallel_raw (List.map (fun y => pack (L_package y P)) Names)
           #with
            valid_parable _ (λ n : name, [interface #val #[UNQ n d] : chUNQinp → chDHEXPout ]) (fun x => [interface]) _ Names Names _ H _ _}).
  destruct Names ; [ refine {package _ #with valid_empty_package _ _} | ].
  rewrite <- interface_foreach_trivial in p ; [ | easy ].
  apply p.
  Unshelve.
  - intros.
    unfold idents.
    solve_imfset_disjoint.
  - clear.
    induction Names.
    + easy.
    + unfold List.map.
      unfold trimmed_pairs ; fold trimmed_pairs.

      assert (trimmed
                [interface #val #[UNQ a d] : chUNQinp → chUNQout ]
                (L_package a P)).
      {
        clear IHNames.
        apply trimmed_package_cons.
        apply trimmed_empty_package.
      }

      destruct Names ; [ apply H | split ; [ apply H  | apply IHNames ] ].
  - clear.
    induction Names.
    + easy.
    + unfold List.map.
      unfold valid_pairs ; fold valid_pairs.

      destruct Names ; [ apply (L_package a P) | split ; [ apply (L_package a P)  | apply IHNames ] ].
Qed.

Definition Ks (Names : list name) (b : bool) :
  uniq Names ->
  package
  (L_K)
  (interface_foreach (fun n => [interface #val #[ UNQ n d ] : chUNQinp → chUNQout]) Names)
  (interface_hierarchy_foreach (fun n ℓ => [interface #val #[ SET n ℓ d ] : chSETinp → chSETout]) (Names) d
     :|: interface_hierarchy_foreach (fun n ℓ => [interface #val #[ GET n ℓ d ] : chGETinp → chGETout]) (Names) d
  ).
Proof.
  intros.
  rewrite interface_hierarchy_foreachU.
  replace ((λ (n : name) (ℓ : nat),
             [interface #val #[SET n ℓ d] : chSETinp → chSETout ]
               :|: [interface #val #[GET n ℓ d] : chGETinp → chGETout ]))
    with ((λ (n : name) (ℓ : nat),
            [interface #val #[SET n ℓ d] : chSETinp → chSETout ;
             #val #[GET n ℓ d] : chGETinp → chGETout ])) by now setoid_rewrite <- fset_cat.

  refine (ℓ_packages d
            (fun n H => {package parallel_raw (List.map (fun y => pack (K_package y n H b)) Names) #with valid_parable _ _ _ _ _ _ (all_set_get_disjoint n H) _ (trimmed_pairs_list Names _ _ _) (valid_pairs_K_list Names n b H)})
            _
            (fun n H => trimmed_parallel_raw _ _ _ (all_set_get_disjoint n H) _ (trimmed_pairs_list Names _ _ _)) _).
  1,2: apply H0.
  1:{
    intros.

    replace (λ x : name,
                [interface
                   #val #[SET x n d] : chSETinp → chSETout ;
                 #val #[GET x n d] : chGETinp → chGETout ]) with
      (λ n0 : name,
          [interface #val #[SET n0 n d] : chSETinp → chSETout]
            :|: [interface #val #[GET n0 n d] : chGETinp → chGETout ]) by now setoid_rewrite <- fset_cat.
    replace (λ n0 : name,
                [interface #val #[SET n0 ℓ d] : chSETinp → chSETout ;
                 #val #[GET n0 ℓ d] : chGETinp → chGETout ]) with
      (λ n0 : name,
          [interface #val #[SET n0 ℓ d] : chSETinp → chSETout]
            :|: [interface #val #[GET n0 ℓ d] : chGETinp → chGETout ])
      by now setoid_rewrite <- fset_cat.

    apply idents_foreach_disjoint_foreach.
    intros.
    unfold idents.
    rewrite !imfsetU.
    solve_imfset_disjoint.
  }
Defined.
Fail Next Obligation.


Obligation Tactic := (* try timeout 8 *) idtac.
Definition K_O_star (b : bool) :
  package
  (L_K)
  (UNQ_O_star)
  (SET_O_star_ℓ :|: GET_O_star_ℓ) :=
  Ks O_star b (ltac:(reflexivity)).
Fail Next Obligation.

(* Fig 15 *)

Definition Nk_package (n : name) (ℓ : nat) (d : nat) (_ : (ℓ <= d)%nat) :
  package
    L_K
    [interface
       #val #[ UNQ n d ] : chUNQinp → chUNQout
    ]
    [interface
       #val #[ SET n ℓ d ] : chSETinp → chSETout ;
       #val #[ GET n ℓ d ] : chGETinp → chGETout
    ].
  refine [package
      #def #[ SET n ℓ d ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ UNQ n d ] : chUNQinp → chUNQout }
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
  solve_imfset_disjoint.
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
  package (L_K) [interface #val #[UNQ PSK d] : chKinp → chKout ]
       (interface_hierarchy
          (λ n : nat,
             [interface #val #[SET PSK n d] : chKinp → chKout ; #val #[GET PSK n d] : chKout → chGETout ])
          d) :=
  (ℓ_packages d (fun n H => K_package PSK n H false) _ _ _).
Next Obligation.
  intros.
  repeat (apply trimmed_empty_package || apply trimmed_package_cons).
Qed.
Next Obligation.
  intros.
  unfold idents.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  rewrite fset_cons ; rewrite imfsetU ; rewrite <- fset1E.
  solve_imfset_disjoint.
Qed.
Fail Next Obligation.

End KeyPackages.
