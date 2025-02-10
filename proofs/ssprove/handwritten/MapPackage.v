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

From KeyScheduleTheorem Require Import ssp_helper.

From KeyScheduleTheorem Require Import BasePackages.
From KeyScheduleTheorem Require Import KeyPackages.
From KeyScheduleTheorem Require Import XTR_XPD.

From KeyScheduleTheorem Require Import Core.
From KeyScheduleTheorem Require Import KeySchedulePackages.

(*** Helper definitions *)


From elpi Require Import elpi.
Elpi Tactic undup.
Elpi Accumulate lp:{{
/*(*/
  pred same-goal i:sealed-goal, i:sealed-goal.
  same-goal (nabla G1) (nabla G2) :-
    % TODO: proof variables could be permuted
    pi x\ same-goal (G1 x) (G2 x).
  same-goal (seal (goal Ctx1 _ Ty1 P1 _) as G1)
            (seal (goal Ctx2 _ Ty2 P2 _) as G2) :-
    same-ctx Ctx1 Ctx2,
    % this is an elpi builtin, aka same_term, which does not
    % unify but rather compare two terms without assigning variables
    Ty1 == Ty2,
    P1 = P2.

  pred same-ctx i:goal-ctx, i:goal-ctx.
  same-ctx [] [].
  same-ctx [decl V _ T1|C1] [decl V _ T2|C2] :-
    % TODO: we could compare up to permutation...
    % TODO: we could try to relate def and decl
    T1 == T2,
    same-ctx C1 C2.

  pred undup i:sealed-goal, i:list sealed-goal, o:list sealed-goal.
  undup _ [] [].
  undup G [G1|GN] GN :- same-goal G G1.
  undup G [G1|GN] [G1|GL] :- undup G GN GL.

  msolve [G1|GS] [G1|GL] :-
    % TODO: we could find all duplicates, not just
    % copies of the first goal...
    undup G1 GS GL.
/*)*/
}}.


(*** Package *)

Section MapPackages.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.

(* Context {L_M : {fset Location} }. *)
(* Context {PrntIdx : name -> forall (ℓ : bitvec), code fset0 [interface] (chProd chName chName)}. *)
(* Context {PrntN: name -> code fset0 fset0 (chName × chName)}. *)
(* Context {Labels : name -> bool -> code fset0 fset0 chLabel}. *)

(* Axiom XTR_LABAL_from_index : nat -> name. *)
(* Axiom XPN_LABAL_from_index : nat -> name. *)
Axiom level : chHandle -> code fset0 [interface] (chOption chNat).

Definition KS_interface d :=
  ([interface #val #[SET PSK 0 d] : chSETinp → chSETout ]
     :|: DH_interface
     :|: (XPD_n_ℓ d :|: XTR_n_ℓ d)
     :|: GET_O_star_ℓ d
  ).

Notation " 'chXTRinp' " :=
  (chHandle × chHandle)
    (in custom pack_type at level 2).
Notation " 'chXTRout' " :=
  (chHandle)
    (in custom pack_type at level 2).
(* Context {xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle}. *)

(* fig. 29 *)
Definition R_ch_map_XTR_package d (ℓ : nat) (n : name) (M : name -> chHandle -> nat) :
  (List.In n XTR_names) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  package L_M (XTR_n_ℓ d (* ℓ.+1 *))
    [interface
       #val #[ XTR n ℓ d (* ℓ.+1 *)] : chXTRinp → chXTRout
    ].
Proof.
  intros.
  refine [package
     #def #[ XTR n ℓ d (* ℓ.+1 *) ] ('(h1,h2) : chXTRinp) : chXTRout {
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

        assertD (ℓ' <= d)%nat (fun H =>
        #import {sig #[ XTR n ℓ' d (* ℓ.+1 *) ] : chXTRinp → chXTRout }
        as XTR_fn ;;
        h ← xtr_angle n h1 h2 ;;
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
    apply xtr_angle.
  }
  {
    unfold XTR_n_ℓ.
    set (o := mkopsig _ _ _) ; pattern x2 in o ; subst o.
    apply lower_level_in_interface.
    2: apply x3.

    epose serialize_name_notin.
    unfold XTR_names, interface_foreach, List.fold_left.
    unfold mkopsig.
    rewrite <- !fset1E.
    rewrite !in_fsetU.
    rewrite !in_fset1.
    unfold XTR_names in H.

    repeat (destruct H as [ | H ] ; [subst ; repeat (apply /orP ; ((left ; now apply /eqP) || right)) ; now apply /eqP | ]) ; contradiction.
  }
  {
    unfold set_at.
    ssprove_valid.
  }
Defined.
Fail Next Obligation.


Definition R_ch_map_XTR_packages (d : nat) (M : chHandle -> nat)
  (H_inLM : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M) :
  package L_M (XTR_n_ℓ d) (XTR_n_ℓ d).
Proof.
  assert (H1 : forall n, ∀ x y : ExtraTypes_name__canonical__eqtype_Equality,
             x ≠ y
             → idents [interface #val #[XTR x n d] : chXTRinp → chXTRout ]
                 :#: idents [interface #val #[XTR y n d] : chXTRinp → chXTRout ]
         ).
  {
    intros.
    unfold idents.
    solve_imfset_disjoint.
  }

  assert (H2 : uniq XTR_names) by reflexivity.

  assert (H3 : forall ℓ, trimmed_pairs
    (List.map (fun n : name => [interface #val #[(@XTR n ℓ d)] : chXTRinp → chXTRout ]) XTR_names)
    (map_with_in XTR_names (fun (x : name) H0 => pack (R_ch_map_XTR_package d ℓ x (fun _ : name => M) H0 H_inLM)))) by now repeat split ; apply trimmed_package_cons ; apply trimmed_empty_package.

  set (XTR_n_ℓ) at 2.
  rewrite (interface_hierarchy_trivial (XTR_n_ℓ d) XTR_names d _).
  2: easy.
  subst i.
  refine (ℓ_packages
            d
            (fun ℓ H => {package parallel_raw (map_with_in XTR_names (fun x H0 => pack (R_ch_map_XTR_package d ℓ x (fun _ => M) H0 H_inLM)))
                        #with
                 (valid_forall_map_with_in
                    (λ (n : name) (ℓ : nat), (XTR_n_ℓ d) (* [interface #val #[XTR n ℓ] : chXTRinp → chXTRout ] *))
                    (λ n : name, [interface #val #[XTR n ℓ d] : chXTRinp → chXTRout ])
                    XTR_names
                    (λ ℓ (x : name) (H0 : List.In x XTR_names), R_ch_map_XTR_package d ℓ x (λ _ : name, M) H0 H_inLM)
                    d
                    ℓ
                    H (H1 _) H2 (H3 _) _ ) })
            (fun _ _ => trimmed_parallel_raw _ _ _ (H1 _) H2 (H3 _)) _ ).
  - unfold XTR_names, map_with_in, List.map.
    unfold valid_pairs.
    split ; [ | split ] ; apply R_ch_map_XTR_package.
  - intros.
    apply idents_foreach_disjoint_foreach.
    intros.
    unfold idents.
    solve_imfset_disjoint.
Defined.
Fail Next Obligation.

Notation " 'chXPDinp' " :=
  (chHandle × 'bool × bitvec)
    (in custom pack_type at level 2).
Notation " 'chXPDout' " :=
  (chHandle)
    (in custom pack_type at level 2).
(* Context {xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle}. *)

Definition R_ch_map_XPD_package d (ℓ : nat) (n : name) (M : name -> chHandle -> nat) (M_ℓ : name -> nat -> chHandle -> nat) :
  (List.In n XPR) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  (forall s1 s k, ('option ('fin #|fin_handle|); M_ℓ s1 s k) \in L_M) ->
  package L_M (XPD_n_ℓ d (* ℓ.+1 *))
    [interface
       #val #[ XPD n ℓ d (* ℓ.+1 *) ] : chXPDinp → chXPDout
    ].
  intros.
  refine [package
     #def #[ XPD n ℓ d (* ℓ.+1 *) ] ('(h1,r,args) : chXPDinp) : chXPDout {
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
        assertD (ℓ1 <= d)%nat (fun H =>
            h ← xpd_angle n label h1 args ;;

            #import {sig #[ XPD n ℓ1 d (* ℓ.+1 *) ] : chXPDinp → chXPDout }
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
    rewrite <- fset0E.
    apply Labels.
  - apply valid_scheme.
    apply level.
  - apply valid_scheme. rewrite <- fset0E. apply (prog_valid (xpd_angle _ _ _ _)).
  - unfold XPD_n_ℓ.
    set (o := mkopsig _ _ _) ; pattern x2 in o ; subst o.
    apply lower_level_in_interface.
    2: apply x3. (* Lia.lia. *)

    (* simpl. *)
    unfold XPD, serialize_name.
    unfold mkopsig.
    (* destruct n. *)
    (* all: try (unfold XPR in H ; repeat (destruct H ; [ discriminate | ] || contradiction)). *)

    unfold XPR, interface_foreach, List.fold_left, "++".
    unfold mkopsig.
    rewrite <- !fset1E.
    rewrite !in_fsetU.
    rewrite !in_fset1.
    unfold XPR, "++" in H.
    repeat (destruct H as [ | H ] ; [subst ; repeat (apply /orP ; ((left ; now apply /eqP) || right)) ; now apply /eqP | ]) ; contradiction.
Defined.
Fail Next Obligation.

Lemma trimmed_R_ch_map_XPD_package : forall d n ℓ M1 M2 A B C, trimmed [interface
       #val #[ XPD n ℓ d (* d.+1 *) ] : chXPDinp → chXPDout
    ] (R_ch_map_XPD_package d ℓ n M1 M2 A B C).
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
       #val #[ XPD n d d (* d.+1 *) ] : chXPDinp → chXPDout
    ]) XPR) (parallel_raw
       (map_with_in XPR
          (λ (x : name) (H0 : List.In x XPR),
             pack (R_ch_map_XPD_package d d x (λ _ : name, M) (λ (_ : name) (_ : nat), M) H0
                     (λ _ : name, H_L_M) (λ (_ : name) (_ : nat), H_L_M))))).
Proof.
  intros.

  apply trimmed_parallel_raw.
  {
    intros.
    unfold idents.
    solve_imfset_disjoint.
  }
  {
    reflexivity.
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

Definition R_ch_map_XPD_packages  (d : nat) (M : chHandle -> nat) :
  (forall s, ('option ('fin #|fin_handle|); M s) \in L_M) ->
  package L_M (XPD_n_ℓ d) (XPD_n_ℓ d).
Proof.
  intros H_L_M.
  (* refine (ℓ_packages *)
  (*           d (fun ℓ H => {package parallel_raw (map_with_in XPR (fun x H => pack (R_ch_map_XPD_package ℓ x (fun _ => M) (fun _ _ => M) H (fun _ => H_L_M) (fun _ _ => H_L_M)))) #with _ }) *)
  (*   _ _ _). *)

  (* 2: intros ; apply trimmed_parallel_raw_R_ch_map_XPD. *)
  (* 2: now apply interface_foreach_idents_XPD. *)

  assert (H1 : forall n, ∀ x y : ExtraTypes_name__canonical__eqtype_Equality,
             x ≠ y
             → idents [interface #val #[XPD x n d] : chXPDinp → chXPDout ]
                 :#: idents [interface #val #[XPD y n d] : chXPDinp → chXPDout ]
         ).
  {
    intros.
    unfold idents.
    solve_imfset_disjoint.
  }

  assert (H2 : uniq XPR) by reflexivity.

  eassert (H3 : forall ℓ, trimmed_pairs
    (@List.map (Equality.sort ExtraTypes_name__canonical__eqtype_Equality) Interface
       (fun n : name =>
        @fset
          (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
             (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                choice_type_choice_type__canonical__Ord_Ord))
          (@cons (prod nat (prod choice_type choice_type))
             (@pair nat (prod choice_type choice_type) (@XPD n ℓ d)
                (@pair choice_type choice_type (chProd (chProd chHandle chBool) bitvec) chHandle))
             (@nil (prod nat (prod choice_type choice_type))))) XPR)
    (@map_with_in (Equality.sort ExtraTypes_name__canonical__eqtype_Equality) raw_package XPR
       (fun (x : name) (H0 : @List.In name x XPR) =>
        @pack _ _ _
          (R_ch_map_XPD_package d ℓ x (fun _ : name => M) (fun (_ : name) (_ : nat) => M) H0
             (fun _ => H_L_M) (fun _ _ => H_L_M))))).
  {
    intros.
    unfold pack.
    unfold map_with_in, XPR.
    unfold parallel_raw.
    unfold List.fold_left.
    unfold List.map.
    unfold "++".
    unfold trimmed_pairs.
    repeat split ; apply trimmed_package_cons ; apply trimmed_empty_package.
  }

  set (XPD_n_ℓ) at 2.
  rewrite (interface_hierarchy_trivial (XPD_n_ℓ d) XPR d _).
  2: easy.
  subst i.
  refine (ℓ_packages
            d
            (fun ℓ H => {package parallel_raw (map_with_in XPR (fun x H0 => pack (R_ch_map_XPD_package d ℓ x (fun _ => M) (fun _ _ => M) H0 (fun _ => H_L_M) (fun _ _ => H_L_M))))
                        #with
                 (valid_forall_map_with_in
                    (λ (n : name) (ℓ : nat), (XPD_n_ℓ d) (* [interface #val #[XPD n ℓ] : chXPDinp → chXPDout ] *))
                    (λ n : name, [interface #val #[XPD n ℓ d] : chXPDinp → chXPDout ])
                    XPR
                    (λ ℓ (x : name) (H0 : List.In x XPR), R_ch_map_XPD_package d ℓ x (λ _ : name, M) (λ _ _ , M) H0 _ _)
                    d
                    ℓ
                    H (H1 _) H2 (H3 _) _ ) })
            (fun _ _ => trimmed_parallel_raw _ _ _ (H1 _) H2 (H3 _)) _ ).
  - unfold XPR, map_with_in, List.map, "++".
    unfold valid_pairs.
    repeat split. all: apply R_ch_map_XPD_package.
  - intros.
    apply idents_foreach_disjoint_foreach.
    intros.
    unfold idents.
    solve_imfset_disjoint.
Defined.
Fail Next Obligation.

Lemma idents_disjoint_foreach :
  (forall {A} f g (L : list A),
      (forall m, idents f :#: idents (g m)) ->
      idents f :#: idents (interface_foreach g L)).
Proof.
  intros.
  induction L.
  + simpl.
    rewrite <- fset0E.
    unfold idents.
    rewrite imfset0.
    apply fdisjoints0.
  + rewrite interface_foreach_cons.
    unfold idents.
    rewrite !imfsetU.
    rewrite fdisjointUr.
    rewrite IHL ; clear IHL.
    rewrite Bool.andb_true_r.
    apply H.
Qed.

Lemma idents_foreach_disjoint_foreach_different :
  (forall {A} f g (Lf Lg : list A),
      (forall n m, idents (f n) :#: idents (g m)) ->
      idents (interface_foreach f Lf) :#: idents (interface_foreach g Lg)).
Proof.
  intros.
  apply idents_disjoint_foreach ; intros.
  rewrite fdisjointC.
  apply idents_disjoint_foreach ; intros.
  rewrite fdisjointC.
  apply H.
Qed.


(* R_ch_map, fig.25, Fig. 27, >> Fig. 29 << *)
(* GET_o_star_ℓ d *)
Definition R_ch_map (d : nat) :
  package (L_M :|: (L_K :|: L_L))
    ([interface #val #[ SET PSK 0 d ] : chSETinp → chSETout] :|:
       DH_interface :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d)
    (KS_interface d)
    (* (SET_O_star_ℓ :|: GET_O_star_ℓ) *).
  refine (let base_package : package L_M
    ([interface #val #[ SET PSK 0 d ] : chSETinp → chSETout] :|:
       DH_interface :|:
    XTR_n_ℓ d :|:
    XPD_n_ℓ d) ([interface #val #[ SET PSK 0 d ] : chSETinp → chSETout] :|: DH_interface)
  :=
    [package
     #def #[ SET PSK 0 d ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ SET PSK 0 d ] : chSETinp → chSETout }
        as set_fn ;;
        nh ← set_fn (h, hon, k) ;;
        set_at (H := pos_handle) (M h) fin_handle (otf nh) ;;
        ret h
      } ;
   #def #[ DHGEN ] (t : chDHGENinp) : chDHGENout {
        #import {sig #[ DHGEN ] : chDHGENinp → chDHGENout }
        as dhgen ;;
        dhgen t
      } ;
     #def #[ DHEXP ] (t : chDHEXPinp) : chDHEXPout {
        #import {sig #[ DHEXP ] : chDHEXPinp → chDHEXPout }
        as dhexp ;;
        dhexp t
      }
    ]
  in _).

  Unshelve.
  2-3: try apply DepInstance ; shelve.

  1: refine ({package
     par (base_package
     ) (par (par
          (R_ch_map_XPD_packages d _ _)
          (R_ch_map_XTR_packages d M H))
            (Ks d O_star false erefl ∘ Ls d O_star F erefl)
       ) }).
  1:{
    ssprove_valid.
    {
      (* simpl. *)
      unfold FDisjoint.
      apply @parable.

      eassert (trimmed (XTR_n_ℓ d) (R_ch_map_XTR_packages d M H)).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.

      eassert (trimmed (XPD_n_ℓ d) (R_ch_map_XPD_packages d M (H BOT))).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.

      eassert (trimmed ([interface #val #[ SET PSK 0 d ] : chSETinp → chSETout] :|: DH_interface) base_package).
      {
        unfold DH_interface.
        rewrite <- fset_cat.
        simpl fset.

        unfold trimmed.
        unfold base_package.
        unfold pack.

        do 3 apply trimmed_package_cons ; apply trimmed_empty_package.
      }
      rewrite <- H. clear H.

      rewrite <- trimmed_Ks.
      rewrite !link_trim_commut.

      solve_Parable.

      {
        apply idents_interface_hierachy3 ; intros.
        apply idents_disjoint_foreach ; intros.
        unfold idents.
        unfold DH_interface.
        rewrite (fset_cons (DHGEN , _)).
        solve_imfset_disjoint.
      }
      {
        apply idents_interface_hierachy3 ; intros.
        apply idents_disjoint_foreach ; intros.
        unfold idents.
        unfold DH_interface.
        rewrite (fset_cons (DHGEN , _)).
        solve_imfset_disjoint.
      }
      {
        unfold DH_interface.
        rewrite (fset_cons (DHGEN, _)).
        rewrite function2_fset_cat.
        apply idents_interface_hierachy3.
        intros.
        unfold idents.
        (* apply idents_interface_foreach_disjoint. *)
        rewrite imfsetU.
        rewrite fdisjointUl.
        apply /andP ; split ; [ solve_imfset_disjoint | ].
        apply idents_disjoint_foreach ; intros.
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    {
      (* simpl. *)
      unfold FDisjoint.
      apply @parable.

      eassert (trimmed (XTR_n_ℓ d) (R_ch_map_XTR_packages d M H)).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.

      eassert (trimmed (XPD_n_ℓ d) (R_ch_map_XPD_packages d M (H BOT))).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.

      rewrite <- trimmed_Ks.
      rewrite !link_trim_commut.
      
      solve_Parable.

      {
        unfold idents.
        unfold XPD_n_ℓ.
        apply idents_interface_hierachy3.
        intros.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        rewrite function_fset_cat.
        unfold idents.

        apply idents_foreach_disjoint_foreach_different ; intros.
        unfold idents.
        solve_imfset_disjoint.
      }
      {
        unfold idents.
        unfold XTR_n_ℓ, XPD_n_ℓ.
        apply idents_interface_hierachy3.
        intros.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.

        rewrite function_fset_cat.

        apply idents_foreach_disjoint_foreach_different ; intros.
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    {
      (* simpl. *)
      unfold FDisjoint.
      apply @parable.

      eassert (trimmed (XTR_n_ℓ d) (R_ch_map_XTR_packages d M H)).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.

      eassert (trimmed (XPD_n_ℓ d) (R_ch_map_XPD_packages d M (H BOT))).
      {
        rewrite trimmed_eq_rect_r.
        apply trimmed_ℓ_packages.
      }
      rewrite <- H. clear H.
      
      solve_Parable.

      {
        unfold idents.
        unfold XTR_n_ℓ, XPD_n_ℓ.
        apply idents_interface_hierachy3.
        intros.
        rewrite fdisjointC.
        apply idents_interface_hierachy3.
        intros.
        (* apply idents_foreach_disjoint_foreach_different ; intros. *)
        unfold idents.
        solve_imfset_disjoint.
      }
    }
    {
      apply fsubsetxx.
    }
    {
      apply fsubsetxx.
    }
    {
      apply fsubsetxx.
    }
    {
      apply fsubsetUr.
      (* apply fsubsetxx. *)
    }
    {
      apply fsubsetUl.
      (* apply fsubsetxx. *)
    }
    {
      rewrite fsetUid.
      apply fsubsetxx.
    }
    {
      rewrite <- fset0E ; rewrite fsetU0.
      apply fsubsetxx.
      (* solve_in_fset. *)
    }
    {
      apply fsubsetxx.
      (* unfold KS_interface. *)
      (* solve_in_fset. *)
    }
    {
      rewrite fsetUA.
      rewrite fsetUid.
      rewrite (fsetUC L_L).
      apply fsubsetxx.
    }
    {
      solve_in_fset.
    }
    {
      unfold KS_interface.
      unfold DH_interface.
      rewrite fset_cons.
      rewrite fset1E.
      rewrite <- fset0E ; rewrite fsetU0.

      fold (GET_O_star_ℓ d).
      fold (SET_O_star_ℓ d).
      solve_in_fset.
    }
  }
  {
    unfold DH_interface.
    unfold set_at.

    rewrite <- fset_cat.
    ssprove_valid ; ssprove_valid'_2.
    1:{
      rewrite !in_fsetU.
      apply /orP ; left.
      apply /orP ; left.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; right.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; right.
      unfold mkopsig.
      rewrite <- fset1E.
      rewrite in_fset1.
      apply eqxx.
    }
    {
      rewrite !in_fsetU.
      apply /orP ; left.
      apply /orP ; left.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; right.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; left.
      unfold mkopsig.
      rewrite in_fset1.
      apply eqxx.
    }
    {
      rewrite !in_fsetU.
      apply /orP ; left.
      apply /orP ; left.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; left.
      unfold mkopsig.
      rewrite in_fset1.
      apply eqxx.
    }
    {
      apply Dependencies.H.
      apply BOT.
    }
  }
Time Defined. (* 114.674 secs (104.24u,1.633s) -> 8.862 secs (8.839u,0.01s) *)
Fail Next Obligation.

Obligation Tactic := (* try timeout 8 *) idtac.
Program Definition Gks_real_map (d : nat) :
  package
    (L_M :|: (L_K :|: L_L))
    [interface]
    (* ([interface #val #[ SET PSK 0 d ] : chSETinp → chSETout]) *)
    (GET_O_star_ℓ d) :=
  {package
     (* (Ks d O_star false erefl ∘ Ls d O_star F erefl) ∘ *)
     R_ch_map d
     ∘ (par (XPD_DH_XTR d) (K_package d PSK O erefl false ∘ L_package d PSK F)) }.
Next Obligation.
  intros.
  rewrite <- fsetUid.
  eapply valid_link.
  2:{
    (* eapply valid_link. *)
    (* 2:{ *)
      (* rewrite <- fsetUid. *)
      eapply valid_par_upto.
      2: apply (pack_valid (XPD_DH_XTR d)).
      2:{
        eapply valid_link.
        - apply K_package.
        - apply L_package.
      }

      3: rewrite <- fset0E ; rewrite fsetU0.
      2,3: solve_in_fset.
      2: apply fsubsetxx.

      unfold XPD_DH_XTR.
      unfold pack.

      (* assert (trimmed _ (XPD_packages d)). *)
      unfold XPD_packages ; rewrite <- trimmed_ℓ_packages ; fold (XPD_packages d).
      rewrite !link_trim_commut.

      rewrite <- trimmed_dh.
      rewrite !link_trim_commut.

      unfold XTR_packages ; rewrite <- trimmed_ℓ_packages ; fold (XTR_packages d).
      rewrite !link_trim_commut.

      (* rewrite <- (trimmed_Ks d O_star). *)
      (* rewrite !link_trim_commut. *)

      repeat set (trim _ _).
      eassert (trimmed _ (par f (par f0 f1))) ; [ | rewrite <- H ; clear H ].
      {
        subst f f0 f1.
        repeat eapply trimmed_par ; try apply trimmed_trim ; apply @parable.
        {
          solve_Parable.
          {
            rewrite fdisjointC.
            apply idents_interface_hierachy3.
            intros.
            unfold DH_interface.
            rewrite fset_cons.
            apply idents_disjoint_foreach ; intros.
            unfold idents.
            solve_imfset_disjoint.
          }
          {
            apply idents_interface_hierachy3.
            intros.
            rewrite fdisjointC.
            apply idents_interface_hierachy3.
            intros.
            (* apply idents_foreach_disjoint_foreach_different ; intros. *)
            unfold idents.
            solve_imfset_disjoint.
          }
        }
        {
          solve_Parable.
          {
            apply idents_interface_hierachy3.
            intros.
            unfold DH_interface.
            rewrite fset_cons.
            apply idents_disjoint_foreach ; intros.
            unfold idents.
            solve_imfset_disjoint.
          }
        }
      }

      rewrite !link_trim_commut.

      eassert (trimmed _ (K_package d PSK O erefl false)) by repeat (apply trimmed_empty_package || apply trimmed_package_cons) ; rewrite <- H ; clear H .

      rewrite !link_trim_commut.

      solve_Parable.
      {
        unfold idents.
        solve_imfset_disjoint.
        {
          rewrite fdisjointC.
          apply idents_interface_hierachy3.
          intros.
          apply idents_disjoint_foreach ; intros.
          rewrite fset_cons.
          unfold idents.
          solve_imfset_disjoint.
        }
        {
          rewrite fset_cons.
          unfold DH_interface.
          rewrite (fset_cons (DHGEN, _)).
          unfold idents.
          solve_imfset_disjoint.
        }
        {
          rewrite fdisjointC.
          apply idents_interface_hierachy3.
          intros.
          rewrite fset_cons.
          apply idents_disjoint_foreach ; intros.
          unfold idents.
          solve_imfset_disjoint.
        }
      }
    }

    eapply valid_package_inject_export.
    2:{
      eapply valid_package_inject_import.
      2:{
        apply (pack_valid (R_ch_map d)).
      }
      {
        solve_in_fset.
      }
    }
    {
      unfold KS_interface.
      solve_in_fset.
    }
Defined.
Fail Next Obligation.

Program Definition Gks_ideal_map (d : nat) (Score : Simulator d) :
  package
    fset0
    (KS_interface d)
    (GET_O_star_ℓ d) := {package Score ∘ (R_ch_map d) }.
Next Obligation.
  admit.
Admitted.
Fail Next Obligation.

(* Program Definition my_package : *)
(*   package fset0 [interface] fset0 *)
(*   := *)
(*   {package (Gks_real (* d *) ∘ ((par XPD_packages (par DH_package (par hash XTR_packages))) ∘ (Ks O_star false erefl ∘ Ls O_star F erefl))) #with _}. *)

Lemma map_eta : forall {A B} (f : A -> B) a l, List.map f (a :: l) = f a :: List.map f l.
Proof. reflexivity. Qed.

Lemma map_with_in_num_trivial : forall k n, map_with_in_num n (fun a b => k) = k.
Proof.
  clear ; intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.

    unfold par.
    rewrite unionmI.
    reflexivity.
Qed.

Lemma map_with_in_num_parable :
  forall f g z Ef Eg,
  forall (Hf : forall z, trimmed Ef (f z)),
  forall (Hg : forall z, trimmed Eg (g z)),
    idents Ef :#: idents Eg ->
    map_with_in_num z (fun n H => par (f n) (g n))
    = par (map_with_in_num z (fun n H => f n)) (map_with_in_num z (fun n H => g n)).
Proof.
  clear ; intros.
  induction z.
  - reflexivity.
  - unfold map_with_in_num ; fold map_with_in_num.
    rewrite IHz.
    + set (map_with_in_num _ _).
      set (map_with_in_num _ _).
      set (f _).
      set (g _).

      rewrite par_assoc.
      rewrite par_assoc.
      f_equal.

      rewrite <- par_assoc.
      rewrite <- par_assoc.
      f_equal.

      rewrite <- (par_commut) ; [ reflexivity | ].
      subst r0 r1.

      assert (forall n, Parable (f n) (map_with_in_num z (fun n H => g n))).
      {
        clear -Hf Hg H.
        induction z ; intros.
        - simpl.
          rewrite <- Hf.
          rewrite <- Hg.
          solve_Parable.
          apply H.
        - unfold map_with_in_num ; fold map_with_in_num.
          apply parable_par_r.
          + apply IHz.
          + rewrite <- Hf.
            rewrite <- Hg.
            solve_Parable.
            apply H.
      }
      apply H0.
Qed.

Lemma get_map_with_in_num_notin :
  forall  (p : forall d n, (d >= n)%nat → raw_package),
  forall (d : nat) k (Hk_le : (k <= d)%nat) x index n m,
    (n > k)%nat ->
    (forall k Hk_le, (k < n)%nat -> getm (p d k Hk_le) (serialize_name x n m index) = None) ->
    map_with_in_num_upper d k
      (H_le := Hk_le)
      (λ (n : nat) (x1 : (n <= d)%N), p d n x1)
      (serialize_name x n m index)
    = None.
Proof.
  clear.
  intros.
  induction k.
  - simpl.
    intros.
    now rewrite H0.
  - intros.
    simpl.
    rewrite unionmE.

    replace (isSome (getm (map_with_in_num_upper _ _ _) _)) with false ; [ | symmetry ].
    1: now rewrite H0.

    now rewrite IHk.
Qed.

Lemma map_with_in_num_upper_getm :
  forall (d : nat) (k : nat) (Hk_le : (k <= d)%nat)
    (p : forall d n, (d >= n)%nat → raw_package)
    x x0 index m,
  forall (H_le : (x0 <= k)%nat),
    (x0 <= m)%nat ->
    (forall n k Hk_le, (k <> n)%nat -> (n <= m)%nat -> getm (p d k Hk_le) (serialize_name x n m index) = None) ->
      getm (map_with_in_num_upper d k (H_le := Hk_le) (λ (n : nat) (x1 : (n <= d)%N), p d n x1)) (serialize_name x x0 m index)
      = getm (p d x0 (leq_trans H_le Hk_le)) (serialize_name x x0 m index).
Proof.
  intros.
  induction k.
  {
    unfold map_with_in_num.
    simpl.
    destruct x0.
    - now replace (leq_trans _ _) with (Hk_le).
    - discriminate.
  }
  {
    destruct (x0 == k.+1) eqn:kn ; move: kn => /eqP kn ; subst.
    {
      unfold map_with_in_num_upper ; fold map_with_in_num_upper.
      rewrite unionmE.

      replace (isSome _) with false ; [ | symmetry ].
      1: now replace (leq_trans _ _) with (Hk_le).

      rewrite get_map_with_in_num_notin ; [ reflexivity | .. ].
      1: apply H_le.
      intros.
      now rewrite H0.
    }
    {
      unfold map_with_in_num_upper ; fold map_with_in_num_upper.
      rewrite unionmE.

      rewrite !IHk.
      - Lia.lia.
      - intros.
        destruct (p d x0 _ _) eqn:pd_is.
        + unfold isSome.
          set (leq_trans _ _) in pd_is.
          replace (leq_trans _ _) with i by easy.
          now rewrite pd_is.
        + unfold isSome.
          set (leq_trans _ _) in pd_is.
          replace (leq_trans _ _) with i by easy.
          rewrite pd_is.
          now rewrite H0.
    }
  }
Qed.

Lemma ℓ_package_getm :
  forall {L I} (d : nat)
    {f : nat -> nat -> Interface}
    (p : forall d (n : nat), (d >= n)%nat → package L (I d) (f d n))
    (H_trim_p : forall n, forall (H_ge : (d >= n)%nat), trimmed (f d n) (p d n H_ge))
    (Hdisj : ∀ (n ℓ : nat) , (n > ℓ)%nat -> (d >= n)%nat -> idents (f d ℓ) :#: idents (f d n)),
  forall x x0 index,
    (forall (H_le : (x0 <= d)%nat),
        (∀ (n k : nat) (Hk_le : (k <= d)%N),
    k ≠ n → (n <= d)%N → getm (pack (p d k Hk_le)) (serialize_name x n d index) = None) ->
    getm (pack (ℓ_packages d (p d) H_trim_p Hdisj)) (serialize_name x x0 d index) =
    getm (pack (p d x0 H_le)) (serialize_name x x0 d index)
  ).
Proof.
  intros.
  unfold ℓ_packages.
  unfold pack.
  rewrite (map_with_in_num_upper_getm d d (leqnn d) p x x0 index d).
  - now replace (leq_trans _ _) with (H_le).
  - assumption.
  - apply H.
Qed.

(* parallel_raw (List.map (λ y : name, K_package d y x0 H1 false) O_star) (serialize_name x x0 d 1) *)

Lemma getm_parallel_raw :
  forall x y m (f : name -> raw_package) l index,
    uniq l ->
    x \in l ->
    (forall a x, a <> x -> getm (f a) (serialize_name x y m index) = None) ->
    getm (parallel_raw (List.map f l)) (serialize_name x y m index)
    = getm (f x) (serialize_name x y m index).
Proof.
  intros.
  generalize dependent x.
  induction l ; intros.
  - easy.
  - rewrite map_eta.
    rewrite parallel_raw_cons.
    rewrite unionmE.

    rewrite in_cons in H0.
    move: H0 => /orP [ /eqP H0 | H0 ] ; subst.
    + destruct (getm (f a)).
      * simpl.
        reflexivity.
      * simpl.
        clear IHl.

        generalize dependent a.
        induction l ; intros.
        -- simpl.
           rewrite emptymE.
           reflexivity.
        -- rewrite map_eta.
           rewrite parallel_raw_cons.
           rewrite unionmE.

           rewrite !cons_uniq in H.
           move: H => /andP [ H /andP [ H2 H3 ] ].
           rewrite !notin_cons in H.
           move: H => /andP [ H H4 ].
           rewrite IHl.
           2:{
             rewrite cons_uniq.
             now apply /andP.
           }
           rewrite H1.
           2: now move: H => /eqP.
           reflexivity.
    + rewrite !cons_uniq in H.
      move: H => /andP H.
      rewrite IHl ; [ | easy.. ].
      rewrite H1.
      * simpl.
        reflexivity.
      * destruct H as [ ? _ ].
        clear -H H0.
        generalize dependent a.
        induction l ; intros.
        -- easy.
        -- rewrite in_cons in H0.
           rewrite notin_cons in H.
           move: H => /andP [/eqP H H1].
           move: H0 => /orP [/eqP H0 | H0 ] ; subst.
           ++ easy.
           ++ now apply IHl.
Qed.

(* (parallel_raw (List.map (fun y => (pack (K_package d y n x1 false))) O_star)) *)

Definition parallel_package
  (A : eqType) (d : nat) L (f : A -> _) g Names (i : forall (a : A), package L (f a) (g a))
    (H : ∀ x y : A, x ≠ y → idents (g x) :#: idents (g y))
    (H1 : ∀ a : A, trimmed (g a) (i a))
    (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_foreach g Names) :=
  {package
     parallel_raw _ #with
    valid_parable _ _ _ _ _ _
    (H)
    H3
    (trimmed_pairs_cons _ _ _ (H1))
    (valid_pairs_cons _ _ _ _ _ (fun m => pack_valid (i m))) }.

Lemma trimmed_pairs_cons :
  forall {A : eqType} (l : list A) (f : forall (a : A), (a \in l) -> Interface) g,
    (forall a, (a \in l) -> trimmed (f a _) (g a _)) ->
    trimmed_pairs
      (map_with_in l f)
      (map_with_in l g).
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold List.map ; fold (List.map f l); fold (List.map g l).
    simpl.
    destruct l.
    + apply H.
    + simpl.
      split ; [ apply H | apply IHl ].
Qed.

Definition parallel_in_package
  (A : eqType) (d : nat) L (f : A -> _) g Names (i : forall (a : A) (_ : a \in Names), package L (f a) (g a))
    (H : ∀ x y : A, x ≠ y → idents (g x) :#: idents (g y))
    (H1 : ∀ (a : A) (_ : a \in Names), trimmed (g a) (i a _))
    (H3 : uniq Names) :
  package L
    (interface_foreach f Names)
    (interface_foreach g Names) :=
  {package
     parallel_raw _ #with
    valid_parable _ _ _ _ _ _
    (H)
    H3
    (trimmed_pairs_cons _ _ _ (fun a => H1 _ _))
    (valid_pairs_cons _ _ _ _ _ (fun m => pack_valid (i _ m))) }.

Lemma ℓ_list :
  forall {L I} (d : nat) (l : seq name) (l_uniq : uniq l)
    {f : nat -> name -> nat -> Interface}
    (p : forall d (a : name) (n : nat), (d >= n)%nat → package L (I d a) (f d a n))
    (H_trim_p : forall d a n, forall (H_ge : (d >= n)%nat), trimmed (f d a n) (p d a n H_ge))
    (Hdisj : ∀ d a y n (ℓ : nat), ((a <> y /\ n = ℓ) \/ (n > ℓ)%nat) -> (d >= n)%nat -> idents (f d a ℓ) :#: idents (f d y n)),
  forall x x0 index (_ : x \in l),
    (forall (H_le : (x0 <= d)%nat),
        (∀ d (a x1 : name) x0 H_le n,
            (x0 <= d)%N /\ (n <= d)%N ->
            ((a ≠ x1) \/ (a = x1 /\ x0 <> n)) →
            getm (pack (p d a x0 H_le)) (serialize_name x1 n d index) = None) ->
        getm
          (pack (ℓ_packages d
                   (fun n x1 => parallel_package _ d L _ _ _ (fun a => p d a n x1) (fun a y H => Hdisj d a y n n (or_introl (conj H erefl)) x1) (fun a => H_trim_p d a n x1) l_uniq)
                   (fun n x1 =>
                      trimmed_parallel_raw
                        _
                        l
                        _
                        (fun x y H => Hdisj d x y n n (or_introl (conj H erefl)) x1)
                        l_uniq
                        (trimmed_pairs_cons _ _ _ (fun x => H_trim_p _ _ _ _)))
                   (fun n ℓ H1 H2 => idents_foreach_disjoint_foreach _ _ l (fun a b => Hdisj _ _ _ _ _ (or_intror H1) H2 )) (* (Hdisj x) *)))
          (serialize_name x x0 d index) =
    getm (pack (p d x x0 H_le)) (serialize_name x x0 d index)
  ).
Proof.
  intros.

  set (tp := fun _ _ => _).
  pattern d in tp.
  set (ℓp := fun _ _ => _) in tp.
  subst tp.

  set (t_trim := fun _ _ => _).
  pattern d in t_trim.
  set (ℓ_trim := fun _ _ => _) in t_trim.
  subst t_trim.

  set (t_disj := fun _ _ _ _ => _).
  pattern d in t_disj.
  set (ℓ_disj := fun _ _ _ _ => _) in t_disj.
  subst t_disj.

  rewrite ℓ_package_getm.
  - subst ℓp.
    apply getm_parallel_raw.
    + assumption.
    + assumption.
    + now intros ; apply H0 ; [ | left].
  - intros.
    subst ℓp.
    hnf.
    rewrite getm_parallel_raw.
    + specialize (H0 d x x k Hk_le).
      now apply H0 ; [ | right].
    + assumption.
    + assumption.
    + now intros ; apply H0 ; [ | left ].
 Qed.

Lemma map_intro_c2 :
  (* forall (d : nat), *)
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
    ValidPackage LA (GET_O_star_ℓ d) A_export A →
    LA :#: L_M :|: (L_K :|: L_L) ->
    (AdvantageE
       (Gks_real d)
       (Gks_real_map d) A = 0
    )%R.
Proof.
  intros.

  apply: eq_rel_perf_ind_ignore.
  1: apply fsubsetxx.
  2: now  rewrite fdisjointUr in H0 ; apply (ssrbool.elimT andP) in H0 as [].
  2: apply H0.
  1:{
    unfold eq_up_to_inv.

    let id := fresh "id" in
    let So := fresh "S" in
    let To := fresh "T" in
    let hin := fresh "hin" in
    intros id So To m hin.

    assert (
        exists n ℓ,
          ((ℓ <= d)%nat /\ (n \in O_star))
          /\ ((id, (S, T)) = (GET n ℓ d, (chHandle, (chProd chKey chBool))))
      ).
    {
      clear -hin.

      simpl in hin.
      unfold SET_O_star_ℓ in hin.
      unfold GET_O_star_ℓ in hin.

      unfold interface_hierarchy_foreach in hin.

      set (d) in hin at 1 |- *.
      assert (H_le : d <= n) by reflexivity.
      generalize dependent n.

      induction O_star ; intros.
      - simpl in hin.
        induction d.
        + rewrite in_fset in hin.
          easy.
        + apply IHn0.
          2: Lia.lia.
          simpl in hin.
          rewrite <- fset0E in hin |- *.
          rewrite fsetU0 in hin.
          apply hin.
      - assert (((id, (S, T)) \in interface_hierarchy
                                    (λ ℓ : nat, [interface #val #[GET a ℓ n] : chXPDout → chGETout ]) d)
                \/ ((id, (S, T)) \in interface_hierarchy
                                      (λ ℓ : nat,
                                          interface_foreach
                                            (λ n0 : name, [interface #val #[GET n0 ℓ n] : chXPDout → chGETout ])
                                            l) d)).
        {
          replace ((λ ℓ : nat,
                   interface_foreach
                     (λ n0 : name, [interface #val #[GET n0 ℓ n] : chXPDout → chGETout ])
                     (a :: l))) with
                (λ ℓ : nat,
                   [interface #val #[GET a ℓ n] : chXPDout → chGETout ] :|: interface_foreach
                     (λ n0 : name, [interface #val #[GET n0 ℓ n] : chXPDout → chGETout ])
                     l) in hin by now setoid_rewrite interface_foreach_cons.

          clear -hin.
          - rewrite <- interface_hierarchy_U in hin.
            rewrite in_fset in hin.
            rewrite mem_cat in hin.
            apply (ssrbool.elimT orP) in hin.
            destruct hin as [hin | hin].
            + easy.
            + easy.
        }
        clear hin.
        destruct H.
        + clear IHl.
          (* destruct H. *)
          * induction d.
            -- simpl in H.
               rewrite <- fset1E in H.
               rewrite in_fset1 in H.
               apply (ssrbool.elimT eqP) in H.
               inversion H ; subst ; clear.
               do 2 eexists ; split ; [ | (* left ; *) reflexivity ] ; split ; [ Lia.lia | apply mem_head ].
            -- simpl in H.
               rewrite in_fset in H.
               rewrite mem_cat in H.
               apply (ssrbool.elimT orP) in H.
               destruct H.
               {
                 apply IHn0.
                 1: Lia.lia.
                 apply H.
               }
               {
                 rewrite <- fset1E in H.
                 rewrite in_fset1 in H.
                 apply (ssrbool.elimT eqP) in H.
                 rewrite H.
                 do 2 eexists ; split ; [ | reflexivity ] ; split ; [ Lia.lia | apply mem_head ].
               }
        + specialize (IHl n H H_le).
          destruct IHl as [? [? [[] ?]]].
          do 2 eexists ; split ; [ split ; [ apply H0 | ] | easy ].
          now rewrite in_cons ; apply /orP ; right.
    }

    clear hin.
    destruct H1 as [? [? [[] ?]]].
    - rewrite ?get_op_default_link.
      (* First we need to squeeze the codes out of the packages *)
      unfold get_op_default.

      {
        - inversion H3 ; subst ; clear H3.
          erewrite (lookup_op_spec_inv (Ks d O_star false erefl) (GET x x0 d)).
          2:{
            unfold Ks.
            unfold eq_rect_r.
            unfold eq_rect.
            destruct Logic.eq_sym.
            destruct function2_fset_cat.

            unfold combined.

            epose (ℓ_list d O_star erefl
                     (fun d a n H_le => K_package d a n H_le false) _ _ x x0 1%nat _ _ _).
            Unshelve.
            1: erewrite e.
            1:{
              unfold K_package.
              rewrite setmE.
              unfold ".1", ".2".
              unfold SET.

              replace (_ == _) with false.
              2: symmetry ; apply /eqP ; solve_imfset_disjoint.

              rewrite setmE.

              unfold GET.

              rewrite eqxx.
              reflexivity.
            }
            {
              intros ; hnf.
              do 2 apply trimmed_package_cons.
              apply trimmed_empty_package.
            }
            {
              intros.
              hnf.
              rewrite fset_cons.
              rewrite fdisjointC.
              rewrite fset_cons.
              unfold idents.
              destruct H3 ; solve_imfset_disjoint.
            }
            {
              assumption.
            }
            {
              assumption.
            }
            {
              intros.
              hnf.
              unfold K_package.
              rewrite setmE.
              unfold ".1", ".2".
              unfold SET.

              replace (_ == _) with false.
              2: symmetry ; apply /eqP ; solve_imfset_disjoint.

              rewrite setmE.

              unfold GET.

              replace (_ == _) with false.
              2: symmetry ; apply /eqP ; destruct H4 ; solve_imfset_disjoint.

              now rewrite emptymE.
            }
          }

          erewrite (lookup_op_spec_inv (R_ch_map d) (GET x x0 d)).
          2:{
            unfold pack.
            unfold R_ch_map.

            rewrite !setmE.
            unfold ".1", ".2".
            unfold SET, GET.
            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            rewrite unionmE.

            replace (isSome _) with false ; [ | symmetry ].
            2:{
              rewrite unionmE.
              replace (isSome (getm _ _)) with false ; [ | symmetry ].
              2:{
                unfold R_ch_map_XPD_packages.

                unfold eq_rect_r.
                unfold eq_rect.
                destruct Logic.eq_sym.

                epose (ℓ_list d XPR erefl
                         (fun d a n H_le => R_ch_map_XPD_package d n _ (λ _ : name, M) (λ (_ : name) (_ : nat), M) _ _ _) _ _ x x0 1%nat _ _ _).
                erewrite e.

                erewrite (ℓ_package_getm d d (fun d n x1 => {package (parallel_raw (map_with_in XPR (fun y _ => pack (R_ch_map_XPD_package d n _ (λ _ : name, M) (λ (_ : name) (_ : nat), M) _ _ _))))}) _ _ _ x x0 1%nat H1).

                unfold ℓ_packages.
                unfold pack.
                unfold ℓ_raw_packages.

                (* Set Printing Implicit. *)
                erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (map_with_in XPR (fun y _ => pack (R_ch_map_XPD_package d n _ (λ _ : name, M) (λ (_ : name) (_ : nat), M) _ _ _)))) x x0 1 d _ H1).
                {
                  unfold XPR.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.

                  assert (forall a b c d e f g x0,
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XPD_package d x0 a b c e f g)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XPD_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XPD.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
                Unshelve.
                2:{ admit. }
                2:{ apply H1. }

                {
                  admit.
                  (*   intros. *)
                  (*   unfold XPR. *)

                  (*   Optimize Heap. *)
                  (*   (* Optimize Proof. *) *)
                  
                  (*   unfold "++". *)
                  (*   unfold map_with_in. *)
                  (*   rewrite parallel_raw_cons. *)
                  (*   (* rewrite !parallel_raw_cons. *) *)
                  (*   Time Optimize Heap. *)
                  (*   rewrite unionmE. *)

                  (*   unfold R_ch_map_XPD_package. *)
                  (*   rewrite setmE. *)
                  (*   unfold ".1", ".2". *)
                  (*   unfold SET, GET. *)
                  (*   unfold XPD. *)

                  (*   replace (_ == _) with false ; [ | symmetry ]. *)
                  (*   2: apply /eqP ; solve_imfset_disjoint. *)
                  (*   now rewrite emptymE. *)
                  (* } *)

                  (* repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE). *)
                  (* now rewrite emptymE. *)
                  (*   replace (isSome (getm _ _)) with false ; [ | symmetry ]. *)
                  (*   2: now rewrite H3. *)
                  (*   2:{ *)
                  (*     unfold R_ch_map_XPD_package. *)
                  (*     rewrite setmE. *)
                  (*     unfold ".1", ".2". *)
                  (*     unfold SET, GET. *)
                  (*     unfold XPD. *)

                  (*     replace (_ == _) with false ; [ | symmetry ]. *)
                  (*     2: apply /eqP ; solve_imfset_disjoint. *)

                  (*     now rewrite emptymE. *)
                  (*   } *)
                }
              }
              {
                unfold R_ch_map_XTR_packages.

                unfold eq_rect_r.
                unfold eq_rect.
                destruct Logic.eq_sym.

                unfold ℓ_packages.
                unfold pack.
                unfold ℓ_raw_packages.

                (* Set Printing Implicit. *)
                erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (map_with_in XTR_names (fun y _ => pack (R_ch_map_XTR_package d n _ (λ _ : name, M) _ _)))) x x0 1 d _ H1).
                {
                  unfold XTR_names.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.

                  assert (forall a b c d e x0,
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XTR_package d x0 a b c e)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XTR_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XTR_names.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
                Unshelve.
                2: apply H1.
                {
                  intros.

                  unfold XTR_names.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.
                  
                  assert (forall a b c d e k x0,
                             (k <= d)%nat ->
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XTR_package d k a b c e)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XTR_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XTR_names.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  rewrite unionmE.
                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H5] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
              }
            }

            rewrite mapmE.
            {
              unfold Ks.
              unfold eq_rect_r.
              unfold eq_rect.
              destruct Logic.eq_sym.
              destruct function2_fset_cat.

              unfold combined.

              unfold ℓ_packages.
              unfold pack.
              unfold ℓ_raw_packages.

              eassert (forall H_le,
                          parallel_raw
                            (List.map (λ y : name, pack (K_package d y x0 H_le false)) O_star)
                            (serialize_name x x0 d 1)
                          = some (_)).
              {
                clear -H2 ; intros.
                induction O_star.
                - easy.
                - move: H2 => /orP [ /eqP H2 | H2 ] ; subst.
                  + rewrite map_eta.
                    rewrite parallel_raw_cons.
                    rewrite unionmE.

                    unfold K_package.

                    set ([fmap _ ; _ ]).
                    set (Option_Some _).
                    assert (getm f (serialize_name a x0 d 1) = o) ; subst f o.
                    {
                      unfold K_package.
                      rewrite !setmE.
                      unfold ".1", ".2".
                      unfold SET.

                      replace (_ == _) with false.
                      2: symmetry ; apply /eqP ; solve_imfset_disjoint.

                      rewrite eqxx.
                      reflexivity.
                    }
                    rewrite H2.
                    unfold isSome.
                    reflexivity.
                  + rewrite map_eta.
                    rewrite parallel_raw_cons.
                    rewrite unionmE.

                    unfold K_package.
                    rewrite !setmE.
                    unfold ".1", ".2".
                    unfold SET.

                    replace (_ == _) with false.
                    2: symmetry ; apply /eqP ; solve_imfset_disjoint.
                    
                    destruct (x == a) eqn:s_eq ; move: s_eq => /eqP s_eq ; subst.
                    * rewrite eqxx.
                      reflexivity.
                    * replace (_ == _) with false ; [ | symmetry ; apply /eqP ].
                      2: now apply serialize_name_notin_different_name.
                      rewrite emptymE.
                      unfold isSome.

                      apply IHl.
                      apply H2.
              }
              
              erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (List.map (fun y => pack (K_package d y n x1 false)) O_star)) x x0 1 d _ H1).
              {
                now rewrite H3.
              }
              {
                clear ; intros.
                induction O_star.
                - easy.
                - rewrite map_eta.
                  rewrite parallel_raw_cons.
                  rewrite unionmE.

                  rewrite !setmE.
                  unfold ".1", ".2".
                  unfold SET, GET.

                  destruct (n == k) eqn:n_is_neq_k ; move: n_is_neq_k => /eqP n_is_neq_k ; subst.
                  * Lia.lia.
                  * replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.

                    now rewrite emptymE.
              }
            }
          }


            erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (List.map (fun y => pack (K_package d y n x1 false)) O_star)) x x0 1 d _ H1).
            {
             now rewrite H3.
            }
            {
              clear ; intros.
              induction O_star.
              - easy.
              - rewrite map_eta.
                rewrite parallel_raw_cons.
                rewrite unionmE.

                rewrite !setmE.
                unfold ".1", ".2".
                unfold SET, GET.

                destruct (n == k) eqn:n_is_neq_k ; move: n_is_neq_k => /eqP n_is_neq_k ; subst.
                * Lia.lia.
                * replace (_ == _) with false ; [ | symmetry ].
                  2: apply /eqP ; solve_imfset_disjoint.

                  replace (_ == _) with false ; [ | symmetry ].
                  2: apply /eqP ; solve_imfset_disjoint.

                  now rewrite emptymE.
            }
          }
          Unshelve.
          2:{ apply H1. }

          unfold get_or_fn.
          unfold bind ; fold @bind.
          unfold code_link ; fold @code_link.

          erewrite (lookup_op_spec_inv (R_ch_map d) (GET x x0 d)).
          2:{
            rewrite !setmE.
            unfold ".1", ".2".
            unfold SET, GET.
            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            replace (_ == _) with false ; [ | symmetry ].
            2: apply /eqP ; solve_imfset_disjoint.

            rewrite unionmE.

            replace (isSome _) with false ; [ | symmetry ].
            2:{
              rewrite unionmE.
              replace (isSome (getm _ _)) with false ; [ | symmetry ].
              2:{
                unfold R_ch_map_XPD_packages.

                unfold eq_rect_r.
                unfold eq_rect.
                destruct Logic.eq_sym.

                unfold ℓ_packages.
                unfold pack.
                unfold ℓ_raw_packages.

                (* Set Printing Implicit. *)
                erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (map_with_in XPR (fun y _ => pack (R_ch_map_XPD_package d n _ (λ _ : name, M) (λ (_ : name) (_ : nat), M) _ _ _)))) x x0 1 d _ H1).
                {
                  unfold XPR.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.

                  assert (forall a b c d e f g x0,
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XPD_package d x0 a b c e f g)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XPD_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XPD.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
                Unshelve.
                2:{ admit. }
                2:{ apply H1. }

                {
                  admit.
                (*   intros. *)
                (*   unfold XPR. *)

                (*   Optimize Heap. *)
                (*   (* Optimize Proof. *) *)
                  
                (*   unfold "++". *)
                (*   unfold map_with_in. *)
                (*   rewrite parallel_raw_cons. *)
                (*   (* rewrite !parallel_raw_cons. *) *)
                (*   Time Optimize Heap. *)
                (*   rewrite unionmE. *)

                (*   unfold R_ch_map_XPD_package. *)
                (*   rewrite setmE. *)
                (*   unfold ".1", ".2". *)
                (*   unfold SET, GET. *)
                (*   unfold XPD. *)

                (*   replace (_ == _) with false ; [ | symmetry ]. *)
                (*   2: apply /eqP ; solve_imfset_disjoint. *)
                (*   now rewrite emptymE. *)
                (* } *)

                (* repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE). *)
                (* now rewrite emptymE. *)
                (*   replace (isSome (getm _ _)) with false ; [ | symmetry ]. *)
                (*   2: now rewrite H3. *)
                (*   2:{ *)
                (*     unfold R_ch_map_XPD_package. *)
                (*     rewrite setmE. *)
                (*     unfold ".1", ".2". *)
                (*     unfold SET, GET. *)
                (*     unfold XPD. *)

                (*     replace (_ == _) with false ; [ | symmetry ]. *)
                (*     2: apply /eqP ; solve_imfset_disjoint. *)

                (*     now rewrite emptymE. *)
                (*   } *)
                }
              }
              {
                unfold R_ch_map_XTR_packages.

                unfold eq_rect_r.
                unfold eq_rect.
                destruct Logic.eq_sym.

                unfold ℓ_packages.
                unfold pack.
                unfold ℓ_raw_packages.

                (* Set Printing Implicit. *)
                erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (map_with_in XTR_names (fun y _ => pack (R_ch_map_XTR_package d n _ (λ _ : name, M) _ _)))) x x0 1 d _ H1).
                {
                  unfold XTR_names.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.

                  assert (forall a b c d e x0,
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XTR_package d x0 a b c e)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XTR_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XTR_names.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H3] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
                Unshelve.
                2: apply H1.
                {
                  intros.

                  unfold XTR_names.
                  unfold "++".
                  unfold map_with_in.
                  rewrite !parallel_raw_cons.
                  rewrite unionmE.
                  
                  assert (forall a b c d e k x0,
                             (k <= d)%nat ->
                             (x0 <= d)%nat ->
                             getm (pack (R_ch_map_XTR_package d k a b c e)) (serialize_name x x0 d 1) = None).
                  {
                    intros.
                    unfold R_ch_map_XTR_package.
                    rewrite setmE.
                    unfold ".1", ".2".
                    unfold SET, GET.
                    unfold XTR_names.

                    replace (_ == _) with false ; [ | symmetry ].
                    2: apply /eqP ; solve_imfset_disjoint.
                    now rewrite emptymE.
                  }

                  rewrite unionmE.
                  repeat (replace (isSome (getm _ _)) with false ; [ | symmetry ] ; [ | now rewrite H5] ; try rewrite unionmE).
                  now rewrite emptymE.
                }
            }
          }

          rewrite mapmE.
          {
            unfold Ks.
            unfold eq_rect_r.
            unfold eq_rect.
            destruct Logic.eq_sym.
            destruct function2_fset_cat.

            unfold combined.

            unfold ℓ_packages.
            unfold pack.
            unfold ℓ_raw_packages.

            eassert (forall H_le,
                        parallel_raw
                          (List.map (λ y : name, pack (K_package d y x0 H_le false)) O_star)
                          (serialize_name x x0 d 1)
                        = some (_)).
            {
              clear -H2 ; intros.
              induction O_star.
              - easy.
              - move: H2 => /orP [ /eqP H2 | H2 ] ; subst.
                + rewrite map_eta.
                  rewrite parallel_raw_cons.
                  rewrite unionmE.

                  unfold K_package.

                  set ([fmap _ ; _ ]).
                  set (Option_Some _).
                  assert (getm f (serialize_name a x0 d 1) = o) ; subst f o.
                  {
                    unfold K_package.
                    rewrite !setmE.
                    unfold ".1", ".2".
                    unfold SET.

                    replace (_ == _) with false.
                    2: symmetry ; apply /eqP ; solve_imfset_disjoint.

                    rewrite eqxx.
                    reflexivity.
                  }
                  rewrite H2.
                  unfold isSome.
                  reflexivity.
                + rewrite map_eta.
                  rewrite parallel_raw_cons.
                  rewrite unionmE.

                  unfold K_package.
                  rewrite !setmE.
                  unfold ".1", ".2".
                  unfold SET.

                  replace (_ == _) with false.
                  2: symmetry ; apply /eqP ; solve_imfset_disjoint.
                  
                  destruct (x == a) eqn:s_eq ; move: s_eq => /eqP s_eq ; subst.
                  * rewrite eqxx.
                    reflexivity.
                  * replace (_ == _) with false ; [ | symmetry ; apply /eqP ].
                    2: now apply serialize_name_notin_different_name.
                    rewrite emptymE.
                    unfold isSome.

                    apply IHl.
                    apply H2.
            }
            
            erewrite (map_with_in_num_upper_getm d d (leqnn d) (fun d n x1 => parallel_raw (List.map (fun y => pack (K_package d y n x1 false)) O_star)) x x0 1 d _ H1).
            {
             now rewrite H3.
            }
            {
              clear ; intros.
              induction O_star.
              - easy.
              - rewrite map_eta.
                rewrite parallel_raw_cons.
                rewrite unionmE.

                rewrite !setmE.
                unfold ".1", ".2".
                unfold SET, GET.

                destruct (n == k) eqn:n_is_neq_k ; move: n_is_neq_k => /eqP n_is_neq_k ; subst.
                * Lia.lia.
                * replace (_ == _) with false ; [ | symmetry ].
                  2: apply /eqP ; solve_imfset_disjoint.

                  replace (_ == _) with false ; [ | symmetry ].
                  2: apply /eqP ; solve_imfset_disjoint.

                  now rewrite emptymE.
            }
          }
          }
          Unshelve.
          2: apply H1.

          
          (* epose getmP. *)

          unfold get_or_fn.
          unfold bind ; fold @bind.
          unfold code_link ; fold @code_link.
          
          ssprove_sync.
          1: admit.
          intros.

          destruct a.
          + simpl.
            apply r_ret.
            intros.
            split.
            * reflexivity.
            * apply H3.
          + simpl.
            ssprove_sync.
            intros.
            apply r_ret.
            split.
            * reflexivity.
            * apply H3.
      }
  }
Admitted.

Axiom AdvantageFrame : forall G0 G1 G2 G3 A,
    (AdvantageE G0 G1 A = 0)%R ->
    (AdvantageE G2 G3 A = 0)%R ->
    AdvantageE G0 G2 A = AdvantageE G1 G3 A.

Lemma map_outro_c5 :
  forall (d : nat),
  forall (Score : Simulator d),
  forall (LA : {fset Location}) (A : raw_package),
    ValidPackage LA (KS_interface d) A_export A →
    (AdvantageE
       (Gks_real d)
       (Gks_ideal d Score) (A) =
     AdvantageE
       (Gks_real_map d)
       (Gks_ideal_map d Score) A
    )%R.
Proof.
  intros.
  unfold Gks_real.
  unfold Gks_real_map.
  unfold pack.

  (* apply AdvantageFrame ; [ now rewrite map_intro_c2 | ]. *)

  unfold Gks_ideal.
  unfold Gks_ideal_map.
  unfold pack.

  unfold Gcore_ideal.

  (* rewrite <- link_assoc. *)
  (* epose Advantage_link. *)
  (* rewrite <- Advantage_link. *)
  (* rewrite <- Advantage_link. *)
  (* rewrite <- Advantage_link. *)

  (* unfold R_ch_map. *)
  (* reflexivity. *)
Admitted.

End MapPackages.
