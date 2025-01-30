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

Notation " 'chXTRinp' " :=
  (chHandle × chHandle)
    (in custom pack_type at level 2).
Notation " 'chXTRout' " :=
  (chHandle)
    (in custom pack_type at level 2).
(* Context {xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle}. *)

(* fig. 29 *)
Definition R_ch_map_XTR_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) :
  (List.In n XTR_names) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  package L_M (XTR_n_ℓ (* ℓ.+1 *))
    [interface
       #val #[ XTR n ℓ (* ℓ.+1 *)] : chXTRinp → chXTRout
    ].
Proof.
  intros.
  refine [package
     #def #[ XTR n ℓ (* ℓ.+1 *) ] ('(h1,h2) : chXTRinp) : chXTRout {
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
        #import {sig #[ XTR n ℓ' (* ℓ.+1 *) ] : chXTRinp → chXTRout }
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


Definition R_ch_map_XTR_packages (* (d : nat) *) (M : chHandle -> nat)
  (H_inLM : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M) :
  package L_M (XTR_n_ℓ (* d *)) (XTR_n_ℓ (* d *)).

  assert (H1 : forall n, ∀ x y : ExtraTypes_name__canonical__eqtype_Equality,
             x ≠ y
             → idents [interface #val #[XTR x n] : chXTRinp → chXTRout ]
                 :#: idents [interface #val #[XTR y n] : chXTRinp → chXTRout ]
         ).
  {
    intros.
    unfold idents.
    solve_imfset_disjoint.
  }

  assert (H2 : uniq XTR_names) by reflexivity.

  assert (H3 : forall ℓ, trimmed_pairs
    (@List.map (Equality.sort ExtraTypes_name__canonical__eqtype_Equality) Interface
       (fun n : name =>
        @fset
          (Datatypes_prod__canonical__Ord_Ord Datatypes_nat__canonical__Ord_Ord
             (Datatypes_prod__canonical__Ord_Ord choice_type_choice_type__canonical__Ord_Ord
                choice_type_choice_type__canonical__Ord_Ord))
          (@cons (prod nat (prod choice_type choice_type))
             (@pair nat (prod choice_type choice_type) (@XTR DepInstance n ℓ)
                (@pair choice_type choice_type (chProd chHandle chHandle) chHandle))
             (@nil (prod nat (prod choice_type choice_type))))) XTR_names)
    (@map_with_in (Equality.sort ExtraTypes_name__canonical__eqtype_Equality) raw_package XTR_names
       (fun (x : name) (H0 : @List.In name x XTR_names) =>
          @pack _ _ _ (R_ch_map_XTR_package ℓ x (fun _ : name => M) H0 H_inLM)))).
  {
    unfold pack.
    unfold map_with_in, XTR_names.
    unfold parallel_raw.
    unfold List.fold_left.
    unfold List.map.
    unfold trimmed_pairs.
    repeat split ; unfold trimmed ; trim_is_interface.
  }

  set (XTR_n_ℓ) at 2.
  rewrite (interface_hierarchy_trivial XTR_n_ℓ XTR_names d _).
  2: easy.
  subst i.
  refine (ℓ_packages
            d
            (fun ℓ H => {package parallel_raw (map_with_in XTR_names (fun x H0 => pack (R_ch_map_XTR_package ℓ x (fun _ => M) H0 H_inLM)))
                        #with
                 (valid_forall_map_with_in
                    (λ (n : name) (ℓ : nat), XTR_n_ℓ (* [interface #val #[XTR n ℓ] : chXTRinp → chXTRout ] *))
                    (λ n : name, [interface #val #[XTR n ℓ] : chXTRinp → chXTRout ])
                    XTR_names
                    (λ ℓ (x : name) (H0 : List.In x XTR_names), R_ch_map_XTR_package ℓ x (λ _ : name, M) H0 H_inLM)
                    d
                    ℓ
                    H (H1 _) H2 (H3 _) _ ) })
            _ (fun _ _ => trimmed_parallel_raw _ _ _ (H1 _) H2 (H3 _)) _ ).
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

Definition R_ch_map_XPD_package (ℓ : nat) (n : name) (M : name -> chHandle -> nat) (M_ℓ : name -> nat -> chHandle -> nat) :
  (List.In n XPR) ->
  (forall s1 s, ('option ('fin #|fin_handle|); M s1 s) \in L_M) ->
  (forall s1 s k, ('option ('fin #|fin_handle|); M_ℓ s1 s k) \in L_M) ->
  package L_M (XPD_n_ℓ (* ℓ.+1 *))
    [interface
       #val #[ XPD n ℓ (* ℓ.+1 *) ] : chXPDinp → chXPDout
    ].
  intros.
  refine [package
     #def #[ XPD n ℓ (* ℓ.+1 *) ] ('(h1,r,args) : chXPDinp) : chXPDout {
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

            #import {sig #[ XPD n ℓ1 (* ℓ.+1 *) ] : chXPDinp → chXPDout }
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

Lemma trimmed_R_ch_map_XPD_package : forall n ℓ M1 M2 A B C, trimmed [interface
       #val #[ XPD n ℓ (* d.+1 *) ] : chXPDinp → chXPDout
    ] (R_ch_map_XPD_package ℓ n M1 M2 A B C).
Proof.
  intros.

  unfold R_ch_map_XPD_package.
  unfold pack.
  apply trimmed_package_cons.
  apply trimmed_empty_package.
Qed.

Lemma trimmed_parallel_raw_R_ch_map_XPD :
  (* forall (d : nat), *)
  forall (M : chHandle → nat),
  forall (H_L_M : ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M),
    trimmed (interface_foreach (fun n => [interface
       #val #[ XPD n d (* d.+1 *) ] : chXPDinp → chXPDout
    ]) XPR) (parallel_raw
       (map_with_in XPR
          (λ (x : name) (H0 : List.In x XPR),
             pack (R_ch_map_XPD_package d x (λ _ : name, M) (λ (_ : name) (_ : nat), M) H0
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

Definition R_ch_map_XPD_packages  (* (d : nat) *) (M : chHandle -> nat) :
  (forall s, ('option ('fin #|fin_handle|); M s) \in L_M) ->
  package L_M (XPD_n_ℓ (* d *)) (XPD_n_ℓ (* d *)).
  intros H_L_M.
  (* refine (ℓ_packages *)
  (*           d (fun ℓ H => {package parallel_raw (map_with_in XPR (fun x H => pack (R_ch_map_XPD_package ℓ x (fun _ => M) (fun _ _ => M) H (fun _ => H_L_M) (fun _ _ => H_L_M)))) #with _ }) *)
  (*   _ _ _). *)

  (* 2: intros ; apply trimmed_parallel_raw_R_ch_map_XPD. *)
  (* 2: now apply interface_foreach_idents_XPD. *)
  
  assert (H1 : forall n, ∀ x y : ExtraTypes_name__canonical__eqtype_Equality,
             x ≠ y
             → idents [interface #val #[XPD x n] : chXPDinp → chXPDout ]
                 :#: idents [interface #val #[XPD y n] : chXPDinp → chXPDout ]
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
             (@pair nat (prod choice_type choice_type) (@XPD DepInstance n ℓ)
                (@pair choice_type choice_type (chProd (chProd chHandle chBool) bitvec) chHandle))
             (@nil (prod nat (prod choice_type choice_type))))) XPR)
    (@map_with_in (Equality.sort ExtraTypes_name__canonical__eqtype_Equality) raw_package XPR
       (fun (x : name) (H0 : @List.In name x XPR) =>
        @pack _ _ _
          (R_ch_map_XPD_package ℓ x (fun _ : name => M) (fun (_ : name) (_ : nat) => M) H0
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
    repeat split ; unfold trimmed ; try trim_is_interface.
  }

  set (XPD_n_ℓ) at 2.
  rewrite (interface_hierarchy_trivial XPD_n_ℓ XPR d _).
  2: easy.
  subst i.
  refine (ℓ_packages
            d
            (fun ℓ H => {package parallel_raw (map_with_in XPR (fun x H0 => pack (R_ch_map_XPD_package ℓ x (fun _ => M) (fun _ _ => M) H0 (fun _ => H_L_M) (fun _ _ => H_L_M))))
                        #with
                 (valid_forall_map_with_in
                    (λ (n : name) (ℓ : nat), XPD_n_ℓ (* [interface #val #[XPD n ℓ] : chXPDinp → chXPDout ] *))
                    (λ n : name, [interface #val #[XPD n ℓ] : chXPDinp → chXPDout ])
                    XPR
                    (λ ℓ (x : name) (H0 : List.In x XPR), R_ch_map_XPD_package ℓ x (λ _ : name, M) (λ _ _ , M) H0 _ _)
                    d
                    ℓ
                    H (H1 _) H2 (H3 _) _ ) })
            _ (fun _ _ => trimmed_parallel_raw _ _ _ (H1 _) H2 (H3 _)) _ ).
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

(* R_ch_map, fig.25, Fig. 27, Fig. 29 *)
(* GET_o_star_ℓ d *)
Definition R_ch_map (* (d : nat) *) :
  package L_M
    ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ (* d *) :|:
    XPD_n_ℓ (* d *))
    ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ]).
  refine (let base_package : package L_M
    ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ (* d *) :|:
    XPD_n_ℓ (* d *)) ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ])
  :=
    [package
     #def #[ SET PSK 0 d ] ('(h,hon,k) : chSETinp) : chSETout {
        #import {sig #[ SET PSK 0 d ] : chSETinp → chSETout }
        as set_fn ;;
        nh ← set_fn (h, hon, k) ;;
        set_at (H := pos_handle) (M h) fin_handle (otf nh) ;;
        ret h
      } ;
   #def #[ DHGEN ] (t : 'unit) : 'unit {
        #import {sig #[ DHGEN ] : 'unit → 'unit }
        as dhgen ;;
        dhgen Datatypes.tt
      } ;
     #def #[ DHEXP ] (t : 'unit) : 'unit {
        ret (Datatypes.tt : 'unit)
      }
    ]
  in _).

  Unshelve.
  2-9: try apply DepInstance ; shelve.
  
  1: refine ({package
     par (base_package
     ) (R_ch_map_XTR_packages (* d *) M H) }).
  1:{
  ssprove_valid.
  {
    (* simpl. *)
    unfold FDisjoint.
    apply @parable.

    eassert (trimmed _ (R_ch_map_XTR_packages M H)).
    {
      admit.
    }
    rewrite <- H.

    eassert (trimmed _ base_package).
    {
      admit.
    }
    rewrite <- H0.

    solve_Parable.
    admit.
  }
  {
    rewrite fsetUid.
    apply fsubsetxx.
  }
  {
    (* rewrite <- fsetUA. *)
    (* rewrite (fsetUC XPD_n_ℓ). *)
    (* rewrite <- fsetUA. *)
    (* rewrite (fsetUA XTR_n_ℓ). *)
    (* rewrite fsetUid. *)
    (* rewrite fsetUA. *)
    (* apply fsubsetxx. *)
    solve_in_fset.
  }
  {
    solve_in_fset.
  }
  }
  {
    unfold set_at.
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
      apply /orP ; left.
      rewrite in_fset1.
      reflexivity.
    }
    {
      rewrite !in_fsetU.
      apply /orP ; left.
      apply /orP ; left.
      rewrite fset_cons.
      rewrite !in_fsetU.
      apply /orP ; left.
      rewrite in_fset1.
      unfold mkopsig.
      apply eqxx.
    }
    {
      admit.
    }
  }
  Unshelve.
  1,2: admit.
Admitted.
Admit Obligations.
Fail Next Obligation.

Program Definition Gks_real_map (* (d : nat) *) :
  package
    fset0
    ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout
    ] :|:
    GET_O_star_ℓ)
    [interface] :=
  {package R_ch_map (* d *) ∘ ((* (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E) ) ∘ *) Gcore_real (* d *)) }.
Fail Next Obligation.

Program Definition Gks_ideal_map (* (d : nat) *) (Score : Simulator) :
  package
    fset0
    ([interface
       #val #[ SET PSK 0 d ] : chSETinp → chSETout ;
       #val #[ DHGEN ] : 'unit → 'unit ;
       #val #[ DHEXP ] : 'unit → 'unit
    ] :|:
    XTR_n_ℓ (* d *) :|:
    XPD_n_ℓ (* d *) :|:
    GET_O_star_ℓ)
    [interface
    ] := {package (R_ch_map (* d *) ∘ (* (par (par (XPD_packages d) (XTR_packages d)) (DH_package ord E) ) ∘ *) Gcore_ideal (* d *) Score) }.
Fail Next Obligation.

Lemma map_intro_c2 :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real (* d *))
       (Gks_real_map (* d *)) A = 0
    )%R.
Proof.
  intros.
  admit.
  
(*   (* (* unfold Gks_real. *) *) *)
(*   (* (* unfold Gks_real_map. *) *) *)
(*   (* (* unfold pack. *) *) *)
(*   (* (* unfold Gcore_real. *) *) *)

(*   (* (* simpl. *) *) *)

(*   (* apply: eq_rel_perf_ind_ignore. *) *)
(*   (* 2: { *) *)
(*   (*   eapply valid_link. *) *)
(*   (*   - apply (pack_valid (R_ch_map d M H)). *) *)
(*   (*   - epose (pack_valid (Gcore_real (ord := ord) (E := E) d)). *) *)
(*   (*     admit. *) *)
(*   (* } *) *)
(*   (* 1: { *) *)
(*   (*   epose (pack_valid (Gks_real ord E d)). *) *)
(*   (*   admit. *) *)
(*   (*   (* apply (pack_valid (Gcore_real d _ _)). *) *) *)
(*   (* } *) *)
(*   (* 1: apply fsubsetxx. *) *)
(*   (* 2:{ *) *)
(*   (*   admit. *) *)
(*   (* } *) *)
(*   (* 2: apply fdisjoints0. *) *)
(*   (* 2: admit. (* rewrite fsetU0 ; apply fdisjoints0. *) *) *)

(*   (* induction d. *) *)
(*   (* - unfold XTR_n_ℓ. unfold XPD_n_ℓ. simpl. *) *)
(*   (*   rewrite <- fset0E. rewrite !fsetU0. *) *)
(*   (*   unfold eq_up_to_inv. *) *)
(*   (*   simplify_eq_rel inp_unit. *) *)
(*   (*   + admit. (* SET PSK 0 *) *) *)
(*   (*   + admit. (* DHGEN *) *) *)
(*   (*   + admit. (* DHEXP *) *) *)
(*   (* - *) *)
(*   (*   assert (forall {n} (x : Simulator (S n)), Simulator n). *) *)
(*   (*   { *) *)
(*   (*     clear. *) *)
(*   (*     intros. *) *)
(*   (*     unfold Simulator in *. *) *)
(*   (*     refine {package (pack x)}. *) *)
(*   (*     eapply (valid_package_inject_import _ _ _ _ _ _ (pack_valid x)). *) *)
(*   (*   } *) *)
(*   (*   specialize (IHd (X _ Score)). clear X. *) *)

(*   (*   unfold eq_up_to_inv. *) *)
(*   (*   intros. *) *)

(*   (*   eassert ([interface #val #[SET_psk 0] : chSETinp → chSETout ; #val #[DHGEN] : 'unit → 'unit ; *) *)
(*   (*                       #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d.+1 :|:  *) *)
(*   (*              XPD_n_ℓ d.+1 :|: GET_o_star_ℓ d.+1 = *) *)
(*   (*             ([interface #val #[SET_psk 0] : chSETinp → chSETout ; #val #[DHGEN] : 'unit → 'unit ; *) *)
(*   (*              #val #[DHEXP] : 'unit → 'unit ] :|: XTR_n_ℓ d :|:  *) *)
(*   (*             XPD_n_ℓ d :|: GET_o_star_ℓ d) :|: _ *) *)
(*   (*           ). *) *)
(*   (*   { *) *)
(*   (*     unfold XTR_n_ℓ ; unfold interface_hierarchy ; fold interface_hierarchy ; fold (@XTR_n_ℓ d). *) *)
(*   (*     unfold XPD_n_ℓ ; unfold interface_hierarchy ; fold interface_hierarchy ; fold (@XPD_n_ℓ d). *) *)
(*   (*     unfold GET_o_star_ℓ ; fold GET_o_star_ℓ. *) *)
(*   (*     rewrite <- !fsetUA. *) *)
(*   (*     f_equal. *) *)
(*   (*     rewrite fsetUC. *) *)
(*   (*     rewrite <- !fsetUA. *) *)
(*   (*     f_equal. *) *)
(*   (*     rewrite fsetUC. *) *)
(*   (*     rewrite <- !fsetUA. *) *)
(*   (*     f_equal. *) *)
(*   (*     rewrite fsetUC. *) *)
(*   (*     rewrite <- !fsetUA. *) *)
(*   (*     f_equal. *) *)
(*   (*   } *) *)
(*   (*   rewrite H1 in H0. clear H1. *) *)
(*   (*   rewrite in_fsetU in H0. *) *)
(*   (*   apply (ssrbool.elimT orP) in H0. *) *)
(*   (*   destruct H0. *) *)
(*   (*   + specialize (IHd id S T x H0). *) *)
(*   (*     clear H0. *) *)

(*   (*     replace (get_op_default *) *)
(*   (*      (par (par (XPD_packages d.+1 _ _) (XTR_packages d.+1 _ _)) DH_package *) *)
(*   (*       ∘ DH_package ∘ Gcore_hyb d.+1) (id, (S, T))) with *) *)
(*   (*       (get_op_default *) *)
(*   (*      (par (par (XPD_packages d PrntN Labels) (XTR_packages d PrntN Labels)) DH_package *) *)
(*   (*       ∘ DH_package ∘ Gcore_hyb d) (id, (S, T))) by admit. *) *)
(*   (*     replace (get_op_default (R_ch_map d.+1 _ ∘ Gcore_real d.+1 _ _) (id, (S, T))) with *) *)
(*   (*       (get_op_default (R_ch_map d M ∘ Gcore_real d PrntN Labels) (id, (S, T))) by admit. *) *)

(*   (*     apply IHd. *) *)
(*   (*   + rewrite <- !fset_cat in H0. *) *)
(*   (*     simpl in H0. *) *)
(*   (*     generalize dependent H0. *) *)
(*   (*     generalize dependent x. *) *)
(*   (*     generalize dependent T. *) *)
(*   (*     generalize dependent S. *) *)
(*   (*     generalize dependent id. *) *)
(*   (*     simplify_eq_rel inp_unit. *) *)
(*   (*     * admit. (* XTR ES d *) *) *)
(*   (*     * admit. (* XTR HS d *) *) *)
(*   (*     * admit. (* XTR AS d *) *) *)
(*   (*     * admit. (* XPD N d *) *) *)
(*   (*     * admit. (* XPD PSK d *) *) *)
(*   (*     * admit. (* XPD ESALT d *) *) *)
(*   (*     * admit. (* GET_o_star TODO d *) *) *)
Admitted.

Axiom AdvantageFrame : forall G0 G1 G2 G3 A,
    (AdvantageE G0 G1 A = 0)%R ->
    (AdvantageE G2 G3 A = 0)%R ->
    AdvantageE G0 G2 A = AdvantageE G1 G3 A.

Lemma map_outro_c5 :
  (* forall (d : nat), *)
  forall (Score : Simulator),
  forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA [interface #val #[ KS ] : 'unit → chTranscript ] A_export A →
    (AdvantageE
       (Gks_real (* d *))
       (Gks_ideal (* d *) Score) (A) =
     AdvantageE
       (Gks_real_map (* d *))
       (Gks_ideal_map (* d *) Score) A
    )%R.
Proof.
  intros.
  unfold Gks_real.
  unfold Gks_real_map.
  unfold pack.

  apply AdvantageFrame ; [ now rewrite map_intro_c2 | ].

  (* epose AdvantageE_equiv. *)
  (* epose (map_intro_c2 d M Score LA A H). *)
  (* epose (AdvantageE_equiv _ ). *)

  (* apply eq_ler. *)

  (* rewrite c2. *)

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
