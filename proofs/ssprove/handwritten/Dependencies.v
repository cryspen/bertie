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

Axiom chGroup : choice_type.
Axiom chGroup_is_finGroup : FinGroup chGroup.
Axiom gen : chGroup -> code fset0 fset0 chGroup.

Definition fin_K_table : finType := Casts.prod_finType fin_key 'bool.
Definition chK_table := 'fin #|fin_K_table|.

Definition fin_L_table : finType :=
  Casts.prod_finType (Casts.prod_finType fin_handle 'bool) fin_key.
Definition chL_table := 'fin #|fin_L_table|.

Definition PrntN (n : name) : chProd chName chName :=
  let (a,b) :=
    match n with
    | ES => (ZERO_SALT, PSK)
    | EEM | CET | ESALT | BIND => (ES, BOT)
    | BINDER => (BIND, BOT)
    | HS => (ESALT, DH)
    | SHT | CHT | HSALT => (HS, BOT)
    | AS => (HSALT, ZERO_IKM)
    | CAT | SAT | RM | EAM => (AS, BOT)
    | PSK => (RM, BOT)
    | _ => (BOT, BOT)
    end
  in (name_to_chName a, name_to_chName b).

Class Dependencies := {
    TLSPrntN: name -> (* code fset0 fset0 *) (chProd chName chName) ;
    TLSPrntN_is_PrntN: forall n, PrntN n == TLSPrntN n ;

    Labels : name -> bool -> code fset0 fset0 chLabel ;
    (* O_star : list name ; *)
    xpd : chKey -> (chLabel * bitvec) -> code fset0 fset0 chKey ;
    xtr : chKey -> chKey -> code fset0 fset0 chKey ;
    xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle ;
    xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle ;
    PrntIdx : name -> forall (ℓ : bitvec), code fset0 [interface] (chProd chName chName) ;
    ord : chGroup → nat ;
    E : nat -> nat ;

    L_L : {fset Location} ;
    L_table : chHandle -> nat ;
    in_L_table : forall x, ('option chL_table; L_table x) \in L_L ;

    L_K : {fset Location} ;
    K_table : chHandle -> nat ;
    in_K_table : forall x, ('option chK_table; K_table x) \in L_K ;

    L_M : {fset Location} ;
    M : chHandle -> nat ;
    H : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); M s) \in L_M ;

    d : nat ;

    DHGEN_function : chGroup -> code fset0 fset0 chGroup ;
    DHEXP_function : chGroup -> chGroup -> code fset0 fset0 chHandle ;
  }.

Lemma TlsLikeKeySchedule :
  (ZERO_SALT \in all_names)
  /\ (PSK \in all_names)
  /\ (ES \in all_names)
  /\ (ESALT \in all_names)
  /\ (DH \in all_names)
  /\ (HS \in all_names)
  /\ (HSALT \in all_names)
  /\ (ZERO_IKM \in all_names)
  /\ (AS \in all_names)
  /\ (RM \in all_names)
  (* Maps 0salt, dh and 0ikm to (⊥,⊥) *)
  /\ PrntN ZERO_SALT = (name_to_chName BOT, name_to_chName BOT)
  /\ PrntN DH = (name_to_chName BOT, name_to_chName BOT)
  /\ PrntN ZERO_IKM = (name_to_chName BOT, name_to_chName BOT)
  (* Maps es, hs and as by *)
  /\ PrntN ES = (name_to_chName ZERO_SALT, name_to_chName PSK)
  /\ PrntN HS = (name_to_chName ESALT, name_to_chName DH)
  /\ PrntN AS = (name_to_chName HSALT, name_to_chName ZERO_IKM)
  (* Remaining names *)
  /\ forall n,
      n \notin [:: ZERO_SALT; DH; ZERO_IKM; ES; HS; AS] ->
      n \in all_names ->
      exists n1, ((PrntN n = (name_to_chName n1, name_to_chName BOT)) /\ (n1 != BOT)).
Proof.
  repeat split.
  intros.
  rewrite !in_cons in H1.
  rewrite !notin_cons in H0.
  repeat (move: H0 => /andP [ /eqP ] ? H0) ; clear H0.
  repeat (move: H1 => /orP [ /eqP ? | H1 ] ; subst) ; [ .. | discriminate ].
  all: try contradiction.
  all: try (eexists ; split ; [ reflexivity | apply /eqP ; try discriminate ]).
Qed.

Definition chFinGroup : finGroupType :=
  {| FinGroup.sort := chGroup; FinGroup.class := chGroup_is_finGroup |}.
