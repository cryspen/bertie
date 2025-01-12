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

(*** Extra types *)

Notation " 'chTranscript' " :=
  (t_Handle)
    (in custom pack_type at level 2).

Definition KS : nat := 0%nat.

(* Fig. 12, p. 18 *)
(* Fig.29, P.63 *)


#[global] Instance pos_bool : Positive #|'bool| :=
  eq_ind_r [eta Positive] (erefl : Positive 2) card_bool.

Definition bitvec := chNat. (* {0,1}^96 *)

#[global] Instance pos_unit : Positive #|'unit| :=
  eq_ind_r [eta Positive] (erefl : Positive 1) card_unit.

(* Label *)
Definition fin_label := 'fin (Nat.pow 2 96).
#[global] Instance pos_label : Positive #|fin_label| :=
  eq_ind_r [eta Positive] (erefl : Positive (Nat.pow 2 96)) (card_ord (Nat.pow 2 96)).
Definition chLabel : choice_type := chFin (mkpos #|fin_label|).

(* Name *)
(* Definition 4.2: names are at least / Fig. 1  *)
Inductive name :=
| BOT

| ES
| EEM
| CET
| BIND
| BINDER
| HS
| SHT
| CHT
| HSALT
| AS
| RM
| CAT
| SAT
| EAM
| PSK

| ZERO_SALT
| ESALT
| DH
| ZERO_IKM
.
Definition all_names :=
  [ES; EEM; CET; BIND; BINDER; HS; SHT; CHT; HSALT; AS; RM; CAT; SAT; EAM; PSK; ZERO_SALT; ESALT; DH; ZERO_IKM].

Definition fin_name : finType := 'fin 20.
#[global] Instance pos_name : Positive #|fin_name| :=
  eq_ind_r [eta Positive] (erefl : Positive 20) (card_ord 20).
Definition chName := chFin (mkpos #|fin_name|).

(* Hash *)
Inductive hash_algorithm :=
| sha256
| sha384
| sha512.
Definition fin_hash : finType := 'fin 3.
#[global] Instance pos_hash : Positive #|fin_hash| :=
  eq_ind_r [eta Positive] (erefl : Positive 3) (card_ord 3).
Definition chHash : choice_type := chFin (mkpos #|fin_hash|).

Axiom chHash_to_hash : chHash -> name.

(* Base handles are defined on p. 16 *)

#[global] Instance pos_prod {A B : finType} (x : Positive #|A|) (y : Positive #|B|) : Positive #|Casts.prod_finType A B|.
Proof.
  rewrite (card_prod _ _).
  apply (Positive_prod x y).
Defined.

(* Definition handle := chName × t_Bytes × t_HashAlgorithm × int8. *)
Definition fin_handle : finType :=
  Casts.prod_finType
    (fin_name)
    (Casts.prod_finType
       (fin_label)
       (Casts.prod_finType
          (fin_hash)
          ('unit))).
#[global] Instance pos_handle : Positive #|fin_handle| :=
  pos_prod (pos_name) (pos_prod pos_label (pos_prod pos_hash pos_unit))
.
Definition chHandle : choice_type := chFin (mkpos #|fin_handle|).

Definition chHandle_to_chHash (h : chHandle) : chHash :=
  fto (fst (snd (snd (otf h)))).

(* Axiom chName_to_name : chName -> name. *)

Definition fin_key := (Casts.prod_finType fin_hash fin_name).
#[global] Instance pos_key : Positive #|fin_key| := pos_prod pos_hash pos_name.
Definition chKey := chFin (mkpos #|fin_key|).

Definition chKey_to_chName (h : chKey) : chName :=
  fto (snd (otf h)).

(* Axiom xpd_angle : name -> chLabel -> chHandle -> bitvec -> raw_code chHandle. *)

(* Inductive XPR := *)
(* | XPR_N *)
(* | XPR_PSK *)
(* | XPR_ESALT. *)

Inductive O_star := TODO.
