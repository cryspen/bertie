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

Inductive name :=
| N | PSK | ESALT
| ES
| HS
| AS
| BOT.
Definition bitvec := chNat. (* {0,1}^96 *)
Definition label_ty := chFin (mkpos (Nat.pow 2 96)). (* {0,1}^96 *)
Definition chName : choice_type := chFin (mkpos 7).

(* Base handles are defined on p. 16 *)
(* Definition handle := chName × t_Bytes × t_HashAlgorithm × int8. *)
Definition calc_handle_size := ( 7 + Nat.pow 2 96 + 3 + Nat.pow 2 256 )%nat.
Definition chHandle : choice_type := chFin (mkpos calc_handle_size).

Axiom chName_to_name : chName -> name.

Inductive hash_algorithm :=
| sha256
| sha384
| sha512.

Definition chHash : choice_type := chFin (mkpos 3).

Axiom chHash_to_hash : chName -> name.

Definition chKey := (chHash × chName).


Axiom xpd_angle : name -> label_ty -> chHandle -> bitvec -> raw_code chHandle.

Inductive XPR :=
| XPR_N
| XPR_PSK
| XPR_ESALT.

Inductive O_star := TODO.
