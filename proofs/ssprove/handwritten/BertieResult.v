From mathcomp Require Import all_ssreflect fingroup.fingroup ssreflect.
Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve Require Import choice_type Package Prelude.
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

From SSProve Require Import jasmin_word.

From SSProve Require Import Schnorr SigmaProtocol.

From SSProve Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From SSProve Require Import SPropBase.

From SSProve Require Import Axioms ChoiceAsOrd SubDistr Couplings
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

(* From KeyScheduleTheorem Require Import ssp_helper. *)

(* From KeyScheduleTheorem Require Import BasePackages. *)
(* From KeyScheduleTheorem Require Import KeyPackages. *)
(* From KeyScheduleTheorem Require Import XTR_XPD. *)

(* From KeyScheduleTheorem Require Import Core. *)
(* From KeyScheduleTheorem Require Import MapPackage. *)

From KeyScheduleTheorem Require Import CoreTheorem.


From BertieExtraction Require Import Bertie_Tls13keyscheduler_Key_schedule.

(* ./extraction/Fixes.v *)
(* ./extraction/Bertie_Tls13utils.v *)
(* ./extraction/Bertie_Tls13formats_Handshake_data.v *)
(* ./extraction/Bertie_Tls13crypto.v *)
(* ./extraction/Bertie_Tls13formats.v *)
(* ./extraction/Bertie_Tls13keyscheduler_Key_schedule.v *)


Definition name_to_t_TLSname (n : name) {H_not_bot : n <> BOT} : both t_TLSnames :=
  match n return (n <> BOT) -> _ with
  | BOT => fun H => False_rect _ (H erefl)

  | ES => fun _ => TLSnames_ES
  | EEM => fun _ => TLSnames_EEM
  | CET => fun _ => TLSnames_CET
  | BIND => fun _ => TLSnames_Bind
  | BINDER => fun _ => TLSnames_Binder
  | HS => fun _ => TLSnames_HS
  | SHT => fun _ => TLSnames_SHT
  | CHT => fun _ => TLSnames_CHT
  | HSALT => fun _ => TLSnames_HSalt
  | AS => fun _ => TLSnames_AS
  | RM => fun _ => TLSnames_RM
  | CAT => fun _ => TLSnames_CAT
  | SAT => fun _ => TLSnames_SAT
  | EAM => fun _ => TLSnames_EAM
  | PSK => fun _ => TLSnames_PSK

  | ZERO_SALT => fun _ => TLSnames_ZeroSalt
  | ESALT => fun _ => TLSnames_ESalt
  | DH => fun _ => TLSnames_DH
  | ZERO_IKM => fun _ => TLSnames_ZeroIKM
  end H_not_bot.


Definition t_TLSname_option_pair_to_name
  (n : chOption t_TLSnames) : name :=
  match n with
  | None => BOT
  | Some a =>
      match a with
    | TLSnames_ES_case  =>
       ES
    | TLSnames_EEM_case  =>
      EEM
    | TLSnames_CET_case  =>
      CET
    | TLSnames_Bind_case  =>
      BIND
    | TLSnames_Binder_case  =>
      BINDER
    | TLSnames_HS_case  =>
      HS
    | TLSnames_SHT_case  =>
      SHT
    | TLSnames_CHT_case  =>
      CHT
    | TLSnames_HSalt_case  =>
      HSALT
    | TLSnames_AS_case  =>
      AS
    | TLSnames_RM_case  =>
      RM
    | TLSnames_CAT_case  =>
      CAT
    | TLSnames_SAT_case  =>
      SAT
    | TLSnames_EAM_case  =>
      EAM
    | TLSnames_PSK_case  =>
      PSK
    | TLSnames_ZeroSalt_case  =>
      ZERO_SALT
    | TLSnames_ESalt_case  =>
      ESALT
    | TLSnames_DH_case  =>
      DH
    | TLSnames_ZeroIKM_case  =>
      ZERO_IKM
    end
  end.

Definition chHash_to_t_HashAlgorithm (x : chHash) : both t_HashAlgorithm :=
  match (nat_of_ord (otf x)) as k return (k < 3)%nat -> _ with
  | 0 => fun _ => HashAlgorithm_SHA256
  | 1 => fun _ => HashAlgorithm_SHA384
  | 2 => fun _ => HashAlgorithm_SHA512
  | n => fun H => False_rect _ (ltac:(easy))
  end%nat (ltn_ord (otf x)).

Definition t_HashAlgorithm_to_chHash (x : t_HashAlgorithm) : chHash :=
  match x with
  | HashAlgorithm_SHA256_case => fto (inord 0)
  | HashAlgorithm_SHA384_case => fto (inord 1)
  | HashAlgorithm_SHA512_case => fto (inord 2)
  end.

Definition chLabel_to_label (l : chLabel) : (* both *) (chList int8) :=
  (* array_from_list *) (List.map (fun (x : nat) => (* ret_both *) (((otf l / Nat.pow 2 (x * 8)) mod 8)%nat : int8)) (iota 0 12)).

Notation repr := (fun WS x => wrepr WS x : int WS).

Fixpoint t_Bytes_to_nat (x : t_Bytes) : nat :=
  (match x with
   | [] => 0
   | (y :: ys) => t_Bytes_to_nat ys * 256 + Z.to_nat (toword y)
   end%nat).

(* Theorem pow_eq : Nat.pow 2 96 = N.pow 2 96. *)
(* Proof. *)
(*   refine Nnat.Nat2N.inj_pow. *)

(* Definition label_pow := 2. *)

(* Do not compute type.. Nat.pow 2 96 is a large number *)
Definition t_Bytes_to_chLabel (x : t_Bytes) : chLabel.
  apply fto.
  hnf.
  set {| pos := _ |}.
  assert (p.(pos) > 0) by easy.
  generalize dependent p.
  intros.
  destruct p.(pos).
  - discriminate.
  - apply inord.
    apply (t_Bytes_to_nat x).
Defined.

Lemma t_Bytes_to_chLabel_correct :
  forall x, chLabel_to_label (t_Bytes_to_chLabel x) = x.
Proof.
  intros.
  induction x.
  - unfold t_Bytes_to_chLabel.
    unfold pos.
    (* unfold label_pow. *)
Admitted.

Program Definition chKey_to_t_TagKey (x : chKey) `{H_not_bot : nfto (fto (otf x).2) <> BOT} (bytes : both t_Bytes) : both t_TagKey :=
  prod_b (
      chHash_to_t_HashAlgorithm (fto (otf x).1),
      name_to_t_TLSname (H_not_bot := H_not_bot) (nfto (fto (otf x).2)),
      bytes (* TODO *)
    ).

Definition t_TagKey_to_chKey (x : t_TagKey) : chKey :=
  (fto (
      otf (t_HashAlgorithm_to_chHash x.1.1) ,
      otf (name_to_chName (t_TLSname_option_pair_to_name (Some x.1.2)))
    )).

Obligation Tactic := (* try timeout 8 *) idtac.
Program Fixpoint bitvec_to_bitstring (x : bitvec) {measure x} : chList int8 :=
  match x with
  | O => []
  | _ =>
      bitvec_to_bitstring (x / 8)%nat ++ [wrepr _ (Z.of_nat (x mod 8)%nat)]
  end.
Next Obligation.
  intros.
  subst.
  destruct x.
  - Lia.lia.
  - apply Nat.div_lt ; easy.
Qed.
Next Obligation.
  intros.
  easy.
Qed.
Final Obligation.
Admitted.

Section BertieKeySchedule.
  Definition Bertie_PrntN : name -> (* code fset0 fset0 *) (chProd chName chName) :=
    (fun n =>
       match n as k return n = k -> _ with
       | BOT => fun _ => (* {code ret *) (name_to_chName BOT , name_to_chName BOT) (* } *)
       | n0 => fun H =>
                is_pure (
                    letb x := (@f_prnt_n _ _ _ t_TLSkeyscheduler_t_KeySchedule (name_to_t_TLSname (H_not_bot := ltac:(easy)) n)) in
                      bind_both x (fun x =>
                      prod_b (
                          (ret_both (name_to_chName (t_TLSname_option_pair_to_name (fst x)))) ,
                          (ret_both (name_to_chName (t_TLSname_option_pair_to_name (snd x)))))))
                (* {code x ← is_state (both_prog (@f_prnt_n _ _ _ t_TLSkeyscheduler_t_KeySchedule (name_to_t_TLSname (H_not_bot := ltac:(easy)) n))) ;; *)
                (*  ret ( *)
                (*      (name_to_chName (t_TLSname_option_pair_to_name (fst x))) , *)
                (*      (name_to_chName (t_TLSname_option_pair_to_name (snd x)))) *)
                (*    #with *)
                (*   ltac:(ssprove_valid; apply f_prnt_n) *)
                (* } *)
       end erefl).

  Lemma Bertie_PrntN_correct : ∀ n : name, PrntN n == Bertie_PrntN n.
  Proof.
    intros.
    apply /eqP.
    destruct n ; unfold PrntN ; unfold Bertie_PrntN ; now try rewrite let_both_equation_1.
  Qed.

  Program Definition Bertie_Labels : name -> bool -> code fset0 fset0 chLabel :=
    fun n b => {code
               is_state (letb r := f_labels (name_to_t_TLSname n (H_not_bot := _)) (ret_both (b : 'bool)) in
                           matchb r with
                        | Result_Ok_case v => ret_both (t_Bytes_to_chLabel v)
                        | Result_Err_case v => ret_both (t_Bytes_to_chLabel [])
                         end
               )
         #with
             (ChoiceEquality.is_valid_code (both_prog_valid _))}.
  Next Obligation.
    intros.
    admit.
  Admitted.

  Definition Bertie_O_star : list name :=
    [EEM; CET; BIND; BINDER; SHT; CHT; HSALT; RM; CAT; SAT; EAM; PSK; ZERO_SALT; ESALT; DH; ZERO_IKM].

  Program Definition Bertie_xpd : chKey -> (chLabel * bitvec) -> code fset0 fset0 chKey :=
    (λ (H : chKey) (H0 : chLabel -× bitvec),
   let H1 :=
     let n := nfto (fto (otf H).2) in
     match n as n0 return ({n0 = BOT} + {n0 ≠ BOT}) with
     | BOT => left erefl
     | name => right (fun (H2 : name = BOT) => False_ind False ltac:(discriminate))
     end in
   match H1 with
   | left _ =>
     {code ret (fto ((otf H).1, otf (name_to_chName BOT))) }
   | right n =>
       let s := H0.1 in
       let b :=
         xpd
           (chKey_to_t_TagKey (H_not_bot := n) H (ret_both (chLabel_to_label H0.1) (* TODO? *)))
           (ret_both (chLabel_to_label H0.1))
           (ret_both (bitvec_to_bitstring H0.2))
       in
       {code x ← is_state b ;;
        ret
          (fto ((otf H).1,
           let X1 :=
             (match x with
             | Result_Ok_case s0 => Some (snd (fst s0))
             | Result_Err_case _ => None
             end) in
           otf (name_to_chName (t_TLSname_option_pair_to_name X1)))) }
   end).
  Final Obligation.
    intros.
    fold chElement in *.
    ssprove_valid.
    apply b.
  Defined.
  Fail Next Obligation.

  Definition Bertie_xtr : chKey -> chKey -> code fset0 fset0 chKey.
  Proof.
    intros.
    destruct (nfto (fto (otf X).2) == BOT) eqn:X_not_bot ; [ refine {code is_state (ret_both (fto (inord 0, inord 0) : chKey))#with (ChoiceEquality.is_valid_code (both_prog_valid _))} | move /eqP in X_not_bot ].
    destruct (nfto (fto (otf X0).2) == BOT) eqn:X0_not_bot ; [ refine {code is_state (ret_both (fto (inord 0, inord 0) : chKey))#with (ChoiceEquality.is_valid_code (both_prog_valid _))} | move /eqP in X0_not_bot ].
    refine {code is_state (matchb xtr
                             (chKey_to_t_TagKey X (H_not_bot := X_not_bot) (ret_both ([] : t_Bytes) (* TODO *)))
                             (chKey_to_t_TagKey X0 (H_not_bot := X0_not_bot) (ret_both ([] : t_Bytes) (* TODO *))) with
                          | Result_Ok_case v => ret_both (t_TagKey_to_chKey v)
                          | Result_Err_case _ => ret_both (fto (inord 0, inord 0) : chKey)
                           end)
              #with
        (ChoiceEquality.is_valid_code (both_prog_valid _))
      }.
  Defined.

  Definition chHandle_to_t_Handle : forall (h : chHandle), nfto (fto (otf h).1) <> BOT -> t_Handle.
  Proof.
    intros h1 ?.
    unfold t_Handle.

    refine (is_pure (prod_b (_, _, _))).
    + refine (name_to_t_TLSname (nfto (fto (otf h1).1)) (H_not_bot := H)).
    + refine (chHash_to_t_HashAlgorithm (fto (otf h1).2.1)).
    + refine (ret_both 0).
  Defined.

  Definition t_Handle_to_chHandle : forall (h : t_Handle), chHandle.
  Proof.
    intros.
    unfold t_Handle in h.
    destruct h as [[]].
    unfold chHandle.

    apply fto.
    unfold fin_handle.
    refine (otf _, (otf _, _)).
    - apply (name_to_chName (t_TLSname_option_pair_to_name (Some s))).
    - apply (t_HashAlgorithm_to_chHash s0).
    - refine (Datatypes.tt : 'unit). (* TODO *)
  Defined.

  Definition Bertie_xtr_angle : name -> chHandle -> chHandle -> code fset0 fset0 chHandle.
    intros n h1 h2.
    destruct (n == BOT) eqn:n_not_bot ; [ refine {code is_state (ret_both (fto (inord 0, (inord 0, Datatypes.tt)) : chHandle))#with (ChoiceEquality.is_valid_code (both_prog_valid _))} | ].
    destruct (nfto (fto (otf h1).1) == BOT) eqn:h1_not_bot ; [ refine {code is_state (ret_both (fto (inord 0, (inord 0, Datatypes.tt)) : chHandle))#with (ChoiceEquality.is_valid_code (both_prog_valid _))} | ].
    destruct (nfto (fto (otf h2).1) == BOT) eqn:h2_not_bot ; [ refine {code is_state (ret_both (fto (inord 0, (inord 0, Datatypes.tt)) : chHandle))#with (ChoiceEquality.is_valid_code (both_prog_valid _))} | ].
    move /eqP in n_not_bot.
    move /eqP in h1_not_bot.
    move /eqP in h2_not_bot.

    refine (
      {code
         is_state (
           letb x := Bertie_Tls13keyscheduler_Key_schedule.xtr_angle (name_to_t_TLSname (H_not_bot := _) n) (ret_both (chHandle_to_t_Handle h1 _)) (ret_both (chHandle_to_t_Handle h2 _)) in
             matchb x with
             | Result_Ok_case v => ret_both (t_Handle_to_chHandle v)
             | Result_Err_case v => ret_both (fto (inord 0, (inord 0, Datatypes.tt)) : chHandle)
         end
         )
         #with
        (ChoiceEquality.is_valid_code (both_prog_valid _))}) ; assumption.
  Defined.

  (* (name : both t_TLSnames) (left : both t_Handle) (right : both t_Handle) *)

  Definition Bertie_xpd_angle : name -> chLabel -> chHandle -> bitvec -> code fset0 fset0 chHandle.
  Admitted.
  Definition Bertie_PrntIdx : name -> forall (ℓ : bitvec), code fset0 [interface] (chProd chName chName). Admitted.
  Definition Bertie_ord : chGroup → nat. Admitted.
  Definition Bertie_E : nat -> nat. Admitted.

  Definition Bertie_L_K : {fset Location}. Admitted.
  Definition Bertie_K_table : chHandle -> nat. Admitted.
  Definition Bertie_in_K_table : forall x, ('option chK_table; Bertie_K_table x) \in Bertie_L_K. Admitted.

  Definition Bertie_L_L : {fset Location}. Admitted.
  Definition Bertie_L_table : chHandle -> nat. Admitted.
  Definition Bertie_in_L_table : forall x, ('option chL_table; Bertie_L_table x) \in Bertie_L_L. Admitted.

  Definition Bertie_L_M : {fset Location}. Admitted.
  Definition Bertie_M : chHandle -> nat. Admitted.
  Definition Bertie_H : name → ∀ s : chHandle, ('option ('fin #|fin_handle|); Bertie_M s) \in Bertie_L_M. Admitted.

  Definition Bertie_DHGEN_function : chGroup -> code fset0 fset0 chGroup. Admitted.
  Definition Bertie_DHEXP_function : chGroup -> chGroup -> code fset0 fset0 chHandle. Admitted.

End BertieKeySchedule.

Instance BertieKeySchedule (d : nat) : Dependencies :=
  {
    TLSPrntN := Bertie_PrntN;
    TLSPrntN_is_PrntN := Bertie_PrntN_correct ;
    Labels := Bertie_Labels ;

    xpd := Bertie_xpd ;
    xtr := Bertie_xtr ;
    xtr_angle := Bertie_xtr_angle ;
    xpd_angle := Bertie_xpd_angle ;
    PrntIdx := Bertie_PrntIdx ;
    ord := Bertie_ord ;
    E := Bertie_E ;

    L_L := Bertie_L_L ;
    L_table := Bertie_L_table  ;
    in_L_table := Bertie_in_L_table ;

    L_K := Bertie_L_K ;
    K_table := Bertie_K_table ;
    in_K_table := Bertie_in_K_table ;

    L_M := Bertie_L_M ;
    M := Bertie_M ;
    H := Bertie_H ;

    d := d ;

    DHGEN_function := Bertie_DHGEN_function ;
    DHEXP_function := Bertie_DHEXP_function ;
  }.

Definition BertieKeyScheduleCoreTheorem (d k : nat) (H_lt : (d < k)%nat) :=
  core_theorem (DepInstance := BertieKeySchedule d) d k H_lt.
