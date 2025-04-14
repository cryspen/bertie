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
(* From KeyScheduleTheorem Require Import MapPackage. *)

(*** Helper *)

(*** Core theorem *)

Section CoreTheorem.

  Context {DepInstance : Dependencies}.
  Existing Instance DepInstance.


  Definition Gacr (f : HashFunction) (b : bool) :
    package fset0
      [interface]
      [interface #val #[ HASH f_hash ] : chHASHinp → chHASHout].
  (* Proof. *)
  (*   refine [package *)
  (*             #def #[ HASH ] (t : chHASHinp) : chHASHout { *)
  (*               ret fail *)
  (*               (* (* get_or_fn _ _ _ *) *) *)
  (*               (* d ← untag (match f with | f_hash | f_xtr => xtr t end) ;; *) *)
  (*               (* if b && d \in Hash *) *)
  (*               (* then fail *) *)
  (*               (* else *) *)
  (*               (*   ret d *) *)
  (*             } *)
  (*     ]. *)
  (*   Qed. *)
  Admitted.

  Definition R_alg :
    package fset0
      [interface]  (* #val #[ HASH ] : chHASHinp → chHASHout] *)
      [interface].
  Proof.
  Admitted.

  Definition R_cr :
    package fset0
      [interface]  (* #val #[ HASH ] : chHASHinp → chHASHout] *)
      [interface].
  Proof.
  Admitted.

  Definition R_Z (f : HashFunction) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition R_D (f : HashFunction) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition R_xtr (n : name) (ℓ : nat) :
    n \in XTR_names ->
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Definition SblngN (n : name) : list name :=
    filter (fun n' =>
              (nfto (fst (PrntN n)) == nfto (fst (PrntN n')))
           && (nfto (snd (PrntN n)) == nfto (snd (PrntN n')))) all_names.

  Definition ChldrN (n : name) : list name :=
    filter (fun n' => (n == nfto (fst (PrntN n'))) || (n == nfto (snd (PrntN n')))) all_names.

  Inductive POp :=
  | base_op
  | xtr_op
  | xpd_op
  | out_op.
  Definition PrntOp (n : name) : POp :=
    match (nfto (fst (PrntN n)), nfto (snd (PrntN n))) with
    | (BOT, BOT) => base_op
    | (_, BOT) => xpd_op
    | _ => xtr_op
    end.

  Definition ChldrOp (n : name) : POp :=
    match ChldrN n with
    | [] => out_op
    | (x :: _) => PrntOp x
    end.

  HB.instance Definition _ : Equality.axioms_ name :=
    {|
      Equality.eqtype_hasDecEq_mixin :=
        {| hasDecEq.eq_op := name_eq; hasDecEq.eqP := name_equality |}
    |}.

  Definition n1 n := nfto (fst (PrntN n)).
  Definition CN n := ChldrN (n1 n).
  Definition E n := n1 n :: CN n.
  Definition eN_star n := filter (fun x => x \notin E n) (N_star).
  Definition eI_star n := filter (fun x => x \notin E n) (I_star).
  Definition eO_star n := filter (fun x => x \notin E n) (O_star).
  Definition eXPN n := filter (fun x => x \notin CN n) (XTR_names).

  (* R_{n,ℓ}, n \ in XPN \ (PSK,ESALT) (Fig. 34 p. 79) *)
  Definition R_xpd d k (H_lt : (d < k)%nat) (n : name) (ℓ : nat) :
    n \in XPR ->
    (* n \notin [PSK; ESALT] -> *)
    package (L_K :|: L_L)
      ([interface #val #[HASH f_hash] : chHASHout → chHASHout ] :|: (interface_foreach (fun n => XPD_n_ℓ_f k n ℓ) (CN n)) :|: GET_ℓ (CN n) k ℓ :|: SET_ℓ [(n1 n)] k ℓ)
      (((interface_hierarchy_foreach (XPD_n_ℓ_f k) XPR (ℓ.-1)) :|: (interface_hierarchy_foreach (fun n ℓ_off => XPD_n_ℓ_f k n (ℓ.+1 + ℓ_off)) XPR (d - (ℓ.+1))))
         :|: DH_interface
         :|: SET_ℓ [PSK] k 0
         :|: XTR_n d k
         :|: GET_n O_star d k).
  Proof.
    (* intros. *)

    (* epose (G_check_XTR_XPD := *)
    (*         {package *)
    (*            (par *)
    (*               (G_check d k (ltnW H_lt)) *)
    (*               (par *)
    (*                  (combined_ID d XTR_names (fun n ℓ => [interface #val #[ XTR n ℓ k ] : chXTRinp → chXTRout]) _ erefl _ _) *)
    (*                  (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout]) _ erefl _ _)) *)
    (*               ∘ (par *)
    (*                    (combined_ID d O_star (fun n ℓ => [interface #val #[ GET n ℓ k ] : chGETinp → chGETout]) _ erefl _ _) *)
    (*                    (G_XTR_XPD d k (fun name => match name with HS => true | _ => false end) H_lt))) *)
    (*       }). *)

    (* epose {package *)
    (*    (par *)
    (*       (G_check_XTR_XPD) *)
    (*       (par *)
    (*          (G_dh d k (ltnW H_lt)) *)
    (*          (parallel_ID k [:: PSK] (fun n => [interface #val #[ SET n 0 k ] : chSETinp → chSETout]) _ erefl _) *)
    (*       ) *)
    (*    ) ∘ (KeysAndHash d k H_lt (fun ℓ_i name => *)
    (*             if (name \in XTR_names) *)
    (*             then *)
    (*               if (ℓ_i.+1 <=? ℓ)%nat then false else true *)
    (*             else false) *)
    (*           (fun name => match name with | ESALT => R | _ => D end) all_names erefl) *)
    (*   }. *)
  Admitted.

  (* Definition R_xpd (n : name) (ℓ : nat) : *)
  (*   n \in XPR -> *)
  (*   package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface]. *)
  (* Proof. *)
  (* Admitted. *)

  Definition R_pi (L : list name) :
    package fset0 [interface] (* [#val #[ HASH_ f ] : chHASHinp → chHASHout] *) [interface].
  Proof.
  Admitted.

  Axiom Gsodh :
    forall (d k : nat),
      (d < k)%nat ->
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Gxtr :
    forall (d k : nat),
      (d < k)%nat ->
      forall (n : name) (ℓ : nat),
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  (* Fig. 24(a), p. 40 *)
  Definition Gxpd :
    forall (d k : nat),
      (d < k)%nat ->
      forall (n : name) (ℓ : nat),
    loc_GamePair
      ([interface #val #[HASH f_hash] : chHASHout → chHASHout ]
         :|: [interface #val #[ UNQ (n1 n) k ] : chUNQinp → chUNQout]
         :|: SET_ℓ [n1 n] k ℓ
         :|: interface_foreach (fun n => XPD_n_ℓ_f k n ℓ) (CN n)
         :|: GET_ℓ (CN n) k ℓ
         :|: interface_foreach (fun n => [interface #val #[ UNQ n k ] : chUNQinp → chUNQout]) (CN n)
      ).
  Proof.
  Admitted.

  Axiom Gpi :
    forall (d k : nat),
      (d < k)%nat ->
      forall (L : list name)
      (f : ZAF),
    loc_GamePair
      [interface
         (* #val #[ SODH ] : 'unit → 'unit *)
      ].

  Axiom Ai : raw_package -> bool -> raw_package.
  Axiom R_sodh : package fset0 [interface] [interface].

  Lemma d2 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core d k false H_lt) (G_core d k true H_lt) A
       <= Advantage (Gacr f_hash) (A ∘ R_cr) +
         AdvantageE (G_core_Hash d k H_lt) (G_core d k true H_lt) A)%R.
  Proof.
    intros.
  Admitted.

  Lemma d3 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_Hash d k H_lt) (G_core_D d k H_lt) A
       <= Advantage (Gacr f_xtr) (A ∘ (R_Z f_xtr)) +
         Advantage (Gacr f_xpd) (A ∘ (R_Z f_xpd)) +
         Advantage (Gacr f_xtr) (A ∘ (R_D f_xtr)) +
         Advantage (Gacr f_xpd) (A ∘ (R_D f_xpd)))%R.
  Proof.
    intros.
  Admitted.

  (* Lemma d4 : *)
  (*   forall (d k : nat) H_lt, *)
  (*   (* forall (Score : Simulator d k), *) *)
  (*   forall (LA : {fset Location}) (A : raw_package), *)
  (*     ValidPackage LA (KS_interface d k) A_export A → *)
  (*     (AdvantageE (G_core_R_esalt d k H_lt) (G_core d k true H_lt) A *)
  (*      >= maxR (fun i => AdvantageE (G_core_Hash d k H_lt) (G_core_D d k H_lt) (Ai A i)))%R. *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)

  Lemma d4 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_R_esalt d k H_lt) (G_core d k true H_lt) A
       <= maxR (fun i => AdvantageE (G_core_D d k H_lt) (G_core d k true H_lt) (Ai A i)))%R.
  Proof.
    intros.
  Admitted.

  Lemma d5 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_R_esalt d k H_lt) (G_core_SODH d k H_lt) A
       = Advantage (Gsodh d k H_lt) (A ∘ R_sodh))%R.
  Proof.
    intros.
  Admitted.

  Fixpoint idealization_loop (fuel : nat) (ioc : list name) {struct fuel} : list (list name) :=
    match fuel with
    | O => []
    | S fuel =>
        if ioc != all_names
        then
          match (filter (fun n => (n \notin ioc) && (let (n1, n2) := PrntN n in ((nfto n1 \in ioc) || (nfto n1 == BOT)) && ((nfto n2 \in ioc) || (nfto n2 == BOT)) && (all (fun sn => sn \notin ioc) (SblngN n)))) all_names) with
          | [] => []
          | (n_c :: xs) =>
              [ioc ++ SblngN n_c] ++ idealization_loop fuel (ioc ++ SblngN n_c)
          end
        else []
    end.

  Lemma idealization_order_one_iter :
    forall fuel ioc,
      idealization_loop fuel.+1 ioc =
        (if ioc != all_names
         then
           match (filter (fun n => (n \notin ioc) && (let (n1, n2) := PrntN n in ((nfto n1 \in ioc) || (nfto n1 == BOT)) && ((nfto n2 \in ioc) || (nfto n2 == BOT)) && (all (fun sn => sn \notin ioc) (SblngN n)))) all_names) with
           | [] => []
           | (n_c :: xs) =>
               let snc := SblngN n_c in
               [ioc ++ snc] ++ idealization_loop fuel (ioc ++ snc)
           end
         else []).
  Proof. reflexivity. Qed.

  Lemma filter_cons : forall {A} f (a : A) x,
      filter f (a :: x) =
        if (f a)
        then a :: filter f x
        else filter f x.
  Proof. reflexivity. Qed.

  Definition IdealizationOrder :=
    let ioc0 := [PSK; ZERO_SALT; DH; ZERO_IKM] in
    let fuel := List.length all_names in
    ([::] :: [ioc0] ++ idealization_loop fuel ioc0).

  Definition IdealizationOrderPreCompute :=
    [:: [::];
     [:: PSK; ZERO_SALT; DH; ZERO_IKM];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT; BINDER];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT; BINDER; HS];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT; BINDER; HS; SHT; CHT; HSALT];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT; BINDER; HS; SHT; CHT; HSALT; AS];
       [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES; EEM; CET; BIND; ESALT; BINDER; HS; SHT; CHT; HSALT; AS; RM; CAT; SAT; EAM]].

  Definition smpl_PrntN (n : name) : name * name :=
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
    in (a,b).

  Lemma PrntN_project_to_smpl_PrntN
    : (forall n, nfto (PrntN n).1 = (smpl_PrntN n).1 /\ nfto (PrntN n).2 = (smpl_PrntN n).2).
        {
          intros.
          unfold PrntN.
          destruct n.
          all: now rewrite !nfto_name_to_chName_cancel.
        }
  Qed.

  (* Lemma filter_slow : *)
  (*   let ioc := [:: PSK; ZERO_SALT; DH; ZERO_IKM] in *)
  (*   [:: ES] = filter (fun n => (n \notin ioc) && (let (n1, n2) := PrntN n in ((nfto n1 \in ioc) || (nfto n1 == BOT)) && ((nfto n2 \in ioc) || (nfto n2 == BOT)) && (all (fun sn => sn \notin ioc) (SblngN n)))) all_names. *)
  (*   intros. *)
  (*   unfold SblngN. *)
  (*   unfold PrntN. *)
  (*   unfold all_names. *)
  (*   unfold filter. *)
  (* Admitted. *)

  (* Lemma idealization_order_0 : *)
  (*   forall n, *)
  (*     idealization_loop n.+1 [:: PSK; ZERO_SALT; DH; ZERO_IKM] = *)
  (*       [[:: PSK; ZERO_SALT; DH; ZERO_IKM; ES]] ++ *)
  (*     idealization_loop n [:: PSK; ZERO_SALT; DH; ZERO_IKM; ES]. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite idealization_order_one_iter. *)
  (*   unfold PrntN. *)
  (*   unfold last ; simpl (_ != _) ; hnf ; unfold all_names. *)

  (*   replace (filter _ _) with [ES]. *)
  (*   2:{ *)
  (*     repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf). *)

  (*     unfold all ; *)
  (*       simpl (if _ then _ else _) ; *)
  (*       hnf ; *)
  (*       unfold SblngN ; *)
  (*       unfold all_names ; *)

  (*       repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf). *)

  (*     rewrite eqxx. *)
  (*     simpl. *)
  (*     reflexivity. *)
  (*   } *)
  (*   Show Proof. *)
  (* Time Qed. *)

  Lemma compute_eq : (IdealizationOrder = IdealizationOrderPreCompute).
  Proof.
    unfold IdealizationOrder.
    unfold IdealizationOrderPreCompute.
    repeat (rewrite idealization_order_one_iter ;
      unfold last ; simpl (_ != _) ; hnf ;
      unfold all_names ;

      repeat (rewrite filter_cons ; simpl (_ && _) ; try rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf) ; unfold filter ;

      unfold SblngN at 1 ;
      unfold all_names ;

      repeat (rewrite filter_cons ; simpl (_ && _) ; try rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf) ; unfold filter ;
      rewrite eqxx ;

      unfold all ;
      simpl (if _ then _ else _) ;
      hnf ;
      unfold SblngN ;
      unfold all_names ;
      repeat (rewrite filter_cons ; simpl (_ && _) ; try rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf) ; unfold filter ;
      rewrite eqxx ;

      simpl cat).

    do 1 (rewrite idealization_order_one_iter ;
      unfold last ; simpl (_ != _) ; hnf ;
      unfold all_names ;

          repeat (rewrite filter_cons ; simpl (_ && _) ; try rewrite !nfto_name_to_chName_cancel ; simpl (_ && _) ; hnf) ; unfold filter).

    simpl.
    reflexivity.

    Unshelve.
    (* Grab Existential Variables. *)
    Fail idtac.
    all: fail.
  Admitted. (* Time Qed. *)

  (* Show Match name. *)

  Lemma d10_helper : forall j,
    (j.+1 <= List.length IdealizationOrderPreCompute)%nat ->
    forall x,
      x \in nth all_names IdealizationOrderPreCompute j ->
      x \in nth all_names IdealizationOrderPreCompute j.+1.
  Proof.
    intros.
    unfold IdealizationOrderPreCompute in H |- *.
    do 9 (destruct j ; [ simpl in H0 |- *;  rewrite !in_cons in H0 |- * ; repeat move /orP: H0 => [ /eqP ? | H0 ] ; [ subst .. | discriminate ] ; easy | ]).
    discriminate.
  Qed.

  Lemma d10 : forall i j,
      (i < j)%nat ->
      (j <= List.length IdealizationOrderPreCompute)%nat ->
    forall x,
      x \in nth all_names IdealizationOrderPreCompute i ->
      x \in nth all_names IdealizationOrderPreCompute j.
  Proof.
    intros.
    induction j.
    - destruct i ; [ | discriminate ].
      apply H1.
    - destruct (i == j) eqn:i_is_j.
      2: now apply d10_helper, IHj.
      {
        clear H IHj.
        move /eqP: i_is_j => i_is_j.
        subst.
        now apply d10_helper.
      }
  Qed.

  Lemma d11 :
    forall d k H_lt ℓ c A,
      ((c == O)%nat || (PSK \notin nth [] IdealizationOrderPreCompute c.-1)) ->
      PSK \in nth [] IdealizationOrderPreCompute c ->
      (AdvantageE
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c))
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c.+1))
        A
      <=
        Advantage (Gxtr d k H_lt ES ℓ) (A ∘ R_xtr ES ℓ erefl))%R.
  Proof.
    intros.


  Admitted.

  Lemma d12 :
    forall d k H_lt ℓ c A,
      ((c == O)%nat || (ESALT \notin nth [] IdealizationOrderPreCompute c.-1)) ->
      ESALT \in nth [] IdealizationOrderPreCompute c ->
      (AdvantageE
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c))
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c.+1))
        A
      <=
        Advantage (Gxtr d k H_lt HS ℓ) (A ∘ R_xtr HS ℓ erefl))%R.
  Proof.
    intros.
  Admitted.

  Lemma d13 :
    forall d k H_lt ℓ c A,
      ((c == O)%nat || (HSALT \notin nth [] IdealizationOrderPreCompute c.-1)) ->
      HSALT \in nth [] IdealizationOrderPreCompute c ->
      (AdvantageE
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c))
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c.+1))
        A
      <=
        Advantage (Gxtr d k H_lt AS ℓ) (A ∘ R_xtr AS ℓ erefl))%R.
  Proof.
    intros.
  Admitted.

  Lemma d14 :
    forall d k H_lt ℓ c A n (_ : ChldrOp (nfto (fst (PrntN n))) = xpd_op) (H_in_xpr : n \in XPR) (* (H_notin : n \notin [PSK; ESALT]) *),
      ((nfto (fst (PrntN n))) \notin nth [] IdealizationOrderPreCompute c.-1) ->
      ((c == O) || ((nfto (fst (PrntN n))) \in nth [] IdealizationOrderPreCompute c.+1)) ->
      (AdvantageE
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c))
        (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute c.+1))
        A
      <=
        Advantage (Gxpd d k H_lt n ℓ) (A ∘ R_xpd d k H_lt n ℓ H_in_xpr))%R.
  Proof.
    intros.

    unfold G_core_hyb_pred_ℓ_c.
    unfold G_core_package_construction.
    unfold pack.

    unfold IdealizationOrderPreCompute.
    unfold G_core_hyb_pred_ℓ_c.
    unfold G_core_package_construction.
    unfold pack.

    simpl in H0.

    move /orP: H1 => [ /eqP ? | H1 ] ; subst.
    - unfold nth.
      rewrite <- !Advantage_link.
      rewrite Advantage_E.

      eassert (
          forall (P : seq ExtraTypes.name) (Q : seq ExtraTypes.name) (Z : seq ExtraTypes.name)
            (H_uniq : uniq (P ++ Q))
            (H_uniq_P : uniq P)
            (H_uniq_Q : uniq Q)
            A,
            AdvantageE
              (KeysAndHash d k H_lt (λ (ℓ0 : nat) (name : ExtraTypes.name),
                   if (name \in N_star) || (name == PSK)
                   then if (ℓ + (name \in Z) <=? ℓ0)%N then false else true
                   else false) (λ name : ExtraTypes.name, match name with
                                                          | ESALT => R
                                                          | _ => D
                                                          end) (P ++ Q) H_uniq)
              (par
                 (KeysAndHash d k H_lt (λ (ℓ0 : nat) (name : ExtraTypes.name),
                      if (name \in N_star) || (name == PSK)
                      then if (ℓ + (name \in Z) <=? ℓ0)%N then false else true
                      else false) (λ name : ExtraTypes.name, match name with
                                                             | ESALT => R
                                                             | _ => D
                                                             end) P H_uniq_P)
                 (KeysAndHash d k H_lt (λ (ℓ0 : nat) (name : ExtraTypes.name),
                      if (name \in N_star) || (name == PSK)
                      then if (ℓ + (name \in [::]) <=? ℓ0)%N then false else true
                      else false) (λ name : ExtraTypes.name, match name with
                                                             | ESALT => R
                                                             | _ => D
                                                             end) Q H_uniq_Q)
                 )
              A = 0)%R.
      1: admit.

      eassert (
          forall (A : seq ExtraTypes.name) (B : seq ExtraTypes.name) P
            (H_eq : forall x, x \in A <-> x \in B)
            (H_uniq_A : uniq A)
            (H_uniq_B : uniq B)
            Adv,
            AdvantageE
              (KeysAndHash d k H_lt (λ (ℓ0 : nat) (name : ExtraTypes.name),
                   if (name \in N_star) || (name == PSK)
                   then if (ℓ + (name \in P) <=? ℓ0)%N then false else true
                   else false) (λ name : ExtraTypes.name, match name with
                                                          | ESALT => R
                                                          | _ => D
                                                          end) A H_uniq_A)
              (KeysAndHash d k H_lt (λ (ℓ0 : nat) (name : ExtraTypes.name),
                      if (name \in N_star) || (name == PSK)
                      then if (ℓ + (name \in P) <=? ℓ0)%N then false else true
                      else false) (λ name : ExtraTypes.name, match name with
                                                             | ESALT => R
                                                             | _ => D
                                                             end) B H_uniq_B)
              Adv = 0)%R.
      1:{
        clear. intros.
        unfold KeysAndHash.
        unfold pack.
        admit.
      }

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (1 := (KeysAndHash d k H_lt
        (λ (ℓ0 : nat) (name : ExtraTypes.name),
           if (name \in N_star) || (name == PSK)
           then if (ℓ + (name \in []) <=? ℓ0)%N then false else true
           else false) (λ name : ExtraTypes.name, match name with
                                                  | ESALT => R
                                                  | _ => D
                                                  end) ([:: PSK; ZERO_SALT; DH; ZERO_IKM] ++ [ES; EEM; CET; BIND; BINDER; HS; SHT; CHT; HSALT; AS; RM; CAT; SAT; EAM; ESALT]) erefl)).

      rewrite H2.
      2: clear ; split ; intros ; rewrite !in_cons in H ; repeat move: H => /orP [ /eqP ? | H ] ; [ subst ; easy .. | discriminate ].
      rewrite add0r.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      eapply Order.le_trans.
      1:{
        apply Num.Theory.lerD ; [ | easy ].
        erewrite H1.
        now apply eq_ler.
      }
      rewrite add0r.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (1 := (KeysAndHash d k H_lt
        (λ (ℓ0 : nat) (name : ExtraTypes.name),
           if (name \in N_star) || (name == PSK)
           then if (ℓ + (name \in [:: PSK; ZERO_SALT; DH; ZERO_IKM]) <=? ℓ0)%N then false else true
           else false) (λ name : ExtraTypes.name, match name with
                                                  | ESALT => R
                                                  | _ => D
                                                  end) ([:: PSK; ZERO_SALT; DH; ZERO_IKM] ++ [ES; EEM; CET; BIND; BINDER; HS; SHT; CHT; HSALT; AS; RM; CAT; SAT; EAM; ESALT]) erefl)).

      rewrite H2.
      2: clear ; split ; intros ; rewrite !in_cons in H ; repeat move: H => /orP [ /eqP ? | H ] ; [ subst ; easy .. | discriminate ].

      rewrite addr0.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (1 := (KeysAndHash d k H_lt
        (λ (ℓ0 : nat) (name : ExtraTypes.name),
           if (name \in N_star) || (name == PSK)
           then if (ℓ + (name \in [:: PSK; ZERO_SALT; DH; ZERO_IKM]) <=? ℓ0)%N then false else true
           else false) (λ name : ExtraTypes.name, match name with
                                                  | ESALT => R
                                                  | _ => D
                                                  end) ([:: PSK; ZERO_SALT; DH; ZERO_IKM] ++ [ES; EEM; CET; BIND; BINDER; HS; SHT; CHT; HSALT; AS; RM; CAT; SAT; EAM; ESALT]) erefl)).

      rewrite H2.
      2: clear ; split ; intros ; rewrite !in_cons in H ; repeat move: H => /orP [ /eqP ? | H ] ; [ subst ; easy .. | discriminate ].

      rewrite addr0.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      eapply Order.le_trans.
      1:{
        apply Num.Theory.lerD ; [ easy | ].
        rewrite (Advantage_sym _ _).
        erewrite H1.
        now apply eq_ler.
      }
      rewrite addr0.
      erewrite (Advantage_parR ).
      2: admit.
      2: admit.
      2: admit.
      2: admit.
      2: admit.
      2: admit.
      2: admit.

      try timeout 5 rewrite advantage_reflexivity.
  Admitted.

  (* d6: Hybrid lemma *)
  (* Dependends on idealization order *)
  Lemma d6 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    (* forall i, *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      forall ℓ, (ℓ <= d)%nat ->
      (AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt ℓ.+1) A
       <= Advantage (Gxtr d k H_lt ES ℓ) (A ∘ R_xtr ES ℓ erefl) +
         Advantage (Gxtr d k H_lt HS ℓ) (A ∘ R_xtr HS ℓ erefl) +
         Advantage (Gxtr d k H_lt AS ℓ) (A ∘ R_xtr AS ℓ erefl) +
           sumR_l_in_rel XPR XPR (fun _ H => H) (fun n H_in => Advantage (Gxpd d k H_lt n ℓ) (A ∘ R_xpd d k H_lt n ℓ H_in))%R
      )%R.
  Proof.
    intros.

    eapply Order.le_trans.
    1:{
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := (G_core_hyb_pred_ℓ_c d k H_lt ℓ [])).

      apply Num.Theory.lerD.
      {
        instantiate (1 := 0%R).

        unfold G_core_hyb_ℓ.
        unfold G_core_hyb_pred_ℓ_c.

        replace
          (λ (ℓ0 : nat) (name : ExtraTypes.name),
            if (name \in N_star) || (name == PSK)
            then if (ℓ + _ <=? ℓ0)%N then false else true
            else false)
          with
          (λ (ℓ0 : nat) (name : ExtraTypes.name),
            if (name \in N_star) || (name == PSK)
            then if (ℓ <=? ℓ0)%nat then false else true
            else false).
        2:{
          apply functional_extensionality.
          intros.
          apply functional_extensionality.
          intros.
          replace (ℓ + (_ \in [::]))%nat with (ℓ + false)%nat by reflexivity.
          now rewrite addn0.
        }

        now rewrite advantage_reflexivity.
      }

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [] IdealizationOrderPreCompute (List.length IdealizationOrderPreCompute - 1)))).

      apply Num.Theory.lerD.
      2:{
        instantiate (1 := 0%R).

        unfold G_core_hyb_ℓ.
        unfold G_core_hyb_pred_ℓ_c.

        replace ((λ (ℓ0 : nat) (name : ExtraTypes.name),
           if (name \in N_star) || (name == PSK)
           then
            if
             (ℓ + _ <=? ℓ0)%nat
            then false
            else true
           else false))
          with
          (λ (ℓ0 : nat) (name : ExtraTypes.name),
            if (name \in N_star) || (name == PSK) then if (ℓ.+1 <=? ℓ0)%nat then false else true else false).
        2:{
          apply functional_extensionality.
          intros.
          apply functional_extensionality.
          intros.

          destruct ( _ || _ ) eqn:x0_or ; [ | reflexivity ].
          {
            rewrite !in_cons in x0_or.
            rewrite orbC in x0_or.
            unfold IdealizationOrderPreCompute.
            simpl.
            repeat move: x0_or => /orP [ /eqP ? | x0_or ] ; [ subst .. | discriminate ].
            all: now simpl ; rewrite addn1.
          }
        }

        now rewrite advantage_reflexivity.
      }

      easy.
    }

    rewrite add0r addr0.

    eapply Order.le_trans.
    1:{
      instantiate (1 :=
        sumR 0 (List.length (IdealizationOrderPreCompute) - 1)%nat _
          (fun c => AdvantageE
                   (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [::] (IdealizationOrderPreCompute) c))
                   (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [::] (IdealizationOrderPreCompute) c.+1))
                   A)).

      induction (Datatypes.length _).
      - unfold sumR.
        replace ( _ - _)%nat with O%nat by now cbn.
        simpl iota.
        unfold List.fold_left.
        unfold IdealizationOrderPreCompute.
        unfold nth.

        now rewrite advantage_reflexivity.
      - destruct n ; [ apply IHn | ].
        rewrite sumR_succ.
        eapply Order.le_trans ; [ apply Advantage_triangle | ].
        instantiate (1 := (G_core_hyb_pred_ℓ_c d k H_lt ℓ (nth [::] IdealizationOrderPreCompute n))).
        set (_ + _)%R at 2.
        rewrite addrC.
        subst s.

        apply Num.Theory.lerD ; [ easy | ].

        assert (n = n.+1 - 1)%nat by Lia.lia.
        rewrite H1.
        apply IHn.
    }

    unfold sumR.
    simpl iota.
    unfold List.fold_left.
    rewrite add0r.

    eapply Order.le_trans.
    {
      repeat apply Num.Theory.lerD.
      7:{
        refine (d13 d k H_lt ℓ 6 A _ erefl).
        apply /orP.
        right.
        easy.
      }
      4:{
        refine (d12 d k H_lt ℓ 3 A _ erefl).
        apply /orP.
        right.
        easy.
      }
      2:{
        refine (d11 d k H_lt ℓ 1 A _ erefl).
        apply /orP.
        right.
        easy.
      }
      {
        refine (d14 d k H_lt ℓ 0 A ESALT _ erefl _ _).
        {
          unfold ChldrOp. unfold ChldrN. unfold all_names.

          repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with false by easy).

          (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with true by easy ; hnf).

          unfold PrntOp.
          rewrite !nfto_name_to_chName_cancel.
          reflexivity.
        }
        1:{ unfold XPR. unfold XPR_sub_PSK. easy. }
        1: easy.
      }
      {
        refine (d14 d k H_lt ℓ 2 A EEM _ erefl _ _).
        1:{
          unfold ChldrOp. unfold ChldrN. unfold all_names.

          repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with false by easy).

          (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with true by easy ; hnf).

          unfold PrntOp.
          rewrite !nfto_name_to_chName_cancel.
          reflexivity.
        }
        2:{
          simpl.
          rewrite nfto_name_to_chName_cancel.
          easy.
        }
        {
          apply /orP.
          rewrite nfto_name_to_chName_cancel.
          easy.
        }
      }
      {
        refine (d14 d k H_lt ℓ 4 A SHT _ erefl _ _).
        1:{
          unfold ChldrOp. unfold ChldrN. unfold all_names.

          repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with false by easy).

          (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with true by easy ; hnf).

          unfold PrntOp.
          rewrite !nfto_name_to_chName_cancel.
          reflexivity.
        }
        2:{
          simpl.
          rewrite nfto_name_to_chName_cancel.
          easy.
        }
        {
          apply /orP.
          rewrite nfto_name_to_chName_cancel.
          simpl.
          easy.
        }
      }
      {
        refine (d14 d k H_lt ℓ 5 A CHT _ erefl _ _).
        1:{
          unfold ChldrOp. unfold ChldrN. unfold all_names.

          repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with false by easy).

          (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with true by easy ; hnf).

          unfold PrntOp.
          rewrite !nfto_name_to_chName_cancel.
          reflexivity.
        }
        2:{
          simpl.
          rewrite nfto_name_to_chName_cancel.
          easy.
        }
        {
          apply /orP.
          rewrite nfto_name_to_chName_cancel.
          simpl.
          easy.
        }
      }
      {
        refine (d14 d k H_lt ℓ 7 A RM _ erefl _ _).
        1:{
          unfold ChldrOp. unfold ChldrN. unfold all_names.

          repeat (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with false by easy).

          (rewrite filter_cons ; rewrite !nfto_name_to_chName_cancel ; simpl (( _ == _) || (_ == _)) ; replace (_ == _) with true by easy ; hnf).

          unfold PrntOp.
          rewrite !nfto_name_to_chName_cancel.
          reflexivity.
        }
        2:{
          simpl.
          rewrite nfto_name_to_chName_cancel.
          easy.
        }
        {
          apply /orP.
          rewrite nfto_name_to_chName_cancel.
          simpl.
          easy.
        }
      }
    }

    unfold XPR, XPR_sub_PSK.
    unfold sumR_l_in_rel ; fold @sumR_l_in_rel.
    simpl ([:: ESALT] ++ _).
    unfold sumR_l_in_rel ; fold @sumR_l_in_rel.

    replace (mem_tail _ _ _) with (erefl : ESALT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : EEM \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : CET \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : BIND \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : BINDER \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : SHT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : CHT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : HSALT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : RM \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : CAT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : SAT \in XPR) by easy.
    replace (mem_tail _ _ _) with (erefl : EAM \in XPR) by easy.

    rewrite <- !addrA.
    rewrite addrC.
    rewrite <- !addrA.

    apply Num.Theory.lerD ; [ easy | ].

    rewrite addrC.
    rewrite <- !addrA.

    apply Num.Theory.lerD ; [ easy | ].

    rewrite addrC.
    rewrite <- !addrA.

    rewrite addrC.
    rewrite <- !addrA.

    apply Num.Theory.lerD ; [ easy | ].

    rewrite <- addrC.
    rewrite <- !addrA.

    now repeat ((apply Num.Theory.ler_wpDr ; [ | easy ]) || (apply Num.Theory.lerD ; [ easy | ]) || (apply Num.Theory.ler_wpDl ; [ apply Num.Theory.normr_ge0 | ])).
  Qed.

  Lemma hyb_telescope :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_hyb_ℓ d k H_lt 0) (G_core_hyb_ℓ d k H_lt d) (Ai A i)
       <= sumR 0 d (leq0n d) (fun ℓ => AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt (ℓ+1)) (Ai A i))
      )%R.
  Proof.
    intros.

    set d in H, H_lt |- * at 1 2 6 7.
    generalize dependent n.
    generalize dependent (leq0n d).
    induction d ; intros.
    - unfold sumR.
      (* simpl. *)
      simpl iota.
      unfold AdvantageE.
      unfold List.fold_left.
      rewrite subrr.

      apply eq_ler.
      rewrite Num.Theory.normr0.
      reflexivity.


      (* rewrite add0r. *)
      (* rewrite add0n. *)
    (* now apply eq_ler. *)

      (* reflexivity. *)
    (* rewrite subrr. *)
    (* rewrite Num.Theory.normr0. *)
    (* reflexivity. *)

    -

      rewrite sumR_succ.

      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (1 := (G_core_hyb_ℓ n k H_lt d)).

      eapply Order.le_trans.
      1:{
        apply Num.Theory.lerD ; [ | easy ].
        eapply (IHd _ _ H_lt).
        apply H.
      }

      rewrite addrC.
      apply Num.Theory.lerD ; [ | easy ].
      rewrite addn1.
      easy.
  Qed.

  Lemma equation20_lhs :
    forall (d k : nat) H_lt,
      (d > 0)%nat ->
    (* forall (Score : Simulator d k), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_SODH d k H_lt) (G_core_hyb_ℓ d k H_lt 0) (Ai A i) = 0)%R.
  Proof.
    intros.

    unfold G_core_SODH.
    unfold G_core_hyb_ℓ.

    replace (λ (ℓ : nat) (name : ExtraTypes.name),
              if (name \in N_star) || (name == PSK) then if (0 <=? ℓ)%N then false else true else false) with (λ (_ : nat) (_ : name), false).
    2:{
      apply functional_extensionality.
      intros.
      apply functional_extensionality.
      intros.
      destruct (_ || _) ; [ | reflexivity ].
      now destruct x.
    }

    apply advantage_reflexivity.
  Qed.

  Lemma L_package_esalt_D_to_R :
    forall k A,
    AdvantageE
      (Ls k all_names (λ _ : name, D) erefl)
      (Ls k all_names
         (λ name : ExtraTypes.name,
             match name as name' return (name' = name → ZAF) with
             | BOT => λ _ : BOT = name, D
             | ES => λ _ : ES = name, D
             | EEM => λ _ : EEM = name, D
             | CET => λ _ : CET = name, D
             | BIND => λ _ : BIND = name, D
             | BINDER => λ _ : BINDER = name, D
             | HS => λ _ : HS = name, D
             | SHT => λ _ : SHT = name, D
             | CHT => λ _ : CHT = name, D
             | HSALT => λ _ : HSALT = name, D
             | AS => λ _ : AS = name, D
             | RM => λ _ : RM = name, D
             | CAT => λ _ : CAT = name, D
             | SAT => λ _ : SAT = name, D
             | EAM => λ _ : EAM = name, D
             | PSK => λ _ : PSK = name, D
             | ZERO_SALT => λ _ : ZERO_SALT = name, D
             | ESALT => λ _ : ESALT = name, R
             | DH => λ _ : DH = name, D
             | ZERO_IKM => λ _ : ZERO_IKM = name, D
             end erefl) erefl) A = 0%R.
  Proof.
    intros.
    unfold Ls.
    unfold all_names.
    unfold interface_foreach.
    unfold eq_rect_r.
    unfold eq_rect.
    destruct Logic.eq_sym.
    unfold parallel_package.
    unfold List.map.
    unfold parallel_raw.
    unfold List.fold_left.
    unfold pack.

    repeat (erewrite (Advantage_parR ) ; [ | admit.. ]).
    repeat (erewrite (Advantage_par ) ; [ | admit.. ]).

    eapply eq_rel_perf_ind_eq.
    1,2: apply pack_valid.
    2: admit.
    2,3: admit.

    unfold eq_up_to_inv.
    intros.

    rewrite in_fset in H.
    rewrite mem_seq1 in H.
    move/eqP: H => H ; inversion_clear H.

    unfold get_op_default.

    unfold L_package.
    unfold pack.

    (* lookup_op_squeeze. *)

    unfold lookup_op.
    rewrite !mkfmapE.
    unfold getm_def.
    unfold ".1", ".2".
    rewrite !eqxx.

    unfold mkdef.

    destruct choice_type_eqP.
    2: apply r_ret ; easy.

    destruct choice_type_eqP.
    2: apply r_ret ; easy.

    subst.
    rewrite !cast_fun_K.

    destruct x as [[]].

    eapply r_bind.
    2:{
      intros.
      instantiate (1 := fun '(_, s₀) '(_, s₁) => s₀ = s₁).
      hnf.
      unfold set_at.
      unfold bind.
      ssprove_sync_eq.
      now apply r_ret.
    }

    admit.
  Admitted.

  Lemma D_to_R_esalt_is_zero :
    forall d k H_lt A,
      AdvantageE (G_core_D d k H_lt) (G_core_R_esalt d k H_lt) A = 0%R.
  Proof.
    intros.

    unfold G_core_D.
    unfold G_core_R_esalt.
    unfold G_core_package_construction.

    unfold pack.
    rewrite <- !Advantage_link.

    setoid_rewrite (Advantage_parR (Hash true)).
    2: apply pack_valid.
    2,3,4,5,6,7: admit.

    (* erewrite <- interchange. *)
    (* 2,3,4,5,6,7,8: admit. *)

    erewrite (Advantage_parR ).
    2,3,4,5,6,7,8: admit.

    rewrite <- !Advantage_link.
    (* apply L_package_esalt_D_to_R. *)
  Admitted.

  Lemma equation20_rhs :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_ki d k H_lt) (G_core_hyb_ℓ d k H_lt d) (Ai A i) = 0)%R.
  Proof.
    intros.

    unfold G_core_ki.
    unfold G_core_hyb_ℓ.
    unfold G_core_package_construction.

    unfold pack.
    rewrite <- !Advantage_link.

    (* rewrite <- (par_commut (Hash true)). *)
    (* 2: admit. *)

    (* rewrite <- (par_commut (Hash true)). *)
    (* 2: admit. *)

    (* setoid_rewrite (Advantage_par (Hash true)). *)
    (* 2,3,4,5,6,7,8: admit. *)

    (* rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)). *)
    (* 2: admit. *)

    (* rewrite <- (par_commut (K_package k PSK _ _ _ ∘ _)). *)
    (* 2: admit. *)

    (* rewrite eqxx. *)

    (* setoid_rewrite (Advantage_par (K_package k PSK _ _ _ ∘ _)). *)
    (* 2,3,4,5,6,7,8: admit. *)

    replace (λ (ℓ : nat) (name : ExtraTypes.name),
              if (name \in N_star) || (name == PSK) then if ℓ >=? d then false else true else false)
      with
      (λ (ℓ : nat) (name : ExtraTypes.name), true).
    2:{
      admit.
    }

    (* erewrite (Advantage_par ). *)
    (* 2,3,4,5,6,7,8: admit. *)

    (* erewrite <- interchange. *)
    (* 2,3,4,5,6,7,8: admit. *)

    (* rewrite <- !Advantage_link. *)

    (* apply L_package_esalt_D_to_R. *)
  Admitted.

  Lemma equation20_eq :
    forall (d k : nat) H_lt,
      (d > 0)%nat ->
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_SODH d k H_lt) (G_core d k true H_lt) (Ai A i)
       <= AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)
         +sumR 0 d (leq0n d) (fun ℓ => AdvantageE (G_core_hyb_ℓ d k H_lt ℓ) (G_core_hyb_ℓ d k H_lt (ℓ + 1)) (Ai A i))
      )%R.
  Proof.
    intros.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (G_core_hyb_ℓ d k H_lt 0)).
    rewrite (equation20_lhs d k H_lt).
    2: easy.
    rewrite add0r.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := G_core_ki d k H_lt).
    rewrite <- (addrC (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)))%R.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    instantiate (1 := (G_core_hyb_ℓ d k H_lt d)).

    epose (e := equation20_rhs d k (* Score *)).
    setoid_rewrite (Advantage_sym _ _) in e.

    rewrite e ; clear e.
    rewrite addr0.

    eapply hyb_telescope.
    apply H0.
  Qed.


  Lemma d7 :
    forall (d k : nat) H_lt,
    (* forall (Score : Simulator d k), *)
    (* forall (K_table : chHandle -> nat), *)
    forall i,
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i)
       <= Advantage (λ x : bool, Gpi d k H_lt [:: ESALT] R x) (Ai A i ∘ R_pi [:: ESALT]) +
   Advantage (λ x : bool, Gpi d k H_lt O_star R x) (Ai A i ∘ R_pi O_star)
      )%R.
  Proof.
    intros.
  Admitted.

  Axiom sumR_leq : forall l u H_range f g,
      (forall ℓ, (ℓ <= u)%nat -> f ℓ <= g ℓ)%R ->
      (sumR l u H_range f <= sumR l u H_range g)%R.

  Lemma core_theorem :
    forall (d k : nat) H_lt (H_gt : (0 < d)%nat),
    (* forall (Score : Simulator d k), *)
    forall (LA : {fset Location}) (A : raw_package),
      ValidPackage LA (KS_interface d k) A_export A →
      (forall i, ValidPackage LA (KS_interface d k) A_export (Ai A i)) →
      (AdvantageE
         (G_core d k false H_lt)
         (G_core d k true H_lt) (A (* ∘ R d M H *))
       <= sumR_l [(R_cr, f_hash); (R_Z f_xtr, f_xtr); (R_Z f_xpd, f_xpd); (R_D f_xtr, f_xtr); (R_D f_xpd, f_xpd)] (fun R_hash_fn => Advantage (Gacr (snd R_hash_fn)) (A ∘ (fst R_hash_fn)))
         +maxR (fun i =>
                  Advantage (Gsodh d k H_lt) (Ai A i ∘ R_sodh) +
                    Advantage (Gpi d k H_lt [ESALT] R) (Ai A i ∘ R_pi [ESALT]) +
                    Advantage (Gpi d k H_lt O_star R) (Ai A i ∘ R_pi O_star) +
                    sumR 0 d (leq0n d) (fun ℓ =>
                                          Advantage (Gxtr d k H_lt ES ℓ) (Ai A i ∘ R_xtr ES ℓ erefl) +
                                          Advantage (Gxtr d k H_lt HS ℓ) (Ai A i ∘ R_xtr HS ℓ erefl) +
                                          Advantage (Gxtr d k H_lt AS ℓ) (Ai A i ∘ R_xtr AS ℓ erefl) +
                                            sumR_l_in_rel XPR XPR (fun _ H => H) (fun n H_in => Advantage (Gxpd d k H_lt n ℓ) (Ai A i ∘ R_xpd d k H_lt n ℓ H_in))%R)
      ))%R.
  Proof.
    intros.
    unfold sumR_l.
    rewrite addr0.
    rewrite addrA.

    eapply Order.le_trans ; [ eapply d2 ; apply H | ].

    eapply Order.le_trans.
    1:{
      apply Num.Theory.lerD ; [ easy | ].
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      apply Num.Theory.lerD ; [ | easy ].
      eapply d3, H.
    }
    rewrite !addrA.
    apply Num.Theory.lerD ; [ easy | ].

    eapply Order.le_trans.
    1:{
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := G_core_R_esalt d k H_lt).
      rewrite D_to_R_esalt_is_zero.
      rewrite add0r.
      eapply d4, H.
    }

    apply max_leq.
    intros i.

    eapply Order.le_trans ; [ apply Advantage_triangle | ].
    eapply Order.le_trans.
    1:{
      instantiate (2 := (G_core_SODH d k H_lt)).
      apply Num.Theory.lerD ; [ | easy ].
      eapply Order.le_trans ; [ apply Advantage_triangle | ].
      instantiate (2 := (G_core_R_esalt d k H_lt)).
      apply Num.Theory.lerD ; [ easy | ].
      (* erewrite D_to_R_esalt_is_zero. *)
      (* rewrite add0r. *)
      erewrite d5 ; [ | apply H0 ].
      easy.
    }
    rewrite <- (addrC (Advantage (λ x : bool, Gsodh d k H_lt x) (Ai A i ∘ R_sodh))).
    rewrite <- !addrA.
    apply Num.Theory.lerD ; [ easy | ].
    rewrite addrA.

    eapply Order.le_trans.
    1:{
      apply Num.Theory.lerD ; [ easy | ].
      eapply Order.le_trans.
      1: eapply equation20_eq, H ; apply H_gt.

      apply Num.Theory.lerD ; [ easy | ].
      apply sumR_leq.
      intros.
      rewrite addn1.
      eapply d6 ; [ apply H0 | ].
      apply H1.
    }

    rewrite addrA.
    rewrite <- (addrC (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i))).
    rewrite <- (addrA (AdvantageE (G_core_ki d k H_lt) (G_core d k true H_lt) (Ai A i))).
    apply Num.Theory.lerD.
    1:{
      eapply Order.le_trans.
      1: eapply d7, H.
      easy.
    }

    rewrite D_to_R_esalt_is_zero.
    rewrite add0r.
    easy.
  Qed.

End CoreTheorem.

(* Why does this work with d = 0? *)
