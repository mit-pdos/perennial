From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import grove_prelude.
From New.proof Require Import sync.
From New.proof Require Import proofmode.
From Ltac2 Require Import Ltac2.

Set Default Proof Mode "Classic".
Section instances.

Context `{!heapGS Σ}.
Local Instance pure_exec_pure_wp {φ n e e'} :
  PureExec φ (S n) e e' → PureWp φ e e'.
Proof.
  intros.
  intros ?????.
  iIntros "Hk".
  wp_pures. iFrame.
Qed.

(* Found via [Search PureExec.] *)
Definition pure_wp_injlc v := pure_exec_pure_wp (pure_injlc  v).
Definition pure_wp_injrc v := pure_exec_pure_wp (pure_injrc  v).
Definition pure_wp_fst v1 v2 := pure_exec_pure_wp (pure_fst  v1 v2).
Definition pure_wp_snd v1 v2 := pure_exec_pure_wp (pure_snd  v1 v2).
Definition pure_wp_recc f x erec := pure_exec_pure_wp (pure_recc  f x erec).
Definition pure_wp_pairc v1 v2 := pure_exec_pure_wp (pure_pairc  v1 v2).
Definition pure_wp_if_true e1 e2 := pure_exec_pure_wp (pure_if_true  e1 e2).
Definition pure_wp_if_false e1 e2 := pure_exec_pure_wp (pure_if_false  e1 e2).
Definition pure_wp_case_inl v e1 e2 := pure_exec_pure_wp (pure_case_inl  v e1 e2).
Definition pure_wp_case_inr v e1 e2:= pure_exec_pure_wp (pure_case_inr  v e1 e2).
Definition pure_wp_total_le v1 v2:= pure_exec_pure_wp (pure_total_le  v1 v2).
Definition pure_wp_unop op v v':= pure_exec_pure_wp (pure_unop op v v').
Definition pure_wp_binop op v1 v2 v' := pure_exec_pure_wp (pure_binop op v1 v2 v').
Definition pure_wp_eqop v1 v2 := pure_exec_pure_wp (pure_eqop  v1 v2).
Definition pure_wp_eqop_lit l1 l2 := pure_exec_pure_wp (pure_eqop_lit  l1 l2 ).
Definition pure_wp_beta f x erec v1 v2 {H:AsRecV v1 f x erec} := pure_exec_pure_wp (pure_beta f x erec v1 v2 (AsRecV0:=H)).

Global Existing Instance pure_wp_injlc.
Global Existing Instance pure_wp_injrc.
Global Existing Instance pure_wp_fst.
Global Existing Instance pure_wp_snd.
Global Existing Instance pure_wp_recc.
Global Existing Instance pure_wp_pairc.
Global Existing Instance pure_wp_if_true.
Global Existing Instance pure_wp_if_false.
Global Existing Instance pure_wp_case_inl.
Global Existing Instance pure_wp_case_inr.
Global Existing Instance pure_wp_total_le.
Global Existing Instance pure_wp_unop.
Global Existing Instance pure_wp_binop.
Global Existing Instance pure_wp_eqop.
Global Existing Instance pure_wp_eqop_lit.
Global Existing Instance pure_wp_beta.

End instances.

Section proof.

Context `{!heapGS Σ}.

Lemma wp_newNetworkWithConfigInit (peers : list val) peers_sl :
  {{{
        own_slice peers_sl stateMachine (DfracOwn 1) peers
  }}}
    newNetworkWithConfigInit go_nil (slice.val peers_sl)
  {{{
        (nw : loc), RET #nw; True
  }}}
.
Proof.
Admitted.

Lemma wp_entsWithConfig terms_sl terms :
  {{{
        own_slice terms_sl uint64T (DfracOwn 1) terms
  }}}
    entsWithConfig go_nil (slice.val terms_sl)
  {{{ (r : loc), RET #r; True }}}
.
Proof.
Admitted.

Ltac2 mutable dbg := Message.print.
Ltac2 mutable dbg_constr c := Message.print (Message.of_constr c).
Ltac2 subst_step x v e : constr :=
  lazy_match! x with
  | BAnon => e
  | BNamed ?x' =>
      let rec go_subst e : constr :=
        lazy_match! e with
        | @Val grove_op _ => e
        | Var ?x'' => if (Constr.equal x'' x') then '(Val $v) else e
        | Rec ?f ?x'' ?e' =>
            if Bool.or (Constr.equal x'' x) (Constr.equal f x) then e
            else let e' := go_subst e' in '(Rec $f $x'' $e')
        | App ?e1 ?e2 => let e1 := go_subst e1 in
                        let e2 := go_subst e2 in
                        '(App $e1 $e2)
        | UnOp ?op ?e =>
            let e := go_subst e in
            '(UnOp $op $e)
        | BinOp ?op ?e1 ?e2 =>
            let e1 := go_subst e1 in
            let e2 := go_subst e2 in
            '(BinOp $op $e1 $e2)
        | Pair ?e1 ?e2 =>
            let e1 := go_subst e1 in
            let e2 := go_subst e2 in
            '(Pair $e1 $e2)
        | Fst ?e =>
            let e := go_subst e in
            '(Fst $e)
        | Snd ?e =>
            let e := go_subst e in
            '(Snd $e)
        | If ?e1 ?e2 ?e3 =>
            let e1 := go_subst e1 in
            let e2 := go_subst e2 in
            let e3 := go_subst e3 in
            '(If $e1 $e2 $e3)
        | subst' ?x' ?v' ?e' =>
            if (Constr.equal x' x) then e
            else let e' := go_subst e' in
                 '(subst' $x' $v' $e')
        | _ => constr:(subst' $x $v $e)
                       (* | _ => Control.throw (Tactic_failure None) *)
        end in
      go_subst e
  end.

Ltac2 simplify_subst' () :=
  match! goal with
  | [ |- context k [subst' ?x ?v ?e] ] =>
      let g := (Pattern.instantiate k (subst_step x v e)) in
      change $g
  end.

Ltac wp_finish :=
  reduction.pm_prettify;        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                                  λs caused by wp_value *)
  ltac2:(repeat (simplify_subst' ())); simpl fill;
  try wp_value_head.  (* in case we have reached a value, get rid of the WP *)

  Lemma tac_wp_load_ty Δ s E i l q t v Φ is_pers :
    envs_lookup i Δ = Some (is_pers, typed_pointsto l q t v)%I →
    envs_entails Δ (WP (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof. Admitted.

  Lemma tac_wp_store_ty Δ Δ' stk E i l t v v' Φ :
    has_go_type v' t ->
    envs_lookup i Δ = Some (false, l ↦[t] v)%I →
    envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ = Some Δ' →
    envs_entails Δ' (WP (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
    envs_entails Δ (WP (store_ty t (LitV l) v') @ stk; E {{ Φ }}).
  Proof. Admitted.

  Lemma tac_wp_ref_ty name Δ stk E t v Φ :
    has_go_type v t ->
    (∀ (l : loc), envs_entails (envs_snoc Δ false (INamed name) (l ↦[t] v)%I) (WP (Val #l) @ stk; E {{ Φ }})) →
    envs_entails Δ (WP (ref_ty t v) @ stk; E {{ Φ }}).
  Proof. Admitted.

  Lemma tac_wp_ref_ty_anon Δ stk E t v Φ :
    has_go_type v t ->
    (∀ (l : loc), envs_entails
                    (envs_incr_counter
                       (envs_snoc Δ false (IAnon (env_counter Δ)) (l ↦[t] v)%I))
                    (WP (Val #l) @ stk; E {{ Φ }})
    ) →
    envs_entails Δ (WP (ref_ty t v) @ stk; E {{ Φ }}).
  Proof. Admitted.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    (first
        [wp_bind (load_ty _ (Val _)); eapply tac_wp_load_ty
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [solve_pointsto ()
      |wp_finish] )
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_] _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦[t] ?" in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [wp_bind (store_ty _ (Val _) (Val _)); eapply tac_wp_store_ty
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [solve_has_go_type
    |solve_pointsto ()
    |reduction.pm_reflexivity
    |first [wp_pure_filter (Rec BAnon BAnon _)|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

(* To step over a mem operation with
   x := (struct.field_ref_f t n l), look first for (x ↦[...] ...).
   Then, look for (l ↦[t])
 *)

Tactic Notation "wp_pure" :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        let x := constr:(ltac:(tc_solve) : PureWp _ e' _) in
        eapply (tac_wp_pure_wp K e');
          [refine x (* PureWp *)
          |try solve_vals_compare_safe (* pure side condition *)
          |tc_solve (* MaybeIntoLaterNEnvs *)
          |wp_finish (* new goal *)
          ]
      ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Ltac wp_pures' :=
  iStartProof;
  lazymatch goal with
    | |- envs_entails ?envs (wp ?s ?E (Val ?v) ?Q) => wp_finish
    | |- _ =>
      (* The `;[]` makes sure that no side-condition magically spawns. *)
      (* TODO: do this in one go, without [repeat]. *)
      (* XXX: what did the above comment mean? *)
      repeat (wp_pure; [])
  end.

Tactic Notation "wp_pure1_maybe_lc" constr(maybeCredName) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      let x := constr:(ltac:(tc_solve) : PureExec _ _ e' _) in
      first [ eapply (tac_wp_pure maybeCredName K e');
      [refine x (* PureExec *)
      |try solve_vals_compare_safe      (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                         (* IntoLaters *)
      | reduction.pm_reduce; wp_finish  (* new goal *)
      ] | fail "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chose to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_pure_prev" := wp_pure1_maybe_lc (Datatypes.None : option string).

Ltac wp_pures_prev :=
  iStartProof;
  lazymatch goal with
    | |- envs_entails ?envs (wp ?s ?E (Val ?v) ?Q) => wp_finish
    | |- _ =>
      (* The `;[]` makes sure that no side-condition magically spawns. *)
      (* TODO: do this in one go, without [repeat]. *)
      (* XXX: what did the above comment mean? *)
        repeat (first [ wp_pure_prev | wp_pure]; [])
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  (wp_bind (ref_ty _ _) || fail "the next step is not ref_ty");
  simple eapply (tac_wp_ref_ty H);
  [ solve_has_go_type
  | intros l; reduction.pm_reduce; wp_value_head]
.

Tactic Notation "wp_alloc" ident(l) :=
  (wp_bind (ref_ty _ _) || fail "the next step is not ref_ty");
  simple eapply tac_wp_ref_ty_anon;
  [ solve_has_go_type
  | intros l; reduction.pm_reduce; wp_value_head]
.

Ltac iStructSplit n :=
  iDestruct (struct_fields_split with n) as n;
  [ done | tc_solve |
    iEval (repeat (rewrite zero_val_eq || rewrite struct.val_unseal); simpl) in n; iNamed n].

Ltac wp_steps :=
  wp_pures'; try ((wp_load; wp_steps) || (wp_store; wp_steps)).

Global Instance wp_int_gt (l r : w64) :
  PureWpVal True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Lemma wp_network__send (nw : loc) msgs_sl :
  {{{ True }}}
    network__send #nw (slice.val msgs_sl)
  {{{ RET #(); True }}}
.
Proof.
  iIntros (?) "_ HΦ".
  wp_rec.
  wp_pures'.
  wp_alloc nw_ptr.
  wp_pures'.
  wp_alloc msgs_ptr.
  wp_pures.
  wp_for.
  wp_pures'.
  wp_load.
  wp_pures'.
  iModIntro.
  destruct bool_decide eqn:Hlt.
  - simpl. (* Case: more messages to send *)
    wp_pures. rewrite bool_decide_eq_true in Hlt.
    wp_alloc m.
    wp_steps.
    wp_pure.
    {
      (* FIXME(word): handle sint.Z *)
      rewrite !word.signed_eq_swrap_unsigned in Hlt.
      unfold word.swrap in Hlt.
      word.
    }
    admit. (* TODO: add slice ownership to precondition *)
  - simpl. wp_steps. iModIntro. by iApply "HΦ".
Admitted.

Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  wp_rec.
  replace (raftpb.MsgHup) with (Val #37) by admit.
  wp_steps.
  wp_alloc preVote.
  wp_pures'.
  wp_alloc t_ptr.
  wp_steps.
  wp_alloc cfg as "Hcfg".
  wp_pures'.
  wp_alloc candState as "HcandState".
  wp_steps.
  wp_alloc candTerm as "HcandTerm".
  wp_steps.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures'.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  wp_steps.
  wp_alloc tests as "Htests".
  wp_steps.

  (* FIXME: binding is much faster than wp_applying directly. Similar to how
     wp_load/wp_store got faster after the wp_bind. *)
  Time wp_bind (slice.literal _ _);
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  replace (zero_val funcT) with (zero_val' funcT).
  2:{ by rewrite zero_val_eq. }

  (* Time wp_apply (wp_newNetworkWithConfigInit with "[]"). 639ms *)
  Time wp_bind (newNetworkWithConfigInit _ _);
  iApply (wp_newNetworkWithConfigInit with "[$]");
  iNext.

  iIntros (?) "Hnw1".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw2".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  (* Time wp_apply (wp_newNetworkWithConfigInit with "[$]"). *)
  Time wp_bind (newNetworkWithConfigInit _ _); iApply (wp_newNetworkWithConfigInit with "[$]"); iModIntro.
  iIntros (?) "Hnw3".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw4".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw5".

  wp_steps.

  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_steps.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_pures'.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures'.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw6".
  wp_pures'.
  wp_apply wp_slice_literal.
  { solve_has_go_type. }
  iIntros (?) "?".
  wp_steps.

  wp_apply wp_slice_for_range.
  iFrame.
  simpl foldr.
  (* Entire for loop is unfolded here. TODO: is there a way to unfold one iteration at a time? *)
  wp_pures'.
  wp_alloc i.
  wp_pures'.
  wp_alloc tt as "Htt".
  wp_pures'.
  wp_apply wp_struct_make.
  { admit. }
  Show Ltac Profile.
  wp_pures'.
  Time wp_bind (slice.literal _ _);
  iApply wp_slice_literal.
  { solve_has_go_type. admit. }
  { auto. }
  iNext. iIntros (?) "?".
  wp_pures'.
  iStructSplit "Htt".
  wp_load.

  Show Ltac Profile.
Admitted.


End proof.
