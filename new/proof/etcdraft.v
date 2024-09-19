From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import grove_prelude.
From New.proof Require Import sync.
From New.proof Require Import proofmode.
From Ltac2 Require Import Ltac2.

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
        | _ => constr:(subst' $x $v $e)
                       (* | _ => Control.throw (Tactic_failure None) *)
        end in
      go_subst e
  end
.

Ltac2 rec expr_step e : constr :=
  lazy_match! e with
  | Rec ?f ?x ?e =>
      dbg (Message.of_string "reached Rec");
      '(Val $ RecV $f $x $e)
  | App (Val (RecV ?f ?x ?e)) (Val ?v2) =>
      dbg (Message.of_string "reached App (RecV ...) v");
      dbg_constr e;
      (* FIXME: try to keep identifier for function name *)
      subst_step x v2 (subst_step f '(@LitV grove_op LitUnit) e)
      (* subst_step x v2 e (subst_step f '#() e) *)
  | App (?e1) (Val ?v)  =>
      dbg (Message.of_string "reached App e v");
      let e1 := expr_step '$e1 in
      '(App $e1 (Val $v))
  | App ?e1 ?e2 =>
      dbg (Message.of_string "reached App e e");
      let e2new := expr_step '$e2 in
      dbg_constr e2new;
      '(App $e1 $e2new)
  end
.

Ltac2 rec expr_steps e : constr :=
  Control.plus
    (fun () => expr_steps (expr_step e))
    (fun ex => dbg (Message.of_string "no more steps due to: "); dbg (Message.of_exn ex); e)
.

Ltac2 wp_pures_fast () :=
  match! goal with
  | [ |- envs_entails ?Δ (wp ?s ?et ?e ?Φ)] =>
      let e' := (expr_steps e) in
      enough (envs_entails $Δ (wp $s $et $e' $Φ)) by admit
  end.

Ltac2 mutable fast_mode_wp : bool := false.
Ltac2 Set dbg := (fun _ => ()).
Ltac2 Set dbg_constr := (fun _ => ()).

Ltac2 wp_pures () :=
  if fast_mode_wp then
    wp_pures_fast ()
  else
    ltac1:(wp_pures)
.

Set Default Proof Mode "Classic".

Instance maybe_into_later_nenvs_id n Δ : coq_tactics.MaybeIntoLaterNEnvs n Δ Δ (PROP:=iProp Σ).
Proof. Admitted.

Ltac2 reshape_expr (e : constr) (tac : constr -> constr -> unit) :=
  let rec go (k : constr) (e : constr) :=
    let add_item ki e := (go '($ki :: $k) e) in
    match! e with
    | _                               => tac k e
    | App ?e (Val ?v)                 => add_item '(@AppLCtx _ $v) e
    | App ?e1 ?e2                     => add_item '(@AppRCtx _ $e1) e2
    | UnOp ?op ?e                     => add_item '(@UnOpCtx _ $op) e
    | BinOp ?op (Val ?v) ?e           => add_item '(@BinOpRCtx _ $op $v) e
    | BinOp ?op ?e1 ?e2               => add_item '(@BinOpLCtx _ $op $e2) e1
    | If ?e0 ?e1 ?e2                  => add_item '(IfCtx $e1 $e2) e0
    | Pair (Val ?v) ?e                => add_item '(PairRCtx $v) e
    | Pair ?e1 ?e2                    => add_item '(PairLCtx $e2) e1
    | Fst ?e                          => add_item '(@FstCtx _) e
    | Snd ?e                          => add_item '(@SndCtx _) e
    | InjL ?e                         => add_item '(@InjLCtx _) e
    | InjR ?e                         => add_item '(@InjRCtx _) e
    | Case ?e0 ?e1 ?e2                => add_item '(CaseCtx $e1 $e2) e0
    | Primitive2 ?op (Val ?v) ?e      => add_item '(@Primitive2RCtx _ $op $v) e
    | Primitive2 ?op ?e1 ?e2          => add_item '(@Primitive2LCtx _ $op $e2) e1
    | Primitive1 ?op ?e               => add_item '(@Primitive1Ctx _ $op) e
    | ExternalOp ?op ?e               => add_item '(@ExternalOpCtx _ $op) e
    | CmpXchg (Val ?v0) (Val ?v1) ?e2 => add_item '(CmpXchgRCtx $v0 $v1) e2
    | CmpXchg (Val ?v0) ?e1 ?e2       => add_item '(CmpXchgMCtx $v0 $e2) e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item '(CmpXchgLCtx $e1 $e2) e0
    | ResolveProph (Val ?v) ?e        => add_item '(@ResolveProphRCtx _ $v) e
    | ResolveProph ?e1 ?e2            => add_item '(@ResolveProphLCtx _ $e2) e1
    | fill ?k' ?e                     => match! k with [] => go k' e end
    end
  in
  go '(@nil ectx_item) e.

Ltac2 wp_pure1_maybe_lc_fast () :=
  match! goal with
  | [ |- envs_entails ?envs (wp ?s ?et ?e ?q) ] =>
      reshape_expr e (fun k e' =>
                        let e2 := '(_ : expr) in
                        let x := constr:(ltac2:(apply _): PureExec True _ $e' $e2) in
                        enough (envs_entails $envs (wp $s $et (fill $k $e2) $q)) by admit)
  end.

Ltac wp_finish :=
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  reduction.pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Tactic Notation "wp_pure1_maybe_lc_no_simpl" constr(maybeCredName) :=
  lazymatch goal with
  | |- envs_entails ?envs (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      first [ eapply (tac_wp_pure maybeCredName K e');
      [tc_solve                         (* PureExec *)
      |try solve_vals_compare_safe      (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                         (* IntoLaters *)
      | reduction.pm_reduce; wp_finish  (* new goal *)
      ] | fail "wp_pure: first pattern match is not a redex" ]
          (* "3" is carefully chose to bubble up just enough to not break out of the [repeat] in [wp_pures] *)
   ) || fail "wp_pure: cannot find redex pattern"
  | _ => fail "wp_pure: not a 'wp'"
  end.

  Lemma tac_wp_load_ty Δ Δ' s E i l q t v Φ is_pers :
    coq_tactics.MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (is_pers, typed_pointsto l q t v)%I →
    envs_entails Δ' (WP (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP (load_ty t (LitV l)) @ s; E {{ Φ }}).
  Proof. Admitted.

  Lemma tac_wp_store_ty Δ Δ' Δ'' stk E i l t v v' Φ :
    has_go_type v' t ->
    coq_tactics.MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (false, l ↦[t] v)%I →
    envs_simple_replace i false (Esnoc Enil i (l ↦[t] v')) Δ' = Some Δ'' →
    envs_entails Δ'' (WP (Val $ LitV LitUnit) @ stk; E {{ Φ }}) →
    envs_entails Δ (WP (store_ty t (LitV l) v') @ stk; E {{ Φ }}).
  Proof. Admitted.

Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦[t] ?" in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    ( first
        [wp_bind (load_ty _ _); eapply tac_wp_load_ty
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [tc_solve
      |solve_pointsto ()
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
      [wp_bind (store_ty _ _ _); eapply tac_wp_store_ty
      |fail 1 "wp_store: cannot find 'store_ty' in" e];
    [(repeat econstructor || fail "could not establish [has_go_type]") (* solve [has_go_type v' t] *)
    |tc_solve
    |solve_pointsto ()
    |reduction.pm_reflexivity
    |first [wp_pure_filter (Rec BAnon BAnon _)|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_pures" := ltac2:(wp_pures ()).
Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  Time wp_rec.
  Time wp_alloc preVote as "?".
  wp_alloc t_ptr as "?".
  wp_alloc cfg as "Hcfg".
  wp_alloc candState as "HcandState".
  wp_pures.
  wp_store.
  wp_pures.
  wp_pures.
  wp_alloc candTerm as "HcandTerm".
  wp_pures.
  wp_store.
  wp_pures.
  wp_load.
  wp_pures.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  Time wp_pures.
  Time wp_store.
  simpl fill.
  Time wp_pures.
  wp_alloc tests as "Htests".
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  replace (zero_val funcT) with (zero_val' funcT).
  2:{ by rewrite zero_val_eq. }
  simpl.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw1".

  wp_pures.
  Set Ltac Profiling.
  goose_lang.proofmode.wp_pures.
  Show Ltac Profile.
  Time wp_load.

  (* FIXME: figure out if tc search is slow, or if applying the lemma is slow. *)
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw2".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw3".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw4".

  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw5".

  wp_pures.
  wp_load.
  wp_pures.

  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_pures.
  wp_load.
  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_pures.
  wp_apply wp_slice_literal.
  { repeat constructor. }
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros (?) "Hnw6".
  wp_pures.
  wp_apply wp_slice_literal.
  { solve_has_go_type. }
  iIntros (?) "?".
  wp_pures.
  wp_store.
  wp_pures.
  wp_load.
  wp_pures.
  simpl.
Admitted.

End proof.
