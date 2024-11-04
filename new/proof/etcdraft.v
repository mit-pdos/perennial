From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.raftpb.
From New.proof Require Import grove_prelude.

Section proof.
Context `{!heapGS Σ}.

(* FIXME: move to builtin *)
Instance wp_int_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

(* TODO: automatically generate these instances? *)
Instance countable_connem : Countable connem.t.
Admitted.

(*
Lemma test :
  ∀ nw_ptr nw, True -∗
        nw_ptr ↦ nw ∗
        nw.(network.ignorem) ↦$ (∅ : gmap w32 bool)
. *)

Lemma wp_newNetworkWithConfigInit (peers : list interface.t) peers_sl :
  {{{
        peers_sl ↦* peers
  }}}
    newNetworkWithConfigInit #func.nil #peers_sl
  {{{
        (peersMap : gmap w64 interface.t) nw_ptr (nw : network.t), RET #nw_ptr;
        nw_ptr ↦ nw ∗
        nw.(network.peers) ↦$□ peersMap ∗
        nw.(network.dropm64) ↦$ (∅ : gmap connem.t w64) ∗
        nw.(network.ignorem) ↦$ (∅ : gmap w32 bool) ∗
        ⌜ ∀ (i : nat) peer, peers !! i = Some peer →
           if decide (peer = interface.nil) then
             ∃ raftPeer mset, peersMap !! (W64 i) = Some (interface.mk raftPeer mset)
           else
             peersMap !! (W64 i) = Some peer ⌝
        (* FIXME: Coq takes essentially forever if either the `i : nat`
           annotation is removed or if the explicit `W64 i` is removed. *)
  }}}.
Proof.
Admitted.

Lemma wp_entsWithConfig terms_sl (terms : list u64) :
  {{{
        terms_sl ↦* terms
  }}}
    entsWithConfig #func.nil #terms_sl
  {{{ (r : loc), RET #r; True }}}
.
Proof.
Admitted.

(*
Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    (first
        [wp_bind (load_ty _ (Val _)); eapply tac_wp_load_ty
        |fail 1 "wp_load: cannot find 'load_ty' in" e];
      [solve_pointsto () |] )
  | _ => fail "wp_load: not a 'wp'"
  end. *)

Class PointsToAccess {V Vsmall}
  {t tsmall} `{!IntoVal V} `{!IntoVal Vsmall} `{!IntoValTyped V t} `{!IntoValTyped Vsmall tsmall}
  (l' l : loc) (v : V) (vsmall : Vsmall) (update : Vsmall → V → V) : Prop :=
  {
    points_to_acc : ∀ dq, l' ↦{dq} v -∗ l ↦{dq} vsmall ∗
                        (∀ vsmall', l ↦{dq} vsmall' -∗ l' ↦{dq} (update vsmall' v));
    points_to_update_eq : update vsmall v = v
  }.

Import environments.

Lemma tac_wp_load_ty {V t Vsmall tsmall}
  `{!IntoVal V} `{!IntoValTyped V t} `{!IntoVal Vsmall} `{!IntoValTyped Vsmall tsmall}
  (l' l : loc) (v : V) (vsmall : Vsmall) update Δ s E i dq Φ is_pers
  `{!PointsToAccess l' l v vsmall update} :
  envs_lookup i Δ = Some (is_pers, typed_pointsto l' dq v)%I →
  envs_entails Δ (Φ #vsmall) →
  envs_entails Δ (WP (load_ty tsmall #l) @ s; E {{ Φ }}).
Proof using Type*.
  rewrite envs_entails_unseal => ? HΦ.
  rewrite envs_lookup_split //.
  iIntros "[H Henv]".
  destruct is_pers; simpl.
  - iDestruct "H" as "#H".
    iDestruct (points_to_acc with "H") as "[H' _]".
    wp_load.
    iApply HΦ. iApply "Henv". iFrame "#".
  - iDestruct (points_to_acc with "H") as "[H Hclose]".
    wp_load.
    iApply HΦ. iApply "Henv".
    iSpecialize ("Hclose" with "[$]").
    rewrite points_to_update_eq. iFrame.
Qed.

(* XXX: what about getting rid of the [t] parameter and using [structT d] in its place? *)
Instance points_to_access_struct_field_ref {V Vf} l f v (proj : V → Vf) {t tf : go_type}
  `{!IntoVal V} `{!IntoValTyped V t}
  `{!IntoVal Vf} `{!IntoValTyped Vf tf}
  `{!IntoValStructField f t proj} `{!SetterWf proj}
  `{!struct.Wf t}
  : PointsToAccess l (struct.field_ref_f t f l) v (proj v) (λ vf', set proj (λ _, vf')).
Proof.
  constructor.
  - intros. by iApply struct_fields_acc_update.
  - by rewrite RecordSet.set_eq.
Qed.

Instance points_to_access_trivial {V} l (v : V) {t} `{!IntoVal V} `{!IntoValTyped V t}
  : PointsToAccess l l v v (λ v' _, v').
Proof. constructor; [eauto with iFrame|done]. Qed.

Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 tc_solve_many () := solve [ltac1:(typeclasses eauto)].
Ltac2 wp_load () :=
  lazy_match! goal with
  | [ |- envs_entails _ (wp _ _ _ _) ] =>
      let _ := (orelse
        (fun () =>
           let e := wp_bind_filter (Std.unify '(load_ty _ (Val _))) in
           match! e with (App (Val (load_ty _)) (Val #?l)) => l end
        )
        (fun _ => Control.backtrack_tactic_failure "wp_load: could not bind to load instruction")
      ) in
      (* XXX: we want to backtrack to typeclass search if [iAssumptionCore] failed. *)

      (* FIXME: only want backtracking to happen if [iAssumptionCore] fails.
         Better yet, get rid of backtracking entirely here. Wrap this whole
         thing in a backtracking pattern match or something. *)
      eapply (tac_wp_load_ty) > [tc_solve_many ()| ltac1:(iAssumptionCore) |]
  end.

Lemma wp_network__send nw msgs_sl dq (n : network.t) (msgs : list Message.t) :
  {{{
        "Hmsg" ∷ msgs_sl ↦*{dq} msgs ∗
        "Hnw" ∷ nw ↦ n ∗
        "Hn_peers" ∷ ∃ (peersMap : gmap w64 interface.t), n.(network.peers) ↦$□ peersMap
  }}}
    network__send #nw #msgs_sl
  {{{ RET #(); True }}}
.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  wp_call.
  wp_alloc nw_ptr as "?".
  wp_pures.
  wp_alloc msgs_ptr as "?".
  wp_pures.
  Print env.
  Print envs.
  wp_for.
  wp_pures.
  ltac2:(wp_load ()).
  wp_pures.
  case_bool_decide as Hlt.
  - rewrite decide_True //. (* Case: more messages to send *)
    wp_pures.
    rewrite -!default_val_eq_zero_val.
    wp_alloc m as "Hm".
    wp_pures.
    iDestruct (own_slice_len with "Hmsg") as %Hsz.
    destruct msgs.
    { exfalso. simpl in *. rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt. word. }
    iDestruct (own_slice_elem_acc 0 with "Hmsg") as "[Helem Hmsg]".
    { done. }
    ltac2:(wp_load ()).
    wp_pure.
    {
      (* FIXME(word): handle sint.Z *)
      rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt.
      word.
    }
    ltac2:(wp_load ()).
    wp_pures.
    iDestruct ("Hmsg" with "[$]") as "Hmsg".
    rewrite list_insert_id; last done.
    wp_store.
    wp_pures.
    wp_alloc p as "?".
    wp_pures.
    ltac2:(wp_load ()).
    ltac2:(wp_load ()).
    wp_pures.
    ltac2:(wp_load ()).

    ltac2:(wp_load ()).
    iDestruct (struct_fields_acc_update "To" with "Hm") as "[Hf Hm]".
    { done. }
    { apply _. }
    wp_load.
    iSpecialize ("Hm" with "[$]").
    rewrite ?RecordSet.set_eq //.

    wp_bind (load_ty _ (Val _)).
    iRename select (nw_ptr ↦ nw)%I into "H1".
    Time wp_apply (wp_typed_load with "H1").
    Time wp_load.
    wp_pures.

    iDestruct (struct_fields_acc_update "peers" with "Hnw") as "[Hf Hnw]".
    { done. }
    { apply _. }
    wp_load.
    iSpecialize ("Hnw" with "[$]").

    rewrite ?RecordSet.set_eq //.
    (* FIXME: persistent instance for ↦$□ *)
    iDestruct "Hn_peers" as (?) "Hn_peers".
    wp_apply (wp_map_get with "[$]").
    iIntros "_".
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_pures.

    iDestruct (struct_fields_acc_update "t" with "Hnw") as "[Hf Hnw]".
    { done. }
    { apply _. }
    Time wp_load.
    iSpecialize ("Hnw" with "[$]").
    wp_pures.
    (* XXX: should be an "irrelevant" if statement. *)
    case_bool_decide.
    + (* no testing object, so no logging. *)
      wp_pures.
      (* FIXME: combine back the Message points-to, or avoid splitting it up in the first place. *)
      wp_load.
      admit.
    + admit.
  - rewrite decide_False; last naive_solver.
    rewrite decide_True; last naive_solver.
    wp_pures. by iApply "HΦ".
Admitted.

Ltac wp_steps :=
  wp_pures; try ((wp_load; wp_steps) || (wp_store; wp_steps)).


Lemma wp_slice_literal t {V stk E} :
  ∀ (l : list V) `{!IntoVal V} `{!IntoValTyped V t},
  {{{ True }}}
    slice.literal t #l @ stk ; E
  {{{ sl, RET #sl; sl ↦* l }}}.
Proof.
Admitted.

Lemma wp_testLeaderElection2 :
  {{{ True }}}
    testLeaderElection2 #null #false
  {{{ RET #(); True }}}.
Proof.
  Set Ltac Profiling.
  iIntros (?) "_ HΦ".
  wp_call.
  wp_alloc preVote as "?".
  wp_pures.
  wp_alloc t_ptr as "?".
  wp_steps.
  rewrite -!default_val_eq_zero_val.
  wp_alloc cfg as "Hcfg".
  wp_pures.
  wp_alloc candState as "HcandState".
  wp_steps.
  wp_alloc candTerm as "HcandTerm".
  wp_pures.
  wp_store.
  wp_pures.

  wp_steps.

  wp_alloc nopStepper as "HnopStepper".
  wp_pures.
  wp_alloc nopStepperPtr as "HnopStepperPtr".
  wp_steps.
  wp_alloc tests as "Htests".
  wp_steps.

  (* wp_bind (slice.literal _ _)%E.
  unshelve iPoseProofCore (wp_slice_literal stateMachine _ with "[//]") as false
    (fun Htmp => iApplyHyp Htmp). *)
  (* FIXME: find a way to avoid shelved typeclass goal. Not sure why [_] is
     needed to avoid the shelved goal. *)
  wp_apply (wp_slice_literal stateMachine _).
  iIntros (?) "?".

  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw1".

  wp_steps.
  wp_apply (wp_slice_literal stateMachine _).
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw2".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  (* Time wp_apply (wp_newNetworkWithConfigInit with "[$]"). *)
  Time wp_bind (newNetworkWithConfigInit _ _); iApply (wp_newNetworkWithConfigInit with "[$]"); iModIntro.
  iIntros "* Hnw3".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw4".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw5".

  wp_steps.

  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr1".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr2".

  wp_steps.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_entsWithConfig with "[$]").
  iIntros (?) "Hr3".

  wp_pures.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "?".
  wp_pures.
  wp_apply (wp_newNetworkWithConfigInit with "[$]").
  iIntros "* Hnw6".
  wp_pures.
  unshelve wp_apply wp_slice_literal; first apply _.
  iIntros (?) "Hsl".
  wp_steps.

  wp_apply wp_slice_for_range.
  iFrame "Hsl".
  simpl foldr.
  (* Entire for loop is unfolded here. TODO: is there a way to unfold one iteration at a time? *)
  wp_pures.
  wp_alloc i as "?".
  wp_pures.
  wp_alloc tt as "Htt".
  wp_pures.
  wp_apply wp_slice_literal.
  iIntros (?) "Hsl".

  (* FIXME: better tactic for splitting. *)
  iDestruct (struct_fields_split with "Htt") as "Htt".
  { done. }
  { apply _. }
  rewrite /struct_fields /=.
  repeat (iDestruct "Htt" as "[H1 Htt]";
          unshelve iSpecialize ("H1" $! _ _ _ _ _ _); try tc_solve;
          iNamed "H1").

  wp_steps.

  simpl.
  wp_apply (wp_network__send with "[$Hnw1 $Hsl]").
  wp_steps.
  wp_alloc sm_ptr as "?".
  wp_steps.
  (* TODO: should get of ownership of network struct from newNetworkWithConfigInit *)
  Show Ltac Profile.
Admitted.

End proof.
