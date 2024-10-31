From New.code.go_etcd_io.raft Require Import v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.
From New.proof Require Import structs.go_etcd_io.raft.v3.raftpb.
From New.proof Require Import grove_prelude.

Section proof.
Context `{!heapGS Σ}.

(* FIXME: move to builtin *)
Instance wp_int_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Lemma wp_newNetworkWithConfigInit (peers : list interface.t) peers_sl :
  {{{
        peers_sl ↦* peers
  }}}
    newNetworkWithConfigInit #func.nil #peers_sl
  {{{
        nw_ptr (nw : network.t), RET #nw_ptr; nw_ptr ↦ nw
  }}}
.
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

Lemma wp_network__send nw msgs_sl dq (n : network.t) (msgs : list Message.t) :
  {{{
        "Hmsg" ∷ msgs_sl ↦*{dq} msgs ∗
        "Hnw" ∷ nw ↦ n
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
  wp_for.
  wp_pures.
  wp_load.
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
    wp_load.
    wp_pure.
    {
      (* FIXME(word): handle sint.Z *)
      rewrite !word.signed_eq_swrap_unsigned /word.swrap in Hlt.
      word.
    }
    wp_load.
    wp_pures.
    iDestruct ("Hmsg" with "[$]") as "Hmsg".
    rewrite list_insert_id; last done.
    wp_store.
    wp_pures.
    wp_alloc p as "?".
    wp_pures.

    iDestruct (struct_fields_split with "Hm") as "Hm".
    { done. }
    { apply _. }
    rewrite /struct_fields /=.
    repeat (iDestruct "Hm" as "[H1 Hm]";
            unshelve iSpecialize ("H1" $! _ _ _ _ _ _); try tc_solve;
            iNamed "H1").
    wp_load.
    wp_load.
    wp_pures.
    wp_pures.

    iDestruct (struct_fields_split with "Hnw") as "Hnw".
    { done. }
    { apply _. }
    rewrite /struct_fields /=.
    repeat (iDestruct "Hnw" as "[H1 Hnw]";
            unshelve iSpecialize ("H1" $! _ _ _ _ _ _); try tc_solve;
            iNamed "H1").
    wp_load.
    admit. (* FIXME: need own_map *)
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
