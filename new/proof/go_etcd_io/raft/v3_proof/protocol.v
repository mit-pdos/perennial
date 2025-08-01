Require Import New.proof.go_etcd_io.raft.v3_proof.base.
Require Import New.proof.chan.
Local Transparent is_pkg_init_raft.

Module node.
Axiom t : Type.
End node.

Module message.
Axiom t : Type.
End message.

Module entry.
Definition t : Type := list w8.
End entry.

Module astate.
Record t :=
  {
    log : list entry.t;
  }.
End astate.

Section raft.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!quorum.GlobalAddrs}.
Context `{!tracker.GlobalAddrs}.
Context `{!raft.GlobalAddrs}.
Context `{!closeable_chanG Σ}.
Context `{!contextG Σ}.

Axiom is_chan_inv : ∀ (c : chan.t) {V} `{!IntoVal V} (P : V → iProp Σ), iProp Σ.
Instance is_chan_inv_pers c V `{!IntoVal V} (P : V → _) : Persistent (is_chan_inv c P).
Proof. Admitted.

Local Definition is_Node_inner (n : raft.node.t) : iProp Σ :=
  "#Hpropc" ∷ is_chan_inv n.(raft.node.propc') (λ (_ : raft.msgWithResult.t), True)%I ∗
  "#Hadvancec" ∷ is_chan_inv n.(raft.node.advancec') (λ (_ : unit), True)%I ∗
  "#Hdone" ∷ own_closeable_chan n.(raft.node.done') True closeable.Unknown.

Definition is_Node (n : loc) : iProp Σ :=
  ∃ nd,
  "n_ptr" ∷ n ↦□ nd ∗
  "Hinner" ∷ is_Node_inner nd.

Lemma wp_node__Ready (n : loc) :
  {{{ is_pkg_init raft ∗ is_Node n }}}
    n@raft@"node'ptr"@"Ready" #()
  {{{ (ready : chan.t), RET #ready; True }}}.
Proof.
  wp_start. wp_auto. (* need repr predicate for node *)
Admitted.

Lemma wp_node__Advance (n : loc) :
  {{{ is_pkg_init raft ∗ is_Node n }}}
    n@raft@"node'ptr"@"Advance" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  iNamed "Hpre".
  wp_auto.
  (* FIXME: want unit, but ending up with raft.TracingEvent.t *)
  wp_apply wp_chan_select_blocking.
  rewrite big_andL_cons big_andL_singleton.
  iSplit.
  - (* able to send on advancec *)
    repeat iExists _. instantiate (1:=(tt : unit)). iSplitR.
    { iPureIntro. admit. }
    Unshelve. 2: tc_solve.
    admit. (* just prove the send atomic update then trivial postcondition *)
  - repeat iExists _. iNamed "Hinner". Search own_closeable_chan.
    iApply (closeable_chan_receive with "Hdone").
    iIntros "[_ _]". wp_auto. iApply "HΦ". done.
Admitted.

Lemma wp_node__Propose n (ctx : context.Context.t) ctx_desc (data_sl : slice.t) (data : list w8) :
  {{{ is_pkg_init raft ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hnode" ∷ is_Node n ∗
      "data_sl" ∷ data_sl ↦* data }}}
    n@raft@"node'ptr"@"Propose" #ctx #data_sl
  {{{ (err : error.t), RET #err; if decide (err = interface.nil) then False else True }}}.
Proof.
  (* Inlining proofs of [stepWait] and [stepWithWaitOption (wait:=true)] here. *)
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply wp_slice_literal. iIntros "%entries_sl entries_sl".
  wp_auto. wp_bind. wp_method_call. wp_call.
  iClear "n ctx". clear n_ptr ctx_ptr.
  wp_auto. wp_bind. wp_method_call. wp_call.
  iClear "n m ctx". clear n_ptr m_ptr ctx_ptr.
  wp_auto. iNamed "Hnode". wp_auto. wp_apply (wp_chan_make (V:=error.t)).
  iIntros "%result %result_init Hch". wp_auto.
  iNamed "Hctx". wp_apply "HDone".
  wp_apply wp_chan_select_blocking.
  rewrite !big_andL_cons big_andL_nil. rewrite right_id.
  iSplit.
  2:{
    iSplit.
    - (* case: got something from ctx.Done() channel *)
      repeat iExists _.
      iApply (closeable_chan_receive with "HDone_ch").
      iIntros "[_ #HDone_closed]". wp_auto. wp_apply ("HErr" with "HDone_closed").
      iIntros (err) "%Herr". wp_auto.
      iApply "HΦ". rewrite decide_False //.
    - (* case: raft is done *)
      repeat iExists _. iNamed "Hinner".
      iApply (closeable_chan_receive with "Hdone").
      iIntros "[_ #HDone_closed]". wp_auto. wp_globals_get.
      (* FIXME: global variable holding an error *)
      admit.
  }
  repeat iExists _.
  iSplitR; first done.
Qed.

End raft.

Section proof.
Context `{!heapGS Σ}.

End proof.
