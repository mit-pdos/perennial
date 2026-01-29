Require Import New.proof.go_etcd_io.raft.v3_proof.base.

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

Section axioms.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* Global definitions, not specific to a particular (generation of a) node. *)
Axiom raft_names : Type.
Implicit Type γ : raft_names.

Axiom own_raft_log : ∀ γ, list (list w8) → iProp Σ.

Axiom is_raft_log : ∀ γ, list (list w8) → iProp Σ.
Axiom is_raft_log_pers : ∀ γ log, Persistent (is_raft_log γ log).
#[global] Instance is_raft_log_pers_inst γ log : Persistent (is_raft_log γ log) := (is_raft_log_pers _ _).

End axioms.

Section raft.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!closeable_chanG Σ}.
Context `{!contextG Σ}.

Implicit Type γraft : raft_names.

(* FIXME: maybe generally useful and should go somewhere else? *)
Definition unreceived {V} (s : chanstate.t V) : list V :=
  drop s.(chanstate.received) s.(chanstate.sent).

(* FIXME: goose could translate typed constants as a typed value? Or maybe
   emit that in proofgen, since there could be a struct-typed constant. *)
Definition MsgProp := (W32 2).

Definition own_propose_message γraft (pm : raft.msgWithResult.t) : iProp Σ :=
  ∃ data_sl (data : list w8),
    let m := pm.(raft.msgWithResult.m') in
  "Hmsg" ∷ ⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗
  "Hentries" ∷ m.(raftpb.Message.Entries') ↦* [data_sl] ∗
  "data_sl" ∷ data_sl ↦* data ∗
  "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True)) ∗
  "Hresult" ∷ inv nroot (∃ (s : chanstate.t error.t), own_chan pm.(raft.msgWithResult.result') s).

Local Definition is_node_inner γraft (n : raft.node.t) : iProp Σ :=
  "#Hpropc" ∷ inv nroot
    (∃ s, own_chan n.(raft.node.propc') s ∗ [∗ list] v ∈ (unreceived s), own_propose_message γraft v) ∗
  "#Hadvancec" ∷ inv nroot (∃ (s : chanstate.t unit), own_chan n.(raft.node.advancec') s) ∗
  "#Hdone" ∷ own_closeable_chan n.(raft.node.done') True closeable.Unknown.

Definition is_node γraft (n : loc) : iProp Σ :=
  ∃ nd,
  "n_ptr" ∷ n ↦□ nd ∗
  "Hinner" ∷ is_node_inner γraft nd.

Lemma wp_node__Ready γraft (n : loc) :
  {{{ is_pkg_init raft ∗ is_node γraft n }}}
    n @ (ptrT.id raft.node.id) @ "Ready" #()
  {{{ (ready : chan.t), RET #ready; True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
  by iApply "HΦ".
Qed.

(* FIXME: anonymous struct{} *)
Global Instance wp_struct_make_unit:
  PureWp True
    (struct.make #(structT []) (alist_val []))%struct
    #().
Proof.
  erewrite <- struct_val_aux_nil.
  apply wp_struct_make; cbn; auto.
Qed.

Lemma wp_node__Advance γraft (n : loc) :
  {{{ is_pkg_init raft ∗ is_node γraft n }}}
    n @ (ptrT.id raft.node.id) @ "Advance" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  iNamed "Hpre". wp_auto.
  wp_apply wp_chan_select_blocking.
  rewrite big_andL_cons big_andL_singleton.
  iSplit.
  - (* able to send on advancec *)
    iExists unit; repeat iExists _. iSplitR.
    { iPureIntro. done. }
    iNamed "Hinner".
    admit. (* just prove the send atomic update then trivial postcondition *)
  - repeat iExists _. iNamed "Hinner".
    iApply (closeable_chan_receive with "Hdone").
    iIntros "[_ _]". wp_auto. iApply "HΦ". done.
Admitted.

Lemma wp_node__Propose γraft n (ctx : context.Context.t) ctx_desc (data_sl : slice.t) (data : list w8) :
  {{{ is_pkg_init raft ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hnode" ∷ is_node γraft n ∗
      "data_sl" ∷ data_sl ↦* data ∗
      "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True))
  }}}
    n @ (ptrT.id raft.node.id) @ "Propose" #ctx #data_sl
  {{{ (err : error.t), RET #err; if decide (err = interface.nil) then True else True }}}.
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
      iIntros "[_ #HDone_closed]". wp_auto. wp_apply wp_globals_get.
      iDestruct (is_pkg_init_access with "[$]") as "#Hpkg".
      simpl is_pkg_init_def. iNamed "Hpkg".
      wp_auto.
      iApply "HΦ". rewrite decide_False //.
  }
  repeat iExists _.
  iSplitR; first done.
  (* case: send proposeMessage on propc *)
  (* TODO *)
Admitted.

End raft.
