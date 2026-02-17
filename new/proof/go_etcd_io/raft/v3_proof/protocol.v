Require Import New.proof.go_etcd_io.raft.v3_proof.base.
From New.proof.chan_proof Require Import closeable.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import logatom.chan_au_base idiom.handoff.handoff.

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

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Local Set Default Proof Using "All".

Implicit Type γraft : raft_names.

Definition MsgProp := (W32 2).

Definition own_propose_message γraft (pm : raft.msgWithResult.t) : iProp Σ :=
  ∃ data_sl (data : list w8) γch,
    let m := pm.(raft.msgWithResult.m') in
  "Hmsg" ∷ ⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗
  "Hentries" ∷ m.(raftpb.Message.Entries') ↦* [data_sl] ∗
  "data_sl" ∷ data_sl ↦* data ∗
  "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True)) ∗
  (* FIXME: probably can only send once. *)
  "Hresult" ∷ is_chan_handoff γch pm.(raft.msgWithResult.result') (λ (_ : error.t), True%I)
.

Local Definition is_node_inner γraft (n : raft.node.t) : iProp Σ :=
  ∃ γp γa γd,
  "#Hpropc" ∷ is_chan_handoff γp n.(raft.node.propc') (λ (_ : error.t), True%I) ∗
  "#Hadvancec_is" ∷ is_chan n.(raft.node.advancec') γa unit ∗
  "#Hadvancec" ∷ inv nroot (∃ s, own_chan γa unit s) ∗
  "#Hdone" ∷ own_closeable_chan n.(raft.node.done') γd True closeable.Unknown.

Definition is_node γraft (n : loc) : iProp Σ :=
  ∃ nd,
  "n_ptr" ∷ n ↦□ nd ∗
  "Hinner" ∷ is_node_inner γraft nd.

Lemma wp_node__Ready γraft (n : loc) :
  {{{ is_pkg_init raft ∗ is_node γraft n }}}
    n @! (go.PointerType raft.node) @! "Ready" #()
  {{{ (ready : chan.t), RET #ready; True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto. wp_end.
Qed.

Lemma wp_node__Advance γraft (n : loc) :
  {{{ is_pkg_init raft ∗ is_node γraft n }}}
    n @! (go.PointerType raft.node) @! "Advance" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  iNamed "Hpre". wp_auto.
  wp_apply chan.wp_select_blocking.
  rewrite big_andL_cons big_andL_singleton.
  iSplit.
  - (* able to send on advancec *)
    iExists unit; repeat iExists _. iSplitR.
    { iPureIntro. done. }
    iNamed "Hinner".
    admit. (* just prove the send atomic update then trivial postcondition *)
  - iNamed "Hinner". repeat iExists _.
    iSplitR; first done. iSplitR; first admit.
    iDestruct (closeable_chan_receive with "Hdone [-]") as "H".
    2:{
      iExactEq "H". f_equal.
      (* FIXME: chanG0 needs to match closeable_chanG0.... *)
      admit.
    }
    iIntros "[_ _]". wp_auto. iApply "HΦ". done.
Admitted.

Lemma wp_node__Propose γraft n ctx ctx_desc (data_sl : slice.t) (data : list w8) :
  {{{ is_pkg_init raft ∗
      "#Hctx" ∷ is_Context ctx ctx_desc ∗
      "#Hnode" ∷ is_node γraft n ∗
      "data_sl" ∷ data_sl ↦* data ∗
      "Hupd" ∷ (|={⊤,∅}=> ∃ log, own_raft_log γraft log ∗ (own_raft_log γraft (log ++ [data]) ={∅,⊤}=∗ True))
  }}}
    n @! (go.PointerType raft.node) @! "Propose" #(interface.ok ctx) #data_sl
  {{{ (err : error.t), RET #err; if decide (err = interface.nil) then True else True }}}.
Proof.
  (* Inlining proofs of [stepWait] and [stepWithWaitOption (wait:=true)] here. *)
  wp_start. iNamed "Hpre". wp_auto.
  wp_apply wp_slice_literal as "%entries_sl [entries_sl _]".
  { iIntros. wp_auto. iFrame. }
  wp_bind. wp_method_call. wp_call. wp_call.
  wp_auto. wp_bind. wp_method_call. wp_call. wp_call.
  wp_auto. iNamed "Hnode". wp_auto. wp_apply chan.wp_make2.
  { word. }
  iIntros "%result %result_init Hch". wp_auto.
  iNamed "Hctx". wp_apply "HDone".
  wp_apply chan.wp_select_blocking.
  rewrite !big_andL_cons big_andL_nil. rewrite right_id.
  iSplit.
  2:{
    iSplit.
    - (* case: got something from ctx.Done() channel *)
      repeat iExists _. iSplitR; first done. iSplitR; first admit.
      instantiate (1:=ctx_desc.(Context_desc.Done_gn)).
      iClear "Hinner".
      iDestruct (closeable_chan_receive with "HDone_ch []") as "H".
      2:{ iExactEq "H". f_equal.
          (* FIXME: conflicting inGs. *)
  (*     iIntros "[_ #HDone_closed]". wp_auto. wp_apply ("HErr" with "HDone_closed"). *)
  (*     iIntros (err) "%Herr". wp_auto. *)
  (*     iApply "HΦ". rewrite decide_False //. *)
  (*   - (* case: raft is done *) *)
  (*     repeat iExists _. iNamed "Hinner". *)
  (*     iApply (closeable_chan_receive with "Hdone"). *)
  (*     iIntros "[_ #HDone_closed]". wp_auto. wp_apply wp_globals_get. *)
  (*     iDestruct (is_pkg_init_access with "[$]") as "#Hpkg". *)
  (*     simpl is_pkg_init_def. iNamed "Hpkg". *)
  (*     wp_auto. *)
  (*     iApply "HΦ". rewrite decide_False //. *)
  (* } *)
  (* repeat iExists _. *)
  (* iSplitR; first done. *)
  (* (* case: send proposeMessage on propc *) *)
  (* (* TODO *) *)
Admitted.

End wps.
