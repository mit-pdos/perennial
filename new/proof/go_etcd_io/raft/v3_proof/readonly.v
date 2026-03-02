From iris.algebra.lib Require Import mono_nat.
Require Import New.proof.go_etcd_io.raft.v3_proof.protocol.
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

(* Q: what's the invariant for MsgHeartbeat and MsgHeartbeatResp?
   Must ensure after getting MsgHeartbeatResp, the follower was still in the
   leader's term at some point *after* the MsgHeartbeat was created.

   Potentially provable spec: associated to each pair (heartbeat ctx, nodeId),
   there can be a (persistent) atomic update that gets temporary access to
   ownership of the nodeId's latest term being equal to the leader's term.

   This, combined with some assumed raft invariants, will imply that the
   committed log (onto which the ReadState AU was placed) contains that node's
   log.  Importantly, the ONLY node that should commit entries should be the
   leader.  Otherwise, something might be committed and made visible to clients,
   without the leader knowing it. Part of the reason to commit a noop entry is
   so that the leader actually knows about something committed in its term, so
   the above argument works.

   Q: what's the invariant for readOnly? Must imply that receiving heartbeats
   for the last entry implies the earlier entries are OK too.
   A: There is no invariant implying the earlier entries are OK because the code
   is buggy: https://github.com/etcd-io/etcd/issues/20418#issuecomment-3974901065
   The problem is that network retries mean that old ReadIndex requests might
   get queued *after* new ReadIndex requests. The new ReadIndex request might
   have started after the current node was not the latest leader, but the old
   ReadIndex might have valid heartbeat responses. Thus, when `raft.readOnly`
   validates the entire queue up to a valid entry, it might validate a stale
   read index for a recent request.

   Related raft issue (with test case linked):
   https://github.com/etcd-io/raft/issues/392

   TODO: prove fixed version of raft libary
   TODO: prove weaker spec for existing raft library, to justify backportable
   fix to etcd. In particular, if `ReadIndex` is only called once (i.e. if each
   `MsgReadIndex` comes with an exclusive ghost token), then should be able to
   create a monolist of RequestCtxes in the proof, such that if any RequestCtx
   is validated, then all the RequestCtxes before are also valid (i.e. were
   up-to-date when created).

   Can probably avoid prophecy variables by having spec for creating a
   RequestCtx guarantee: "valid(index, request_ctx) ∨ node is no longer leader".
   "valid(index, request_ctx)" means that `request_ctx`'s persistent AU is
   registered for (re)execution at some index `j` and `j ≤ index`.
 *)

Record raft_names :=
  {
    commited_gn : gname;
    prop_gn : gname;
    term_gn : gname;
    config_gn : gname;
    reads_gn : gname;
  }.

Section global_proof.

Implicit Types (γ : raft_names) (log : list (list w8)) (node_id term index : w64)
               (read_req_ctx : go_string).

Context `{!invGS Σ} `{!allG Σ}.
Context (N : namespace).

(** Ghost state for raft protocol *)
Definition own_commit_auth γ log := mono_list_auth_own γ.(commited_gn) (1/2) log.
Definition own_commit γ log := mono_list_auth_own γ.(commited_gn) (1/2) log.
Definition is_commit γ log := mono_list_lb_own γ.(commited_gn) log.

Definition own_term γ node_id term := own γ.(term_gn) {[ node_id := ●MN (sint.nat term) ]}.
Definition is_term_lb γ node_id term := own γ.(term_gn) {[ node_id := ◯MN (sint.nat term) ]}.

Definition is_γread_index γ (γread : gname) index : iProp Σ :=
  γread ↪[γ.(reads_gn)]□ index.
Definition own_read_reqs γ (reads_index : gmap gname w64) : iProp Σ :=
  ghost_map_auth γ.(reads_gn) 1 reads_index.

Definition is_read_wit γread log : iProp Σ :=
  log ↪[γread]□ ().

(** Propositions defined in terms of the primitive ghost state. *)

(* This proof assumes there's only one configuration (for now). *)
Context (cfg : gset w64).

Axiom own_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term_pers : ∀ γ term log, Persistent (is_committed_in_term γ term log).
Global Existing Instance is_committed_in_term_pers.

Definition is_stale_term γ term : iProp Σ :=
  ∃ quorum,
    "%Hquorum" ∷ ⌜ quorum ⊆ cfg ∧ size cfg < 2 * size quorum ⌝ ∗
    "#Hterm_lbs" ∷
      □(∀ node_id (Hin_quorum : node_id ∈ quorum),
         ∃ term', is_term_lb γ node_id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

(* TODO: maybe instead of arbitary continuations, could set up proof in terms of
   linearization order of ALL ops, including reads. *)

(* The "positive" resource precluding is_stale_term perhaps should be up to an index.

  Actually, it won't work to have
    `is_readonly_ack γ term index node_id`,
  plus a lemma
    `∀ Q, is_quorum Q ∧ (∀ node_id, node_id ∈ Q → is_readonly_ack γ term index node_id) →
     is_read_safe γ index`
  because there's no connection to the req_ctx; the index is NOT unconditionally
  safe, it's only safe for the request ctx.

  And, if we add a request ctx, there's no need to have the index. Instead, the meaning of
  `MsgHeartbeatResp(from=i, ctx=A)` is the persistent fact that `i` is not in
  the set of "deniers" for `A`; a "denier" is a node that's part of the staleness quorum.
 *)

(* TODO: what happens if raft reuses request_ctx across terms? There might be a
   different staleness quorum for a later term. Maybe staleness quorum is per
   (term, req_ctx) pair. *)

Definition Ncommit := N.@"commit".
Definition is_raft_commit_inv γ : iProp Σ :=
  inv Ncommit (∃ term log reads_index,
        "commit" ∷ own_commit_auth γ log ∗
        "#Hcommit" ∷ is_committed_in_term γ term log ∗
        "read" ∷ own_read_reqs γ reads_index ∗
        (* Permission to linearize reads on all future logs. *)
        "#Hread_aus" ∷ □(∀ γread (Hin : γread ∈ dom reads_index) log,
                           own_commit_auth γ log ={⊤∖↑N}=∗
                           own_commit_auth γ log ∗ is_read_wit γread log) ∗
        (* Witnesses that reads were linearized on every index starting at
           the one in `read_reqs`. *)
        "#Hread_wits" ∷ □(∀ γread index (Hindex : reads_index !! γread = Some index)
                            index' (Hindex' : sint.nat index ≤ sint.nat index' ≤ length log),
                            is_read_wit γread (take (sint.nat index') log))
    ).

Axiom own_read_req_ctx : ∀ γ read_req_ctx, iProp Σ.
Axiom is_read_req_ctx : ∀ γ read_req_ctx (Φ : list (list w8) → iProp Σ), iProp Σ.

Lemma start_req_ctx Φ req_ctx index γ :
  own_read_req_ctx γ req_ctx ∗
  □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ Φ log))
  ={⊤}=∗
  is_read_req_ctx γ req_ctx Φ.
Proof.
Admitted.

Definition is_read_index γ index Φ : iProp Σ :=
  ∀ log (Hin : sint.nat index ≤ length log) E (Hmask : ↑N ⊆ E),
  is_commit γ log ={E}=∗ Φ log.

Lemma maybe_commit_read [E] γ term log Φ :
  ↑N ⊆ E →
  "#Hinv" ∷ is_raft_commit_inv γ ∗
  "Hcom" ∷ own_committed_in_term γ term log ∗
  "#Hau" ∷ □(|={⊤∖↑N,∅}=> ∃ log, own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ Φ log))
  ={E}=∗
  own_committed_in_term γ term log ∗ (is_read_index γ (W64 (length log)) Φ ∨ is_stale_term γ term).
Proof.
  intros. iNamed 1.
Admitted.

Definition is_MsgReadIndex γ read_req_ctx : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ.

Definition is_MsgReadIndexResp γ read_req_ctx index : iProp Σ :=
  ∃ Φ, is_read_req_ctx γ read_req_ctx Φ ∗
       is_read_index γ index Φ.

End global_proof.

Section wps.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

Axiom own_raft : ∀ (γ : raft_names) (rf : raft.raft.t), iProp Σ.

(* FIXME: own_ProgressTracker precondition *)
Lemma wp_ProgressTracker__IsSingleton (p : loc) :
  {{{ True }}}
    p @! (go.PointerType tracker.ProgressTracker) @! "IsSingleton" #()
  {{{ RET #false; True }}}.
Proof.
Admitted.

Lemma wp_raft__committedEntryInCurrentTerm r rf γ :
  {{{ r ↦ rf ∗ own_raft γ rf }}}
    r @! (go.PointerType raft.raft) @! "committedEntryInCurrentTerm" (# ())
  {{{ (c : bool), RET #c; r ↦ rf ∗ own_raft γ rf ∗
                 if c then ∃ l, is_committed_in_term γ rf.(raft.raft.Term') l else True
  }}}.
Proof.
Admitted.

Definition MsgReadIndex := W32 15.
Lemma wp_raft__sendMsgReadIndexresponse γ r rf m :
  {{{ "Hr" ∷ r ↦ rf ∗
      "Hrf" ∷ own_raft γ rf ∗
      "%HmType" ∷ ⌜ m.(raftpb.Message.Type') = MsgReadIndex ⌝ ∗
      "#Hcom_in_term" ∷ True
  }}}
    @! raft.sendMsgReadIndexResponse #r #m
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre". wp_auto.
Admitted. (* TODO *)

Lemma wp_raft__stepLeader_MsgReadIndex γ r (rf : raft.raft.t) (m : raftpb.Message.t) :
  {{{ "Hr" ∷ r ↦ rf ∗
      "Hrf" ∷ own_raft γ rf ∗
      "%HmType" ∷ ⌜ m.(raftpb.Message.Type') = MsgReadIndex ⌝ }}}
    @! raft.stepLeader #r #m
  {{{ RET #(); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto. rewrite HmType.
  wp_auto.
  wp_apply wp_ProgressTracker__IsSingleton.
  wp_apply (wp_raft__committedEntryInCurrentTerm with "[$]").
  iIntros "%committedInTerm (Hr & Hrf & Hcom)".
  wp_if_destruct.
  - admit.
Admitted.

End wps.
