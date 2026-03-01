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
    read_reqs_gn : gname;
    read_wits_gn : gname;
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

Definition is_read_req γ read_req_ctx index : iProp Σ :=
  read_req_ctx ↪[γ.(read_reqs_gn)]□ index.
Definition own_read_reqs γ (read_reqs : gmap go_string w64) : iProp Σ :=
  ghost_map_auth γ.(read_reqs_gn) 1 read_reqs.

Definition is_read_wit γ read_req_ctx log : iProp Σ :=
  (read_req_ctx, log) ↪[γ.(read_wits_gn)]□ ().

(** Propositions defined in terms of the primitive ghost state. *)

(* This proof assumes there's only one configuration (for now). *)
Context (cfg : gset w64).

Axiom own_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.
Axiom is_committed_in_term : ∀ γ (term : w64) (log : list $ list w8), iProp Σ.

Definition is_stale_term γ term : iProp Σ :=
  ∃ quorum,
    "%Hquorum" ∷ ⌜ quorum ⊆ cfg ∧ size cfg < 2 * size quorum ⌝ ∗
    "#Hterm_lbs" ∷
      □(∀ node_id (Hin_quorum : node_id ∈ quorum),
         ∃ term', is_term_lb γ node_id term' ∗ ⌜ sint.nat term < sint.nat term' ⌝).

(* TODO: maybe instead of arbitary continuations, could set up proof in terms of
   linearization order of ALL ops, including reads. *)

Definition Ncommit := N.@"commit".
(* FIXME: this invariant should not even know about read_req_ctx. Either use a
   purely ghost ID for the aus, or direct higher order ghost state for the
   au continuation Φ. *)
Definition is_raft_commit_inv γ : iProp Σ :=
  inv Ncommit (∃ term log read_reqs,
        "commit" ∷ own_commit_auth γ log ∗
        "read" ∷ own_read_reqs γ read_reqs ∗
        "Hcommit" ∷ is_committed_in_term γ term log ∗
        (* Permission to linearize eads on all future logs. *)
        "#Hread_aus" ∷ □(∀ read_req_ctx (Hin : read_req_ctx ∈ dom read_reqs) log,
                           own_commit_auth γ log ={⊤∖↑N}=∗
                           own_commit_auth γ log ∗ is_read_wit γ read_req_ctx log) ∗
        (* Witnesses that reads were linearized on every index starting at
           the one in `read_reqs`. *)
        "#Hread_wits" ∷ □(∀ read_req_ctx index (Hindex : read_reqs !! read_req_ctx = Some index)
                            index' (Hindex' : sint.nat index ≤ sint.nat index' ≤ length log),
                            is_read_wit γ read_req_ctx (take (sint.nat index') log))
    ).

Definition is_read_valid γ index Φ : iProp Σ :=
  ∀ log (Hin : sint.nat index ≤ length log) E (Hmask : ↑N ⊆ E),
  is_commit γ log ={E}=∗ Φ log.

Lemma maybe_commit_read [E] index γ term log Φ :
  ↑N ⊆ E →
  sint.nat index = length log →
  "#Hinv" ∷ is_raft_commit_inv γ ∗
  "Hcom" ∷ own_committed_in_term γ term log ∗
  "#Hau" ∷ □(|={⊤∖↑N,∅}=> own_commit γ log ∗ (own_commit γ log ={∅,⊤∖↑N}=∗ Φ log))
  ={E}=∗
  own_committed_in_term γ term log ∗ (is_read_valid γ index Φ ∨ is_stale_term γ term).
Proof.
  intros. iNamed 1.
Admitted.

End global_proof.
