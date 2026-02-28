Require Import New.proof.go_etcd_io.raft.v3_proof.protocol.

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
