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
   A: There is no invariant; the code is buggy:
   https://github.com/etcd-io/etcd/issues/20418#issuecomment-3974901065
   The problem is that retries mean that old ReadIndex requests might get queued
   *after* new ReadIndex requests. The new ReadIndex request might have started
    after the current node was not the latest leader, but the old ReadIndex
    might have valid heartbeat responses. Thus, when `raft.readOnly` validates
    the entire queue up to a valid entry, it might validate a stale read index
    for a recent request. *)
