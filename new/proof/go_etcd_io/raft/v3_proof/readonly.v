Require Import New.proof.go_etcd_io.raft.v3_proof.protocol.

(* Q: what's the invariant for MsgHeartbeat and MsgHeartbeatResp?
   Must ensure after getting MsgHeartbeatResp, the follower was still in the
   leader's term at some point *after* the MsgHeartbeat was created.

   Potentially provable spec: associated to each pair (heartbeat ctx, nodeId),
   there can be a (persistent) atomic update that gets temporary access to
   ownership of the nodeId's latest term being equal to the leader's term.

   This, combined with some raft invariants, will imply that the committed log
   (onto which the ReadState AU was placed) contains that node's log.
   Importantly, the ONLY node that should commit entries should be the leader.
   Otherwise, something might be committed and made visible to clients, without
   the leader knowing it.

   Q: what's the invariant for readOnly? Must imply that receiving heartbeats
   for the last entry implies the earlier entries are OK too. *)
