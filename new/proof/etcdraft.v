From New.code.go_etcd_io.raft Require Import v3.
Require Import New.generatedproof.go_etcd_io.raft.v3
  New.generatedproof.go_etcd_io.raft.v3.raftpb.
From New.proof Require Import grove_prelude.

Section proof.
Context `{!heapGS Σ}.

(* FIXME: move to builtin *)
Instance wp_int_gt (l r : w64) : PureWp True (int_gt #l #r) #(bool_decide (sint.Z l > sint.Z r)).
Proof. Admitted.

Instance wp_int_lt (l r : w64) : PureWp True (int_lt #l #r) #(bool_decide (sint.Z l < sint.Z r)).
Proof. Admitted.

End proof.
