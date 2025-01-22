From New.proof Require Import proof_prelude.

Require Import New.generatedproof.structs.go_etcd_io.raft.v3.client.

Section specs.

Definition has_Put (kv : interface.t) : iProp Σ :=
  {{{ True }}}
    interface.get #kv
  {{{ RET #(); True }}}
.

End specs.
