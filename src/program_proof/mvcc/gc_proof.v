From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost mvcc_inv mvcc_misc.
From Goose.github_com.mit_pdos.go_mvcc Require Import gc.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition is_gc (gc : loc) (γ : mvcc_names) : iProp Σ.
Admitted.

(*****************************************************************)
(* func MkGC() *GC                                               *)
(*****************************************************************)
Theorem wp_MkGC (idx : loc) γ :
  {{{ True }}}
    MkGC #idx
  {{{ (gc : loc), RET #gc; is_gc gc γ }}}.
Admitted.

End heap.
