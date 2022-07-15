(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export grove_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import gc.
From Perennial.program_proof.mvcc Require Import mvcc_ghost index_proof.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition is_gc (gc : loc) (γ : mvcc_names) : iProp Σ := True.

(*****************************************************************)
(* func MkGC() *GC                                               *)
(*****************************************************************)
Theorem wp_MkGC (idx : loc) γ :
  {{{ True }}}
    MkGC #idx
  {{{ (gc : loc), RET #gc; is_gc gc γ }}}.
Admitted.

End heap.
