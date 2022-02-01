(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program. *)
From Goose.github_com.mit_pdos.go_mvcc Require Import index.
From Perennial.program_proof.mvcc Require Import mvcc_ghost tuple_proof.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition is_index (idx : loc) (γ : mvcc_names) : iProp Σ := True.

Theorem wp_index__GetTuple idx (key : u64) γ :
  is_index idx γ -∗
  {{{ True }}}
    Index__GetTuple #idx #key
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
Admitted.
  
End heap.
