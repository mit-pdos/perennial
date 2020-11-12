From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Import txn.invariant.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{!txnG Σ}.

(* TODO: set up crash_obligation_alt for txn *)

(* Definitely missing the durable invariant of the heapspec layer, which should
say something more complete about [γ.(txn_walnames)]. Otherwise there probably
isn't enough to relate the state inside [is_txn_always] to that in
[is_wal_inner_durable]. *)
Theorem wp_MkTxn (d:loc) σ dinit (γ:txn_names) :
  {{{ is_wal_inner_durable γ.(txn_walnames).(wal_heap_walnames) σ dinit ∗
      is_txn_always γ
  }}}
    MkTxn #d
  {{{ (l: loc) (γ':txn_names), RET #l; is_txn l γ' dinit }}}.
Proof.
Admitted.

End goose_lang.
