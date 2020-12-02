From Perennial.Helpers Require Import Map.
From iris.base_logic.lib Require Import mnat.
From Perennial.algebra Require Import auth_map liftable liftable2 log_heap async.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_invariant.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

Section goose_lang.
  Context `{!buftxnG Σ}.
  Context {N:namespace}.

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_init_ghost_state (logm_init: gmap addr object) γ : iProp Σ :=
    async_ctx γ.(buftxn_async_name) 1 {| latest := logm_init; pending := [] |}.

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    is_txn_durable γ.(buftxn_txn_names) dinit ∗
    txn_resources γ.(buftxn_txn_names) logm ∗
    async_ctx γ.(buftxn_async_name) 1 logm.

  Definition txn_cfupd_cancel dinit k γ' : iProp Σ :=
    (<disc> (|C={⊤}_k=>
              ∃ logm', is_txn_durable γ' dinit logm' )).



  Theorem wpc_MkTxn (d:loc) γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      txn.MkTxn #d @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(buftxn_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit k γ' ∗
        txn_cinv N γ γ' }}}
    {{{ ∃ γ' logm', ⌜ γ'.(buftxn_txn_names).(txn_kinds) = γ.(buftxn_txn_names).(txn_kinds) ⌝ ∗
                   is_txn_durable γ' dinit logm' }}}.
  Proof.
  Abort.

End goose_lang.
