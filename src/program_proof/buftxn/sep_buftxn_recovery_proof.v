From Perennial.Helpers Require Import Map.
From iris.base_logic.lib Require Import mnat.
From Perennial.algebra Require Import auth_map liftable liftable2 log_heap async.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

Section goose_lang.
  Context `{!buftxnG Σ}.
  Context {N:namespace}.

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_init_ghost_state (logm_init: gmap addr object) γ : iProp Σ :=
    async_ctx γ.(buftxn_async_name) {| latest := logm_init; pending := [] |}.

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    is_txn_durable γ.(buftxn_txn_names) dinit ∗
    txn_resources γ.(buftxn_txn_names) logm ∗
    async_ctx γ.(buftxn_async_name) logm.

  Definition txn_cfupd_cancel dinit k γ' : iProp Σ :=
    (<disc> (|C={⊤}_k=>
              ∃ logm', is_txn_durable γ' dinit logm' )).

  Definition crash_point γ logm crash_txn : iProp Σ :=
    (* TODO: wrap crash_txn in an agree, give out an exchanger ghost name for
    it *)
    async_ctx γ.(buftxn_async_name) logm ∗
    ⌜length (possible logm) = crash_txn⌝.

  Definition addr_token_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    (∃ i, async.own_last_frag γ.(buftxn_async_name) a i) ∨
    (async.own_last_frag γ'.(buftxn_async_name) a crash_txn ∗ modify_token γ' a).

  (* TODO: exchange
  [ephemeral_txn_val crash_txn γ a v]
  for
  [ephemeral_txn_val crash_txn γ' a v]
   *)
  Definition ephemeral_txn_val_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    ∃ v, ephemeral_txn_val γ.(buftxn_async_name) crash_txn a v ∗
         ephemeral_txn_val γ'.(buftxn_async_name) crash_txn a v.

  Definition sep_txn_exchanger γ γ' : iProp Σ :=
    ∃ logm crash_txn,
       crash_point γ logm crash_txn ∗
       txn_durable γ' crash_txn ∗
       ([∗ map] a↦_ ∈ latest logm,
        addr_token_exchanger a crash_txn γ γ' ∗
        ephemeral_txn_val_exchanger a crash_txn γ γ')
  .

  Definition txn_cinv γ γ' : iProp Σ :=
    □ |C={⊤}_0=> inv (N.@"txn") (sep_txn_exchanger γ γ').

  Theorem wpc_MkTxn (d:loc) γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      txn.MkTxn #d @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(buftxn_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit k γ' ∗
        txn_cinv γ γ' }}}
    {{{ ∃ γ' logm', ⌜ γ'.(buftxn_txn_names).(txn_kinds) = γ.(buftxn_txn_names).(txn_kinds) ⌝ ∗
                   is_txn_durable γ' dinit logm' }}}.
  Proof.
  Abort.

End goose_lang.
