From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition abort_cases γ : iProp Σ :=
  (∃ tid, nca_tids_frag γ tid) ∨
  (∃ tid, fa_tids_frag γ tid)  ∨
  (∃ tmod, fci_tmods_frag γ tmod) ∨
  (∃ tmod, fcc_tmods_frag γ tmod).

Theorem wp_txn__Commit_false txn tid γ τ :
  {{{ own_txn_ready txn tid γ τ ∗ abort_cases γ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; False }}}.
Admitted.

Theorem wp_txn__Commit txn tid γ τ :
  {{{ own_txn_ready txn tid γ τ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; own_txn_uninit txn γ }}}.
Admitted.

End program.
