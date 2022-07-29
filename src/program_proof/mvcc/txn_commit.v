From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__Commit_false txn γ τ :
  {{{ own_txn_ready txn γ τ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; False }}}.
Admitted.

Theorem wp_txn__Commit txn γ τ :
  {{{ own_txn_ready txn γ τ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; own_txn_uninit txn γ }}}.
Admitted.

End program.
