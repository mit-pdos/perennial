From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__acquire txn γ τ :
  {{{ own_txn txn γ τ }}}
    Txn__acquire #txn
  {{{ (ok : bool), RET #ok;
      if ok then own_txn_ready txn γ τ else own_txn txn γ τ
  }}}.
Admitted.

End program.
