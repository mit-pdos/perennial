From Perennial.program_proof.mvcc Require Import txn_prelude txn_repr.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__acquire txn tid view γ τ :
  {{{ own_txn txn tid view γ τ }}}
    Txn__acquire #txn
  {{{ (ok : bool), RET #ok;
      if ok then own_txn_ready txn tid view γ τ else own_txn txn tid view γ τ
  }}}.
Admitted.

End program.
