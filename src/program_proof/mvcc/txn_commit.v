From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* TODO: the last case also needs [¬ Q r w].*)
Definition commit_false_cases γ : iProp Σ :=
  (∃ tid, nca_tids_frag γ tid) ∨
  (∃ tid, fa_tids_frag γ tid)  ∨
  (∃ tmods, fci_tmods_frag γ tmods) ∨
  (∃ tmods, fcc_tmods_frag γ tmods).

Theorem wp_txn__Commit_false txn tid γ τ :
  {{{ own_txn_ready txn tid γ τ ∗ commit_false_cases γ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; False }}}.
Admitted.

Theorem wp_txn__Commit txn tid tmods γ τ :
  {{{ own_txn_ready txn tid γ τ ∗ cmt_tmods_frag γ tmods }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; own_txn_uninit txn γ }}}.
Admitted.

End program.

Hint Extern 1 (environments.envs_entails _ (commit_false_cases _)) => unfold commit_false_cases : core.
