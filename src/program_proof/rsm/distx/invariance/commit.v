From Perennial.program_proof.rsm.distx Require Import prelude.

Section inv.
  Context `{!distx_ghostG Σ}.

  (**
   * The commit action modifies the following logical states in [txn_inv]:
   * 1. Result map [resm].
   * 2. Will-commit transaction map [txns_cmt].
   * 3. Key modification map by committed txns [kmodcs].
   * 4. Key modification map by linearized txns [kmodls].
   * Invariants to re-establish:
   * 1. Committed implies prepared [Hcip].
   * 2. Consistency between result map and committed kmod map [Htkcc].
   * 3. Consistency between result map and linearized kmod map [Htkcl].
   * 4. Conflict free [Hcf].
   *
   * And the following logical states in [key_inv]:
   * 1. Committed history [cmtd].
   * 2. Key modification by committed txns [kmodc].
   * 3. Key modification by linearized txns [kmodl].
   * Invariants to re-establish:
   * 1. Committed history is a prefix of linearized history [Hprefix].
   * 2. Difference between linearized and committed histories [Hdiffl].
   * 3. Difference between committed and replicated histories [Hdiffc].
   * 4. Not written at timestamp 0 [Hzrsv].
   *
   * It seems like we're missing an invariant that proves the committing
   * transaction must have linearized. We might want to add something like
   * prepared-implies-linearized-or-finalized.
   *)

  Lemma txn_inv_commit γ ts wrs :
    txnwrs_receipt γ ts wrs -∗
    all_prepared γ ts (dom wrs) -∗
    txn_inv γ -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ==∗
    txn_inv γ ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnres_cmt γ ts wrs.
  Proof.
  Admitted.

End inv.
