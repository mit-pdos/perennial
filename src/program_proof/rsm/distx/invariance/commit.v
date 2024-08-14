From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma resm_to_tmods_lookup_Some resm ts wrs :
  resm_to_tmods resm !! ts = Some wrs ->
  resm !! ts = Some (ResCommitted wrs).
Proof.
  intros Hresm.
  rewrite /resm_to_tmods lookup_omap in Hresm.
  destruct (resm !! ts) as [res |] eqn:Hres; last done.
  by destruct res as [wrsx |] eqn:Hwrsx; first inv Hresm.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  (**
   * The commit action modifies the following logical states in [txn_inv]:
   * 1. Result map [resm].
   * 2. Will-commit transaction map [tmodcs].
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

  Lemma txn_inv_commit γ tid wrs future :
    head future = Some (ActCmt tid wrs) ->
    txns_lnrz_receipt γ tid -∗
    all_prepared γ tid wrs -∗
    txn_inv_no_future γ future -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ==∗
    txn_inv_no_future γ (tail future) ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnres_cmt γ tid wrs.
  Proof.
    iIntros (Hhead) "#Htid #Hprep Htxnsys Hkeys".
    iNamed "Htxnsys".
    iDestruct (txns_lnrz_elem_of with "Htxnsl Htid") as %Htid.
    apply Hdest in Htid as Hcases.
    destruct Hcases as [[Hin Hnotin] | Hcases].
    { (* Case: Txn [tid] has already aborted or committed. *)
      rewrite elem_of_dom in Hin.
      destruct Hin as [wrsc Hwrs].
      apply resm_to_tmods_lookup_Some in Hwrs.
      iDestruct (big_sepM_lookup with "Hvr") as "#Hres"; first apply Hwrs.
      iAssert (⌜wrsc = wrs⌝)%I as %->.
      { iDestruct "Hres" as "[Hwrsc _]".
        iDestruct "Hprep" as "[Hwrs _]".
        by iDestruct (txnwrs_receipt_agree with "Hwrs Hwrsc") as %?.
      }
      (* Case: Txn [tid] has already committed. Extract a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Hcmt"; first apply Hwrs.
      unshelve epose proof (conflict_free_inv_commit_committed _ _ _ _ _ Hhead Hcf) as Hcf'.
      { apply not_elem_of_dom_1, Hnotin. }
      unshelve epose proof (conflict_past_inv_commit _ _ _ _ _ Hhead Hcp) as Hcp'.
      by iFrame "∗ # %".
    }
    destruct Hcases as [[Htmodas Hnotin] | [Htmodcs Hnotin]].
    { (* Case: Txn [tid] predicted to abort. Contradiction. *)
      (* Case A: [tid] not showing at all in [future] -> contradicting [Hhead]. *)
      (* Case B: [(tid, wrs)] conflicting with prior action -> add txnsys invs
      ReadLength and CommitLength and key inv constraining the length of
      replicated history with prepare timestamp. To show that [tid] is not
      committed nor aborted, we use [Hnotin] for the former, and
      [all_prepared_some_aborted_false] for the later. *)
      (* Case C: [(tid, wrs)] does not satisfy [P wrs]. Contradiction with
      additional premise. *)
      admit.
    }
  Admitted.

End inv.
