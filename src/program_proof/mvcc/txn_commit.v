From Perennial.program_proof.mvcc Require Import proph_proof txn_common txn_apply txnmgr_deactivate.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(**
 * Proof plan:
 * 1. Prove FCC
 * 2. Define [ptuple_past_rel]
 * 3. Prove FCI
 * 4. Prove CMT (incl. tuple-write safe extension)
 * 5. Prove tuple-read safe extension
 *)

Definition commit_false_cases tid r γ τ : iProp Σ :=
  (nca_tids_frag γ tid) ∨
  (fa_tids_frag γ tid)  ∨
  (∃ mods, fci_tmods_frag γ (tid, mods)) ∨
  (∃ mods w Q, fcc_tmods_frag γ (tid, mods) ∗ txnmap_ptstos τ w ∗
               ⌜Q r w ∧ ¬ Q r (mods ∪ r) ∧ dom w = dom r⌝).

Theorem wp_txn__Commit_false txn tid view γ τ :
  {{{ own_txn_ready txn tid view γ τ ∗ commit_false_cases tid view γ τ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; False }}}.
Proof.
  iIntros (Φ) "[Htxn Hfrag] HΦ".
  wp_call.

  (***********************************************************)
  (* proph.ResolveCommit(txn.txnMgr.p, txn.tid, txn.wrbuf)   *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 4 wp_loadField.
  wp_apply (wp_ResolveCommit with "[$HwrbufRP]"); first eauto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hfuture & Hproph)".

  (* Obtain contradiction for each case. *)
  unfold commit_false_cases.
  iDestruct "Hfrag" as "[HncaFrag | Hfrag]".
  { (* Case NCA. *)
    iNamed "Hnca".
    iDestruct (nca_tids_lookup with "HncaFrag HncaAuth") as "%Helem".
    apply Hnca in Helem.
    destruct (no_commit_abort_false Helem).
    left.
    set_solver.
  }
  iDestruct "Hfrag" as "[HfaFrag | Hfrag]".
  { (* Case FA. *)
    iNamed "Hfa".
    iDestruct (fa_tids_lookup with "HfaFrag HfaAuth") as "%Helem".
    apply Hfa in Helem.
    destruct (first_abort_false mods Helem).
    set_solver.
  }
  iDestruct "Hfrag" as "[HfciFrag | HfccFrag]".
  { (* Case FCI. *)
    iNamed "Hfci".
    iDestruct "HfciFrag" as (mods') "HfciFrag".
    iDestruct (fci_tmods_lookup with "HfciFrag HfciAuth") as "%Helem".
    apply Hfci in Helem. simpl in Helem.
    (* Obtain contradiction by length of physical tuple. *)
    pose proof Helem as Hfci'.
    apply hd_error_tl_repr in Hfuture as [Hhead _].
    destruct Helem as (lp & ls & Hfc & Hincomp).
    pose proof (first_commit_eq Hfc Hhead) as Emods.
    subst mods'.
    destruct (Exists_incompatible_exists past tid mods) as (key & tid' & H).
    { apply first_commit_incompatible_Exists with future; auto. }
    (* Get the invariant for [key] from which we obtain contradiction. *)
    iDestruct (big_sepS_elem_of _ _ key with "Hkeys") as "Hkey"; first set_solver.
    iNamed "Hkey".
    unfold ptuple_past_rel in Hpprel.
    rewrite Forall_forall in Hpprel.
    destruct H as [Helem H].
    iDestruct (big_sepM_lookup_dom with "Htuples") as "Htuple".
    { by apply elem_of_dom in Helem. }
    iRename "Hptuple" into "Hptuple'".
    iNamed "Htuple".
    iDestruct (ptuple_agree with "Hptuple Hptuple'") as "->".
    destruct H as [H | H].
    - (* Case EvRead. *)
      destruct H as [Hact Hlt].
      apply Hpprel in Hact. simpl in Hact.
      (* The following also do the work. *)
      (* specialize (Hact eq_refl). *)
      (* specialize (Hact ltac:(auto)). *)
      unshelve epose proof (Hact _); first reflexivity.
      replace (int.nat _) with tid in Hlen by word.
      lia.
    - (* Case EvCommit. *)
      destruct H as (mods' & Helem' & Hact & Hle).
      apply Hpprel in Hact. simpl in Hact.
      unshelve epose proof (Hact _); first auto.
      replace (int.nat _) with tid in Hlen by word.
      lia.
  }
  { (* Case FCC. *)
    iNamed "Hfcc".
    iDestruct "HfccFrag" as (mods' w Q) "(HfccFrag & Htxnps & %HQ & %HnotQ & %Hdom)".
    iDestruct (fcc_tmods_lookup with "HfccFrag HfccAuth") as "%Helem".
    apply Hfcc in Helem. simpl in Helem.
    (* Obtain equality between [mods] (in proph) and [mods'] (in evidence). *)
    destruct Helem as (lp & ls & Hfc & Hcomp).
    apply hd_error_tl_repr in Hfuture as Hhdtl.
    destruct Hhdtl as [Hhead _].
    pose proof (first_commit_eq Hfc Hhead) as Emods.
    subst mods'.
    (* Obtain contradiction from [Q r w] and [¬ Q r w]. *)
    iDestruct (txnmap_lookup_big with "Htxnmap Htxnps") as "%Hw".
    assert (Hviewdom : dom view = dom (mods ∪ view)) by set_solver.
    rewrite Hviewdom in Hdom.
    symmetry in Hdom.
    pose proof (Map.map_subset_dom_eq _ _ _ _ Hdom Hw) as H.
    by subst w.
  }
Qed.

Definition ptuple_extend_wr_pre γ tmods ts m past (tid : nat) k : iProp Σ :=
  per_key_inv_def γ k tmods ts m past ∗
  ∃ tuple phys, own_tuple_locked tuple k tid phys phys γ.

Definition ptuple_extend_wr_post γ tmods ts m past (tid : nat) mods k v : iProp Σ :=
  per_key_inv_def γ k (tmods ∖ {[ (tid, mods) ]}) ts m (past ++ [EvCommit tid mods]) ∗
  ∃ tuple phys, own_tuple_locked tuple k tid phys (extend (S tid) phys ++ [v]) γ.

Local Lemma per_key_inv_bigS_disj {γ keys tmods ts m past} tid mods :
  keys ## dom mods ->
  ([∗ set] k ∈ keys, per_key_inv_def γ k tmods ts m past) -∗
  ([∗ set] k ∈ keys, per_key_inv_def γ k (tmods ∖ {[ (tid, mods) ]}) ts m (past ++ [EvCommit tid mods])).
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros "%Hdisj Hkeys".
  iApply (big_sepS_mono with "Hkeys").
  iIntros (k) "%Helem Hkey".
  iApply per_key_inv_past_commit_disj; first set_solver.
  by iApply per_key_inv_tmods_minus_disj; first set_solver.
Qed.

Theorem ptuple_extend_wr γ tmods ts m past tid mods k v :
  (tid, mods) ∈ tmods ->
  le_tids_mods tid (per_tuple_mods tmods k) ->
  mods !! k = Some v ->
  ptuple_extend_wr_pre γ tmods ts m past tid k ==∗
  ptuple_extend_wr_post γ tmods ts m past tid mods k v.
Proof.
  iIntros "%Helem %Hlookup %Hle [Hkey Htuple]".
  iNamed "Hkey".
  iRename "Hptuple" into "Hptuple'".
  iNamed "Htuple".
  unfold ptuple_extend_wr_post.
  iDestruct (ptuple_agree with "Hptuple Hptuple'") as %->.
  set phys' := extend (S tid) phys ++ [v].
  iMod (vchain_update phys' with "Hptuple Hptuple'") as "[Hptuple Hptuple']".
  { apply prefix_app_r, extend_prefix. }
  iModIntro.
  iSplitL "Hptuple Hltuple".
  { do 2 iExists _.
    iFrame "∗ %".
    iPureIntro.
    split.
    { (* Prove [tuple_mods_rel]. *)
      rewrite (per_tuple_mods_minus v); last done.
      apply tuplext_write; [done | by apply (mods_global_to_tuple mods) | done].
    }
    { (* Prove [ptuple_past_rel]. *)
      apply ptuple_past_rel_commit_lt_len.
      { subst phys'.
        rewrite app_length.
        rewrite extend_length; last by eapply tuple_mods_rel_last_phys.
        simpl. lia.
      }
      apply ptuple_past_rel_extensible with phys; last done.
      apply prefix_app_r, extend_prefix.
    }
  }
  do 6 iExists _.
  iFrame "∗ %".
Qed.

Theorem ptuples_extend_wr {γ} tmods ts m past tid mods :
  (tid, mods) ∈ tmods ->
  set_Forall (λ key : u64, le_tids_mods tid (per_tuple_mods tmods key)) (dom mods) ->
  ([∗ map] k ↦ _ ∈ mods, ptuple_extend_wr_pre γ tmods ts m past tid k) ==∗
  ([∗ map] k ↦ v ∈ mods, ptuple_extend_wr_post γ tmods ts m past tid mods k v).
Proof.
  iIntros "%Helem %Hleall Hpre".
  iApply big_sepM_bupd.
  iApply (big_sepM_mono with "Hpre").
  iIntros (k v) "%Hlookup Hpre".
  iApply (ptuple_extend_wr with "Hpre"); [done | | done].
  apply Hleall.
  by eapply elem_of_dom_2.
Qed.

Theorem wp_txn__Commit txn tid view mods γ τ :
  {{{ own_txn_ready txn tid view γ τ ∗ cmt_tmods_frag γ (tid, mods) }}}
    Txn__Commit #txn
  {{{ RET #(); own_txn_uninit txn γ }}}.
Proof.
  iIntros (Φ) "[Htxn Hfrag] HΦ".
  wp_call.

  (***********************************************************)
  (* proph.ResolveCommit(txn.txnMgr.p, txn.tid, txn.wrbuf)   *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 4 wp_loadField.
  wp_apply (wp_ResolveCommit with "[$HwrbufRP]"); first eauto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hfuture & Hproph)".

  iNamed "Hcmt".
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  (* Obtain equality between [mods] and [mods0] using [Helem] and [Hhead]. *)
  apply Hcmt in Helem. simpl in Helem.
  destruct Helem as (lp & ls & Hfc & Hcomp).
  apply hd_error_tl_repr in Hfuture as Hhdtl.
  destruct Hhdtl as [Hhead _].
  pose proof (first_commit_eq Hfc Hhead) as Emods.
  subst mods0.
  (* Separate out the per-key invariant for keys modified by this txn. *)
  set keys := dom mods.
  rewrite (union_difference_L keys keys_all); last set_solver.
  rewrite big_sepS_union; last set_solver.
  iDestruct "Hkeys" as "[Hkeys HkeysDisj]".
  rewrite -big_sepM_dom.
  (* Combine [Htuples] (the tuple physical + logical state), and [Hkeys] (per-key inv). *)
  iDestruct (big_sepM_sep_2 with "Hkeys Htuples") as "H".
  (* Extend physical tuples. *)
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  pose proof (fcc_head_commit_le_all _ _ _ _ Hcmt Hhead) as Hdomle.
  iMod (ptuples_extend_wr with "H") as "H"; [done | done |].
  iDestruct (big_sepM_sep with "H") as "[Hkeys Htuples]".
  rewrite big_sepM_dom.
  (* Update [HkeysFix] w.r.t. to [tmods ∖ {[ (tid, mods) ]}] and [past ++ [EvCommit tid mods]]. *)
  iDestruct (per_key_inv_bigS_disj tid mods with "HkeysDisj") as "HkeysDisj"; first set_solver.
  iDestruct (big_sepS_union_2 with "Hkeys HkeysDisj") as "Hkeys".
  replace (_ ∪ _ ∖ _) with keys_all; last first.
  { apply union_difference_L. set_solver. }

  (* TODO: Update [Hnca Hfa Hfci Hfcc] to re-establish inv w.r.t. [future']. *)
  iDestruct (nca_inv_any_action with "Hnca") as "Hnca"; first apply Hfuture.
  iDestruct (fa_inv_diff_action with "Hfa") as "Hfa"; [apply Hfuture | done |].
  iDestruct (fci_inv_diff_action with "Hfci") as "Hfci"; [apply Hfuture | admit |].
  iDestruct (fcc_inv_diff_action with "Hfcc") as "Hfcc"; [apply Hfuture | admit |].
  iMod (cmt_inv_same_action with "Hfrag [$HcmtAuth]") as "Hcmt"; [apply Hfuture | admit | done |].
  (* Close the invariant. *)
  iMod "Hclose" as "_".
  iMod ("HinvC" with "[Hproph Hts Hm Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { by eauto 15 with iFrame. }
  iIntros "!> HwrbufRP".
  wp_pures.

  (***********************************************************)
  (* txn.apply()                                             *)
  (***********************************************************)
  wp_apply (wp_txn__apply with "[- HΦ]").
  { iExists _.
    iFrame "∗ #".
    iSplit; last done.
    eauto 20 with iFrame.
  }
  iIntros "Htxn".
  wp_pures.

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
  iClear "#".
  iNamed "Htxn".
  iNamed "Himpl".
  do 3 wp_loadField.
  wp_apply (wp_txnMgr__deactivate with "HtxnmgrRI Hactive").
  wp_pures.
  iApply "HΦ".
  eauto 20 with iFrame.
Admitted.

End program.

#[global]
Hint Extern 1 (environments.envs_entails _ (commit_false_cases _ _ _ _)) => unfold commit_false_cases : core.
