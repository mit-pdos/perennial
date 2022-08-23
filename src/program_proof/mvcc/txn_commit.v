From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr tuple_repr
     txnmgr_deactivate
     wrbuf_repr wrbuf_update_tuples
     proph_proof.

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
               ⌜Q r w ∧ ¬ (Q r (mods ∪ r) ∧ dom mods ⊆ dom r) ∧ dom w = dom r⌝).

Theorem wp_txn__Commit_false txn tid r γ τ :
  {{{ own_txn_ready txn tid r γ τ ∗ commit_false_cases tid r γ τ }}}
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
  iDestruct (own_wrbuf_mods_tpls_dom with "HwrbufRP") as "%Hdoms".
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
    rewrite Hdoms in Helem.
    apply elem_of_dom in Helem.
    destruct Helem as [tpl Hlookup].
    iDestruct (big_sepM_lookup with "Htuples") as "Htuple"; first apply Hlookup.
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
    iDestruct "HfccFrag" as (mods' w Q) "(HfccFrag & Htxnps & %HQ & %contra & %Hdom)".
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
    assert (Hrdom : dom r = dom (mods ∪ r)) by set_solver.
    rewrite Hrdom in Hdom.
    symmetry in Hdom.
    pose proof (Map.map_subset_dom_eq _ _ _ _ Hdom Hw) as H.
    rewrite not_and_r in contra.
    destruct contra; [by subst w | done].
  }
Qed.

Definition ptuple_extend_wr_pre γ tmods ts m past (tid : nat) k tpl : iProp Σ :=
  per_key_inv_def γ k tmods ts m past ∗
  ∃ phys, own_tuple_locked tpl k tid phys phys γ.

Definition ptuple_extend_wr_post γ tmods ts m past (tid : nat) mods k tpl v : iProp Σ :=
  per_key_inv_def γ k (tmods ∖ {[ (tid, mods) ]}) ts m (past ++ [EvCommit tid mods]) ∗
  ∃ phys, own_tuple_locked tpl k tid phys (extend (S tid) phys ++ [v]) γ.

#[local]
Lemma per_key_inv_bigS_disj {γ keys tmods ts m past} tid mods :
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

#[local]
Lemma ptuple_extend_wr γ tmods ts m past tid mods k tpl v :
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  le_tids_mods tid (per_tuple_mods tmods k) ->
  mods !! k = Some v ->
  ptuple_extend_wr_pre γ tmods ts m past tid k tpl ==∗
  ptuple_extend_wr_post γ tmods ts m past tid mods k tpl v.
Proof.
  iIntros "%HND %Helem %Hlookup %Hle [Hkey Htuple]".
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
      rewrite (per_tuple_mods_minus_Some v); [ | done | done | done].
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
  do 5 iExists _.
  iFrame "∗ %".
Qed.

Lemma big_sepM2_bupd :
  ∀ (PROP : bi) (H : BiBUpd PROP) (A B K : Type) (EqDecision0 : EqDecision K) (H0 : Countable K) 
    (Φ : K → A -> B → PROP) (l1 : gmap K A) (l2 : gmap K B),
  ([∗ map] k↦x;y ∈ l1;l2, |==> Φ k x y) -∗ |==> [∗ map] k↦x;y ∈ l1;l2, Φ k x y.
Admitted.

(* [big_sepM2_dom] is used for something else. *)
Lemma big_sepM2_dom' :
  ∀ (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K) (A B : Type)
    (Φ : K → PROP) (m1 : gmap K A) (m2 : gmap K B),
  ([∗ map] k↦_;_ ∈ m1;m2, Φ k) ⊣⊢ ([∗ set] k ∈ dom m1, Φ k).
Admitted.

#[local]
Lemma ptuples_extend_wr {γ} tmods ts m past tid mods tpls :
  dom mods = dom tpls ->
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  set_Forall (λ key : u64, le_tids_mods tid (per_tuple_mods tmods key)) (dom mods) ->
  ([∗ map] k ↦ tpl ∈ tpls, ptuple_extend_wr_pre γ tmods ts m past tid k tpl) ==∗
  ([∗ map] k ↦ tpl; v ∈ tpls; mods, ptuple_extend_wr_post γ tmods ts m past tid mods k tpl v).
Proof.
  iIntros "%Hdoms %HND %Helem %Hleall Hpre".
  iApply big_sepM2_bupd.
  iDestruct (big_sepM2_sepM_2 _ (λ k y, True)%I _ mods with "Hpre []") as "Hpre".
  { intros k. do 2 rewrite -elem_of_dom. by rewrite Hdoms. }
  { done. }
  iApply (big_sepM2_mono with "Hpre").
  iIntros (k tpl v) "%Htpls %Hmods Hpre".
  iDestruct "Hpre" as "[Hpre _]".
  iApply (ptuple_extend_wr with "Hpre"); [done | done | | done].
  apply Hleall.
  by eapply elem_of_dom_2.
Qed.

Definition commit_actual_case tid (r w mods : dbmap) γ τ : iProp Σ :=
  cmt_tmods_frag γ (tid, mods) ∗ txnmap_ptstos τ w ∗ ⌜dom w = dom r⌝.

Theorem wp_txn__Commit txn tid r w mods γ τ :
  {{{ own_txn_ready txn tid r γ τ ∗ commit_actual_case tid r w mods γ τ }}}
    Txn__Commit #txn
  {{{ RET #(); own_txn_uninit txn γ ∗ ⌜w = mods ∪ r⌝ }}}.
Proof.
  iIntros (Φ) "[Htxn H] HΦ".
  iDestruct "H" as "(Hfrag & Htxnps & %Hdom)".
  wp_call.

  (***********************************************************)
  (* proph.ResolveCommit(txn.txnMgr.p, txn.tid, txn.wrbuf)   *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  iDestruct (own_wrbuf_mods_tpls_dom with "HwrbufRP") as "%Hdoms".
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
  set keys := dom tpls.
  rewrite (union_difference_L keys keys_all); last set_solver.
  rewrite big_sepS_union; last set_solver.
  iDestruct "Hkeys" as "[Hkeys HkeysDisj]".
  rewrite -big_sepM_dom.
  (* Combine [Htuples] (the tuple physical + logical state), and [Hkeys] (per-key inv). *)
  iDestruct (big_sepM_sep_2 with "Hkeys Htuples") as "H".
  (* Extend physical tuples. *)
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  pose proof (fcc_head_commit_le_all _ _ _ _ Hcmt Hhead) as Hdomle.
  iMod (ptuples_extend_wr with "H") as "H"; [done | | done | done |].
  { by eapply fc_tids_unique_cmt. }
  iDestruct (big_sepM2_sep with "H") as "[Hkeys Htuples]".
  (* Interesting that [big_sepM_dom] and [big_sepM2_dom] are quite different. *)
  rewrite big_sepM2_dom'.
  (* Update [HkeysDisj] w.r.t. [tmods ∖ {[ (tid, mods) ]}] and [past ++ [EvCommit tid mods]]. *)
  iDestruct (per_key_inv_bigS_disj tid mods with "HkeysDisj") as "HkeysDisj"; first set_solver.
  iDestruct (big_sepS_union_2 with "Hkeys HkeysDisj") as "Hkeys".
  rewrite -union_difference_L; last set_solver.

  (* Update [Hnca Hfa Hfci Hfcc] to re-establish inv w.r.t. [future']. *)
  iDestruct (nca_inv_any_action with "Hnca") as "Hnca"; first apply Hfuture.
  iDestruct (fa_inv_diff_action with "Hfa") as "Hfa"; [apply Hfuture | done | ].
  iDestruct (fci_inv_diff_action with "Hfci") as "Hfci"; [apply Hfuture | | ].
  { simpl. by eapply fc_tids_unique_notin_fci. }
  iDestruct (fcc_inv_diff_action with "Hfcc") as "Hfcc"; [apply Hfuture | | ].
  { simpl. by eapply fc_tids_unique_notin_fcc. }
  iMod (cmt_inv_same_action with "Hfrag [$HcmtAuth]") as "Hcmt"; [apply Hfuture | | done | ].
  { by eapply fc_tids_unique_cmt. }
  apply (fc_tids_unique_minus_cmt tid mods) in Hfcnd.
  (* Close the invariant. *)
  iMod "Hclose" as "_".
  iMod ("HinvC" with "[Hproph Hts Hm Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { by eauto 15 with iFrame. }
  iIntros "!> HwrbufRP".
  wp_pures.
  (* Obtain [w = mods ∪ view]. *)
  iDestruct (txnmap_lookup_big with "Htxnmap Htxnps") as "%Hw".
  assert (Hrdom : dom r = dom (mods ∪ r)) by set_solver.
  rewrite Hrdom in Hdom.
  symmetry in Hdom.
  pose proof (Map.map_subset_dom_eq _ _ _ _ Hdom Hw) as Heq.

  (***********************************************************)
  (* txn.wrbuf.UpdateTuples(txn.tid)                         *)
  (***********************************************************)
  do 2 wp_loadField.
  wp_apply (wp_wrbuf__UpdateTuples with "[$HwrbufRP Htuples]").
  { unfold own_tuples_updated. by rewrite Etid. }
  iIntros "HwrbufRP".
  wp_pures.

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
  do 3 wp_loadField.
  wp_apply (wp_txnMgr__deactivate with "HtxnmgrRI Hactive").
  wp_pures.
  iApply "HΦ".
  eauto 20 with iFrame.
Qed.

End program.

#[global]
Hint Extern 1 (environments.envs_entails _ (commit_false_cases _ _ _ _)) => unfold commit_false_cases : core.
