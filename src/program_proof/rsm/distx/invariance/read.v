From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma ext_by_cmtd_inv_read {repl cmtd kmodc} tid tsprep :
  (tid ≤ length repl)%nat ->
  cmtd ≠ [] ->
  ext_by_cmtd repl cmtd kmodc tsprep ->
  ext_by_cmtd repl (last_extend tid cmtd) kmodc tsprep.
Proof.
  rewrite /ext_by_cmtd.
  intros Hlenr Hnnil Hext.
  destruct (kmodc !! tsprep) as [v |].
  - destruct (decide (tid ≤ length cmtd)%nat) as [Hlenc | Hlenc].
    { by rewrite last_extend_id; last apply Hlenc. }
    rewrite Nat.nle_gt in Hlenc.
    assert (Hlen : (length repl < length cmtd)%nat).
    { rewrite Hext.
      rewrite length_app /=.
      pose proof (last_extend_length_ge tsprep repl) as Hlen.
      lia.
    }
    lia.
  - destruct Hext as [Hext Htsprep].
    split; last apply Htsprep.
    destruct Hext as [tsr Hext].
    destruct (decide (tsr ≤ length cmtd)%nat) as [Hlenc | Hlenc].
    + (* we have [repl = cmtd] from [Hext Hlenc] *)
      rewrite last_extend_id in Hext; last apply Hlenc. subst repl.
      exists O.
      by rewrite last_extend_twice /= last_extend_id.
    + rewrite Nat.nle_gt in Hlenc.
      assert (Hlen : length repl = tsr).
      { rewrite Hext last_extend_length_eq_n; [done | done | lia]. }
      rewrite Hlen in Hlenr.
      exists tsr.
      rewrite last_extend_twice.
      by replace (_ `max` _)%nat with tsr by lia.
Qed.

Lemma head_read_first_commit_compatible future ts tshd wrs keyhd :
  head_read future tshd keyhd ->
  first_commit_compatible future ts wrs ->
  keyhd ∈ dom wrs ->
  (tshd ≤ ts)%nat.
Proof.
  intros Hhr (lp & ls & (Happ & _ & Hhead) & Hcomp) Hnempty.
  destruct (decide (lp = [])) as [-> | Hnnil].
  { rewrite Happ /= /head_read Hhead in Hhr. inv Hhr. }
  assert (Hlp : ActRead tshd keyhd ∈ lp).
  { apply head_Some_elem_of.
    rewrite (head_prefix _ future); [done | apply Hnnil |].
    rewrite Happ.
    by apply prefix_app_r.
  }
  rewrite /compatible_all Forall_forall in Hcomp.
  specialize (Hcomp _ Hlp).
  destruct Hcomp; [lia | contradiction].
Qed.

Lemma conflict_free_inv_read {future tmodcs tid key} :
  head_read future tid key ->
  conflict_free future tmodcs ->
  conflict_free (tail future) tmodcs.
Proof.
  intros Hhead Hcf ts wrs Hwrs.
  specialize (Hcf _ _ Hwrs). simpl in Hcf.
  by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
Qed.

Lemma conflict_past_inv_read {past future tmodas tid key} :
  head_read future tid key ->
  conflict_past past future tmodas ->
  conflict_past (past ++ [ActRead tid key]) (tail future) tmodas.
Proof.
  intros Hhead Hcp ts form Hform.
  specialize (Hcp _ _ Hform). simpl in Hcp.
  rewrite /conflict_cases in Hcp.
  destruct form as [| wrsx | wrsx]; simpl.
  - by apply no_commit_inv_tail_future.
  - by apply first_commit_incompatible_inv_snoc_past_tail_future.
  - by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
Qed.

Lemma cmtxn_in_past_inv_read {past resm} tid key :
  cmtxn_in_past past resm ->
  cmtxn_in_past (past ++ [ActRead tid key]) resm.
Proof.
  intros Hcmtxn ts wrs Hwrs.
  specialize (Hcmtxn _ _ Hwrs). simpl in Hcmtxn.
  set_solver.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma key_inv_read γ kmodl tid key vl vr :
    tid ≠ O ->
    le_all tid (dom kmodl) ->
    hist_lnrz_at γ key (pred tid) vl -∗
    hist_repl_at γ key (pred tid) vr -∗
    key_inv_with_kmodl γ key kmodl ==∗
    key_inv_with_kmodl γ key kmodl ∗
    hist_cmtd_length_lb γ key tid ∗
    ⌜vl = vr⌝.
  Proof.
    iIntros (Hnz Hleall) "#Hlnrzlb #Hrepllb Hkey".
    iNamed "Hkey". iNamed "Hprop".
    (* Obtain value at [pred tid] for both [cmtd] and [lnrz]. *)
    iDestruct (hist_lnrz_lookup with "Hlnrz Hlnrzlb") as %Hvl.
    iDestruct (hist_repl_lookup with "Hrepl Hrepllb") as %Hvr.
    (* Re-establish [ext_by_lnrz] and [ext_by_cmtd]. *)
    assert (Hlenl : (tid ≤ length lnrz)%nat).
    { apply lookup_lt_Some in Hvl. lia. }
    pose proof (ext_by_lnrz_inv_read _ _ _ _ Hlenl Hleall Hdiffl) as Hdiffl'.
    assert (Hlenr : (tid ≤ length repl)%nat).
    { apply lookup_lt_Some in Hvr. lia. }
    pose proof (ext_by_lnrz_not_nil _ _ _ Hdiffl) as Hnnil.
    pose proof (ext_by_cmtd_inv_read tid _ Hlenr Hnnil Hdiffc) as Hdiffc'.
    (* Extend [hist_cmtd_auth] to [tid]. Note that it's a no-op when [tid ≤ length cmtd]. *)
    set cmtd' := last_extend _ _ in Hdiffl' Hdiffc'.
    iMod (hist_cmtd_update cmtd' with "Hcmtd") as "Hcmtd".
    { apply last_extend_prefix. }
    iAssert (hist_cmtd_length_lb γ key tid)%I as "#Hlb".
    { iDestruct (hist_cmtd_witness with "Hcmtd") as "#Hlb".
      iFrame "Hlb".
      iPureIntro.
      by apply last_extend_length_ge_n.
    }
    assert (Heq : vl = vr).
    { (* Obtain [prefix cmtd' lnrz]. *)
      destruct Hdiffl' as (_ & Hprefixcl & _).
      assert (Hlenc : (pred tid < length cmtd')%nat).
      { assert (Hlenc : (tid ≤ length cmtd')%nat); first by apply last_extend_length_ge_n. lia. }
      pose proof (prefix_lookup_lt _ _ _ Hlenc Hprefixcl) as Hvl'.
      rewrite Hvl in Hvl'.
      pose proof (ext_by_cmtd_prefix Hdiffc') as Hprefix.
      destruct Hprefix as [Hprefixrc | Hprefixcr].
      { pose proof (prefix_lookup_Some _ _ _ _ Hvr Hprefixrc) as Hvr'.
        rewrite Hvl' in Hvr'.
        by inv Hvr'.
      }
      { pose proof (prefix_lookup_lt _ _ _ Hlenc Hprefixcr) as Hvr'.
        rewrite Hvr Hvl' in Hvr'.
        by inv Hvr'.
      }
    }
    by iFrame "∗ # %".
  Qed.

  Lemma txn_inv_read γ tid key vl vr future :
    tid ≠ O ->
    head_read future tid key ->
    hist_lnrz_at γ key (pred tid) vl -∗
    hist_repl_at γ key (pred tid) vr -∗
    txn_inv_no_future γ future -∗
    key_inv γ key ==∗
    txn_inv_no_future γ (tail future) ∗
    key_inv γ key ∗
    ⌜vl = vr⌝.
  Proof.
    iIntros (Hnz Hhead) "#Hlnrzlb #Hrepllb Htxn Hkey".
    iNamed "Htxn".
    iDestruct (key_inv_expose_kmodl with "Hkey") as (kmodl) "Hkey".
    iAssert (⌜le_all tid (dom kmodl)⌝)%I as %Hleall.
    { iNamed "Hkey". iNamed "Hprop".
      iDestruct (big_sepS_elem_of _ _ key with "Hkmodls") as "Hkmodl'".
      { apply Hall. }
      iDestruct (kmod_lnrz_agree with "Hkmodl' Hkmodl") as %->.
      iPureIntro.
      intros tsx Htsx.
      apply elem_of_dom_vslice in Htsx as [wrs [Hwrs Hinwrs]].
      specialize (Hcf _ _ Hwrs). simpl in Hcf.
      eapply head_read_first_commit_compatible; [apply Hhead | apply Hcf | apply Hinwrs].
    }
    (* Obtain a witness that the committed history has been extended to [tid], and [vl = vr]. *)
    iMod (key_inv_read with "Hlnrzlb Hrepllb Hkey") as "(Hkey & #Hcmtd & %Heq)".
    { apply Hnz. }
    { apply Hleall. }
    iDestruct (key_inv_hide_kmodl with "Hkey") as "Hkey".
    (* Re-establish [past_action_witness]. *)
    iAssert (past_action_witness γ (ActRead tid key))%I as "#Hpa"; first iFrame "Hcmtd".
    iCombine "Hpas Hpa" as "Hpas'".
    rewrite -big_sepL_snoc.
    (* Re-establish [conflict_free], [conflict_past], [cmtxn_in_past] w.r.t. read. *)
    pose proof (conflict_free_inv_read Hhead Hcf) as Hcf'.
    pose proof (conflict_past_inv_read Hhead Hcp) as Hcp'.
    pose proof (cmtxn_in_past_inv_read tid key Hcmtxn) as Hcmtxn'.
    by iFrame "∗ # %".
  Qed.

End inv.
