From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma ext_by_lnrz_inv_read ts cmtd lnrz kmodl :
  (ts ≤ length lnrz)%nat ->
  le_all ts (dom kmodl) ->
  ext_by_lnrz cmtd lnrz kmodl ->
  ext_by_lnrz (last_extend ts cmtd) lnrz kmodl.
Proof.
  intros Hlenl Hles Hext.
  destruct (decide (ts ≤ length cmtd)%nat) as [Hlenc | Hlenc].
  { (* Trivial if [cmtd] is not actually extended. *)
    by rewrite last_extend_id.
  }
  apply not_le in Hlenc.
  destruct Hext as (vlast & Hprefix & Hlast & Hlen & Hext).
  exists vlast.
  split.
  { (* Re-establish prefix. *)
    apply prefix_pointwise.
    intros i Hi.
    rewrite /last_extend Hlast /extend.
    destruct (decide (i < length cmtd)%nat) as [Hilt | Hige].
    { (* Case: before-extension [i < length cmtd]. *)
      rewrite lookup_app_l; last done.
      by apply prefix_lookup_lt.
    }
    (* Case: read-extension [length cmtd ≤ i]. *)
    rewrite Nat.nlt_ge in Hige.
    (* Obtain [i < ts]. *)
    rewrite last_extend_length_eq_n in Hi; [| set_solver | lia].
    assert (is_Some (lnrz !! i)) as [u Hu].
    { rewrite lookup_lt_is_Some. lia. }
    assert (Higeweak : (pred (length cmtd) ≤ i)%nat) by lia.
    specialize (Hext _ _ Higeweak Hu).
    rewrite lookup_app_r; last done.
    rewrite Hu lookup_replicate.
    split; last lia.
    rewrite -Hext.
    apply prev_dbval_lt_all.
    intros n Hn.
    (* Obtain [ts ≤ n]. *)
    specialize (Hles _ Hn). simpl in Hles.
    (* Prove [i < n] by [i < ts] and [ts ≤ n]. *)
    lia.
  }
  split.
  { (* Re-establish last. *)
    by rewrite last_last_extend.
  }
  split.
  { (* Re-establish len. *)
    intros n Hn.
    specialize (Hlen _ Hn). simpl in Hlen.
    specialize (Hles _ Hn). simpl in Hles.
    rewrite last_extend_length_eq_n; [| set_solver | lia].
    lia.
  }
  (* Re-establish ext. *)
  intros t u Ht Hu.
  rewrite last_extend_length_eq_n in Ht; [| set_solver | lia].
  apply Hext; [lia | done].
Qed.

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
  destruct form as [| | wrsx | wrsx]; simpl.
  - by apply no_commit_abort_inv_tail_future.
  - by unshelve eapply (first_abort_inv_tail_future _ _ _ _ Hhead).
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

  Lemma txnsys_inv_read γ tid key vl vr future :
    tid ≠ O ->
    head_read future tid key ->
    hist_lnrz_at γ key (pred tid) vl -∗
    hist_repl_at γ key (pred tid) vr -∗
    txnsys_inv_no_future γ future -∗
    key_inv γ key ==∗
    txnsys_inv_no_future γ (tail future) ∗
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
