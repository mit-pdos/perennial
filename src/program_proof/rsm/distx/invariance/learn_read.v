From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma ext_by_cmtd_inv_learn_read_free {repl cmtd kmod} ts :
  kmod !! O = None ->
  ext_by_cmtd repl cmtd kmod O ->
  ext_by_cmtd (last_extend ts repl) cmtd kmod O.
Proof.
  intros Hz. rewrite /ext_by_cmtd Hz.
  intros [[ts' Hrepl] _].
  split; last done.
  rewrite Hrepl.
  exists (ts `max` ts')%nat.
  apply last_extend_twice.
Qed.

Lemma ext_by_cmtd_inv_learn_read_acquired {repl cmtd kmod} ts tslock :
  (ts ≤ tslock)%nat ->
  ext_by_cmtd repl cmtd kmod tslock ->
  ext_by_cmtd (last_extend ts repl) cmtd kmod tslock.
Proof.
  rewrite /ext_by_cmtd. intros Hlt Hdiff.
  destruct (kmod !! tslock) as [v |] eqn:Hv.
  { (* Case: Tuple committed by [tslock]. *)
    rewrite last_extend_twice.
    by replace (_ `max` _)%nat with tslock by lia.
  }
  destruct Hdiff as [[ts' Hrepl] Hlen].
  (* Case: Tuple prepared but not committed by [tslock] yet. *)
  split.
  { rewrite Hrepl last_extend_twice. by eauto. }
  intros Hnz. specialize (Hlen Hnz).
  destruct (decide (repl = [])) as [-> | Hne]; first done.
  rewrite last_extend_length; [lia | done].
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txn_tokens_inv_learn_read {γ gid log} ts key :
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdRead ts key]).
  Proof.
    iIntros "Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (tpls !! key) as [[h t] |]; last done.
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma key_inv_learn_read {γ} ts k h t :
    let tpl := read ts h t in
    key_inv_no_repl_tsprep γ k h t -∗
    key_inv_no_repl_tsprep γ k tpl.1 tpl.2.
  Proof.
    iIntros (tpl) "Hkey".
    subst tpl. rewrite /read.
    case_decide as Ht; last done.
    iNamed "Hkey". iNamed "Hprop". simpl.
    destruct Ht as [-> | Hlt].
    { (* Case: Tuple not acquired by any txn. *)
      apply (ext_by_cmtd_inv_learn_read_free ts) in Hdiffc; last done.
      iFrame "∗ # %".
    }
    (* Case: Tuple prepared at [t] where [ts < t]. *)
    pose proof (ext_by_cmtd_inv_learn_read_acquired _ _ Hlt Hdiffc) as Hdiffc'.
    iFrame "∗ # %".
  Qed.

  Lemma group_inv_learn_read γ gid log cpool ts key :
    CmdRead ts key ∈ cpool ->
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdRead ts key]) cpool.
  Proof.
    iIntros (Hc) "Hkeys Hgroup".
    do 2 iNamed "Hgroup".
    rewrite /group_inv_no_log_with_cpool /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /=.
    (* Obtain validity of the read input. *)
    iDestruct (big_sepS_elem_of with "Hvc") as "Hread"; first apply Hc.
    iDestruct "Hread" as %(_ & Hkey & Hgid).
    destruct (tpls !! key) as [[h t] |] eqn:Hht; last first.
    { (* Case: Out-of-range key; contradiction. *)
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite /valid_key in Hkey.
      by rewrite -not_elem_of_dom Hdom in Hht.
    }
    (* Case: Valid read. *)
    set tpl' := read _ _ _.
    (* Take the required key invariant. *)
    iDestruct (big_sepS_elem_of_acc with "Hkeys") as "[Hkey HkeysC]"; first apply Hkey.
    (* Take the half-ownership of the tuple out from the key invariant. *)
    iDestruct (key_inv_extract_repl_tsprep with "Hkey") as (tpl) "[Hkey Htpl]".
    (* And the other half from the group invariant. *)
    iDestruct (big_sepM_delete with "Hrepls") as "[Hrepl Hrepls]".
    { by apply map_lookup_filter_Some_2. }
    (* Agree on their value. *)
    iDestruct (tuple_repl_agree with "Hrepl Htpl") as %->. simpl.
    (* Update the tuple. *)
    iMod (tuple_repl_update tpl' with "Hrepl Htpl") as "[Hrepl Htpl]".
    { simpl. case_decide; [apply last_extend_prefix | done]. }
    (* Re-establish key invariant w.r.t. the updated tuple. *)
    iDestruct (key_inv_learn_read ts with "Hkey") as "Hkey".
    (* Put back tuple ownership back to key invariant. *)
    iDestruct (key_inv_merge_repl_tsprep with "Hkey Htpl") as "Hkey".
    (* Put the key invariant back. *)
    iDestruct ("HkeysC" with "Hkey") as "Hkeys".
    (* Put back tuple ownership back to group invariant. *)
    iDestruct (big_sepM_insert_2 with "Hrepl Hrepls") as "Hrepls".
    rewrite insert_delete_eq insert_tpls_group_commute; last done.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_read ts key with "Htks") as "Htks'".
    (* Create witnesses for the replicated history. *)
    iDestruct (hist_repl_witnesses_inv_learn (CmdRead ts key) with "Hrepls Hhists") as "#Hhists'".
    { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hht. }
    by iFrame "∗ # %".
  Qed.

End inv.
