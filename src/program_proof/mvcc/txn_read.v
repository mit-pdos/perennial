From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr tuple_repr
     wrbuf_proof index_proof tuple_read_version proph_proof.

Section lemma.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

#[local]
Lemma ltuple_ptuple_ptsto_eq {γ key tmods ts m past} tid v1 v2 :
  per_key_inv_def γ key tmods ts m past -∗
  ltuple_ptsto γ key v1 tid -∗
  ptuple_ptsto γ key v2 tid -∗
  ⌜v1 = v2⌝.
Proof.
  iIntros "Hkey Hlpts Hppts".
  iNamed "Hkey".
  apply tuple_mods_rel_prefix in Htmrel.
  iDestruct "Hlpts" as (logi') "[Hllb %Hv1]".
  iDestruct "Hppts" as (phys') "[Hplb %Hv2]".
  iDestruct (ltuple_prefix with "Hltuple Hllb") as "%Hl".
  iDestruct (ptuple_prefix with "Hptuple Hplb") as "%Hp".
  iPureIntro.
  unshelve epose proof (prefix_lookup_Some logi' logi tid v1 _ _); [done | done |].
  unshelve epose proof (prefix_lookup_Some phys' phys tid v2 _ _); [done | done |].
  unshelve epose proof (prefix_lookup_Some phys logi tid v2 _ _); [done | done |].
  rewrite H in H1. by inversion H1.
Qed.

End lemma.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__Read txn tid view (k : u64) dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv }}}
    Txn__Read #txn #k
  {{{ (v : byte_string) (found : bool), RET (#(LitString v), #found);
      own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv ∗ ⌜dbv = to_dbval found v⌝
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hptsto] HΦ".
  (* We need this to obtain a lb on logical tuple of key [k]. *)
  iDestruct (own_txn_txnmap_ptsto_dom with "Htxn Hptsto") as "%Hindom".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_rec. wp_pures.

  (*@ func (txn *Txn) Read(key uint64) (string, bool) {                       @*)
  (*@     // First try to find @key in the local write set.                   @*)
  (*@     wrbuf := txn.wrbuf                                                  @*)
  (*@     valb, wr, found := wrbuf.Lookup(key)                                @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Lookup with "HwrbufRP").
  iIntros (v d ok) "[HwrbufRP %Hlookup]".
  wp_pures.

  (*@     if found {                                                          @*)
  (*@         return valb, wr                                                 @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  unfold spec_wrbuf__Lookup in Hlookup.
  wp_if_destruct.
  { wp_pures.
    iModIntro.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup'".
    apply (lookup_union_Some_l _ view) in Hlookup.
    rewrite Hlookup' in Hlookup.
    inversion_clear Hlookup.
    iSplitR "Hptsto".
    { eauto 25 with iFrame. }
    by iFrame.
  }

  (*@     idx := txn.idx                                                      @*)
  (*@     tuple := idx.GetTuple(key)                                          @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.

  (*@     tuple.ReadWait(txn.tid)                                             @*)
  (*@                                                                         @*)
  wp_loadField.
  wp_apply (wp_tuple__ReadWait with "HtupleRI").
  iIntros (owned vchain) "(Htuple & HtupleOwn & Hptuple & %Hwait)".
  wp_pures.
  
  (*@     trusted_proph.ResolveRead(txn.proph, txn.tid, key)                  @*)
  (*@                                                                         @*)
  do 2 wp_loadField.
  wp_apply (wp_ResolveRead γ); first auto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iRename "Hproph" into "Hp".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hhead & Hproph)".
  (* Extend the physical tuple. *)
  unfold ptuple_auth_owned.
  (* iMod (tuple_read_safe with "Hkeys Hcmt Hread") as "(Hkeys & Hcmt & Htuple & Hptuple)"; first set_solver. *)
  set Ψ := (λ key, per_key_inv_def γ key tmods ts m (past ++ [ActRead tid k]))%I.
  iDestruct (big_sepS_elem_of_acc_impl k with "Hkeys") as "[Hkey Hkeys]"; first set_solver.
  iRename "Hptuple" into "Hptuple'".
  iDestruct (cmt_inv_fcc_tmods with "Hcmt") as "%Hcmtfcc".
  iAssert (|==> ptuple_auth_owned γ k owned (extend (S tid) vchain) ∗ Ψ k)%I
    with "[Hptuple' Hkey]" as "> [Hptuple Hkey]".
  { destruct Hwait as [Howned | Hlen].
    - (* Case [owned = 0]. *)
      unfold ptuple_auth_owned.
      rewrite Howned.
      iNamed "Hkey".
      iDestruct (ptuple_agree with "Hptuple Hptuple'") as "%Eptuple".
      subst vchain.
      iMod (vchain_update (extend (S tid) phys) with "Hptuple Hptuple'") as "[Hptuple Hptuple']".
      { apply extend_prefix. }
      iModIntro.
      iFrame "Hptuple'".
      subst Ψ. simpl.
      do 2 iExists _.
      (* Get a lb on [logi] required by [tuplext_read]. *)
      rewrite elem_of_dom in Hindom. destruct Hindom as [u Hlookup'].
      iDestruct (big_sepM_lookup _ _ k with "Hltuples") as (logi') "[#Hlb %Hlen]"; first done.
      apply lookup_lt_Some in Hlen.
      iDestruct (ltuple_prefix with "Hltuple Hlb") as "%Hprefix".
      apply prefix_length in Hprefix.
      iFrame "∗ %".
      iPureIntro.
      split.
      { (* Prove [tuple_mods_rel] (i.e., safe extension). *)
        apply tuplext_read; [lia | | done].
        apply fcc_head_read_le_all with future; [done | set_solver].
      }
      { (* Prove [ptuple_past_rel]. *)
        apply ptuple_past_rel_read_lt_len.
        { (* Note: [x < y] is a notation for [S x ≤ y]. *)
          apply extend_length_ge_n.
          by eapply tuple_mods_rel_last_phys.
        }
        apply (ptuple_past_rel_extensible _ phys); last done.
        apply extend_prefix.
      }
    - (* Case [tid < length vchain]. *)
      iModIntro.
      (* First we deduce eq between physical tuples in global and tuple invs. *)
      iNamed "Hkey".
      iDestruct (ptuple_agree with "Hptuple Hptuple'") as "%Eptuple".
      subst vchain.
      iSplitL "Hptuple'".
      { replace (extend (S tid) phys) with phys; first done.
        symmetry.
        apply extend_length_same. lia.
      }
      subst Ψ. simpl.
      do 2 iExists _.
      iFrame "∗ %".
      iPureIntro.
      apply ptuple_past_rel_read_lt_len; [lia | done].
  }
  iDestruct ("Hkeys" with "[] [Hkey]") as "Hkeys"; [ | iAccu | ].
  { (* Adding [ActRead tid k] to [past] where [key ≠ k] preserves [per_key_inv_def]. *)
    iIntros "!>" (key) "%Helem %Hneq Hkey".
    subst Ψ. simpl.
    iApply per_key_inv_past_snoc_diff_key; done.
  }
  iMod "Hclose".
  iMod ("HinvC" with "[Hproph Hm Hts Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { (* Close the inv. *)
    iNext. unfold mvcc_inv_sst_def.
    do 7 iExists _.
    iExists (past ++ [ActRead tid k]), future'.
    iDestruct (nca_inv_any_action with "Hnca") as "Hnca"; first apply Hhead.
    iDestruct (fa_inv_diff_action  with "Hfa")  as "Hfa";  [apply Hhead | done |].
    iDestruct (fci_inv_diff_action with "Hfci") as "Hfci"; [apply Hhead | done |].
    iDestruct (fcc_inv_diff_action with "Hfcc") as "Hfcc"; [apply Hhead | done |].
    iDestruct (cmt_inv_diff_action with "Hcmt") as "Hcmt"; [apply Hhead | done |].
    by iFrame.
  }
  iModIntro.
  iIntros "_".
  wp_pures.

  (*@     val, found := tuple.ReadVersion(txn.tid)                            @*)
  (*@                                                                         @*)
  wp_loadField.
  iDestruct (is_tuple_invgc with "HtupleRI") as "#Hinvgc".
  wp_apply (wp_tuple__ReadVersion with "[$Hactive $Htuple $HtupleOwn Hptuple]").
  { rewrite Etid. iFrame. iPureIntro. destruct Hwait; [by left | word]. }
  iIntros (val found) "[Hactive Hpptsto]".
  rewrite Etid.
  wp_pures.
  iInv "Hinv" as "> HinvO" "HinvC".
  iNamed "HinvO".
  (* Deduce eq between logical and physical read. *)
  iDestruct (big_sepS_elem_of_acc _ _ k with "Hkeys") as "[Hkey Hkeys]"; first set_solver.
  iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup'".
  rewrite lookup_union_r in Hlookup'; last auto.
  iDestruct (big_sepM_lookup with "Hltuples") as "Hlptsto"; first apply Hlookup'.
  iDestruct (ltuple_ptuple_ptsto_eq with "Hkey Hlptsto Hpptsto") as "%Heq".
  iDestruct ("Hkeys" with "Hkey") as "Hkeys".
  iMod ("HinvC" with "[Hproph Hm Hts Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { eauto 20 with iFrame. }

  (*@     return val, found                                                   @*)
  (*@                                                                         @*)
  iModIntro.
  iApply "HΦ".
  iSplitR "Hptsto".
  { iExists _, _.
    iFrame "Hltuples Htxnmap Hwrbuf HwrbufRP".
    iSplitL; last done.
    do 5 iExists _.
    iFrame "Hactive Htid".
    iFrame "Hidx HidxRI Hsite HsiteRI Hp Hinv".
    done.
  }
  by iFrame "Hptsto".
Qed.

Theorem wp_txn__Read_found txn tid view (k : u64) (v : byte_string) γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmap_ptsto τ k (Some v) }}}
    Txn__Read #txn #k
  {{{ RET (#(LitString v), #true);
      own_txn txn tid view γ τ ∗ txnmap_ptsto τ k (Some v)
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hpt] HΦ".
  wp_apply (wp_txn__Read with "[$Htxn $Hpt]").
  iIntros (v' found) "(Htxn & Hpt & %Hv')".
  destruct found eqn:Efound; last by simpl in Hv'.
  simpl in Hv'. inversion_clear Hv'.
  iApply "HΦ".
  iFrame.
Qed.

End program.
