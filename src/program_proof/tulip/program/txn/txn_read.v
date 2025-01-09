From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import
  res txn_repr txn_getwrs proph txn_key_to_group.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_read.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__Read txn tid key value rds γ τ  :
    valid_key key ->
    {{{ own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value }}}
      Txn__Read #txn #(LitString key)
    {{{ (ok : bool), RET (dbval_to_val (if ok then value else None), #ok);
        own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key value
    }}}.
  Proof.
    iIntros (Hvk Φ) "[Htxn Hpt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Read(key string) (tulip.Value, bool) {                  @*)
    (*@     vlocal, hit := txn.getwrs(key)                                      @*)
    (*@     if hit {                                                            @*)
    (*@         return vlocal, true                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Htxn".
    wp_apply (wp_Txn__getwrs with "Hwrs").
    { apply Hvk. }
    iIntros (vlocal ok) "[Hwrs %Hv]".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hvalue.
    wp_if_destruct.
    { (* Prove [vlocal = value]. *)
      apply (lookup_union_Some_l _ rds) in Hv.
      rewrite Hv in Hvalue.
      inv Hvalue.
      wp_pures.
      iApply ("HΦ" $! true).
      by iFrame "∗ # %".
    }
    clear Heqb ok.

    (*@     gid := KeyToGroup(key)                                              @*)
    (*@     gcoord := txn.gcoords[gid]                                          @*)
    (*@     v, ok := gcoord.Read(txn.ts, key)                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Txn__keyToGroup with "Hwrs").
    { apply Hvk. }
    iIntros (gid) "[Hwrs %Hgid]".
    iNamed "Hgcoords".
    wp_loadField.
    wp_apply (wp_MapGet with "Hgcoords").
    iIntros (gcoord ok) "[%Hget Hgcoords]".
    destruct ok; last first.
    { apply map_get_false in Hget as [Hget _].
      rewrite -not_elem_of_dom Hdomgcoords -Hgid in Hget.
      by pose proof (elem_of_key_to_group key).
    }
    apply map_get_true in Hget.
    iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hget.
    iNamed "Htxn".
    wp_loadField.
    wp_apply (wp_GroupCoordinator__Read with "Hgcoordabs").
    { rewrite Htsword.
      split; first apply Hvts.
      split; first apply Hvk.
      apply Hgid.
    }
    iIntros (v ok) "#Hread".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         return tulip.Value{}, false                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { iApply ("HΦ" $! false).
      iAssert (own_txn_gcoords txn γ)%I with "[$HgcoordsP $Hgcoords]" as "Hgcoords".
      { by iFrame "# %". }
      by iFrame "∗ # %".
    }
    rewrite Htsword.

    (*@     trusted_proph.ResolveRead(txn.proph, txn.ts, key)                   @*)
    (*@                                                                         @*)
    rewrite lookup_union_r in Hvalue; last apply Hv.
    iDestruct (big_sepM_lookup with "Hlnrz") as "Hhistl"; first apply Hvalue.
    do 2 wp_loadField.
    wp_apply wp_ResolveRead; first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    pose proof (elem_of_key_to_group key) as Hin.
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
    { apply Hin. }
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
    { apply Hin. }
    iDestruct (big_sepS_elem_of_acc _ _ key with "Hkeys") as "[Hkey HkeysC]".
    { apply elem_of_dom_2 in Hvalue. set_solver. }
    iMod (txnsys_inv_read with "Hread Hhistl Htxnsys Hgroup Hrg Hkey")
      as "(Htxnsys & Hgroup & Hrg & Hkey & %Heq)".
    { rewrite /valid_ts in Hvts. lia. }
    { by rewrite Hfuture. }
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iDestruct ("HkeysC" with "Hkey") as "Hkeys".
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iIntros "!> _".
    wp_pures.
    subst value.

    (*@     return v, true                                                      @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! true).
    iAssert (own_txn_gcoords txn γ)%I with "[$HgcoordsP $Hgcoords]" as "Hgcoords".
    { by iFrame "# %". }
    by iFrame "∗ # %".
  Qed.

End program.
