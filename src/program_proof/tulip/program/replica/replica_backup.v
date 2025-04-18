From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_intervene.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__Backup (rp : loc) gid rid γ :
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Backup #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Backup() {                                           @*)
    (*@     for {                                                               @*)
    (*@         rp.mu.Lock()                                                    @*)
    (*@         // Create a copy to not read @rp.ptgsm to simplify proof.       @*)
    (*@         ptgsm := make(map[uint64][]uint64)                              @*)
    (*@         for ts, ptgs := range(rp.ptgsm) {                               @*)
    (*@             ptgsm[ts] = ptgs                                            @*)
    (*@         }                                                               @*)
    (*@         for ts, ptgs := range(ptgsm) {                                  @*)
    (*@             rp.intervene(ts, ptgs)                                      @*)
    (*@         }                                                               @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         primitive.Sleep(params.NS_BACKUP_INTERVAL)                      @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    do 2 iNamed "Hrp".
    iNamed "Hpgm".
    wp_apply (wp_NewMap).
    iIntros (mP) "HmP".
    wp_loadField.
    set P := (λ (mx : gmap u64 Slice.t), own_map mP (DfracOwn 1) mx)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HptgsmS [$HmP]").
    { clear Φ.
      iIntros (m t p Φ) "!> [HmP [%Hnone %Hsome]] HΦ".
      wp_apply (wp_MapInsert with "HmP"); first done.
      iIntros "HmP".
      by iApply "HΦ".
    }
    iIntros "[HptgsmS HmP]".
    subst P. simpl.
    iAssert (own_replica rp gid rid γ α)%I with "[-HΦ HmP Hlocked]" as "Hrp".
    { by iFrame "Hcm Hhistm Hcpm Hpsmrkm Hdurable Hlsna ∗ # %". }
    set P := (λ (mx : gmap u64 Slice.t), own_replica rp gid rid γ α)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HmP [$Hrp]").
    { clear Φ.
      iIntros (m t p Φ) "!> [Hrp [%Hnone %Hsome]] HΦ".
      wp_pures.
      iDestruct (big_sepM2_dom with "Hptgsm") as %Hdomeq.
      symmetry in Hpgmabs.
      assert (is_Some (ptgsm !! t)) as [g Hg].
      { by rewrite -elem_of_dom -Hdomeq elem_of_dom. }
      pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hpgmabs Hg) as (tx & Htx & Hpgmtx).
      iDestruct (big_sepS_elem_of with "Hlnrzs") as "Hlnrz".
      { apply elem_of_dom_2 in Hpgmtx. apply Hpgmtx. }
      iDestruct (big_sepM2_lookup with "Hptgsm") as "Hptgs".
      { apply Hsome. }
      { apply Hg. }
      iDestruct (big_sepM_lookup with "Hsafebk") as "Hsafe".
      { apply Hpgmtx. }
      wp_apply (wp_Replica__intervene with "[] Hptgs [] Hgidrid Hgaddrm Hproph Hinv Hinvfile Hrp").
      { by replace (uint.nat t) with tx by word. }
      { by replace (uint.nat t) with tx by word. }
      iIntros "Hrp".
      by iApply "HΦ".
    }
    iIntros "[HmP Hrp]".
    subst P. simpl.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hrp]").
    wp_apply (wp_Sleep).
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
