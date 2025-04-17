From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr bgpreparer_ready bgpreparer_get_phase.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

 Theorem wp_BackupGroupCoordinator__WaitUntilPrepareDone gcoord rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__WaitUntilPrepareDone #gcoord
    {{{ (tphase : txnphase) (valid : bool), RET (#(txnphase_to_u64 tphase), #valid); 
        if valid then safe_group_txnphase γ ts gid tphase else True
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) WaitUntilPrepareDone() (uint64, bool) { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_pures.
    iNamed "Hgcoord". do 2 iNamed "Hgpp".

    (*@     for !gcoord.gpp.ready() {                                           @*)
    (*@         gcoord.cv.Wait()                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (cont : bool), ∃ (phase' : bgppphase) (gppP' : loc),
                 "HgppP"   ∷ gcoord ↦[BackupGroupCoordinator :: "gpp"] #gppP' ∗
                 "Hgpp"    ∷ own_backup_gpreparer_with_phase gppP' phase' rk ts cid gid γ ∗
                 "Hleader" ∷ own_backup_gcoord_leader gcoord (dom addrm) ∗
                 "Hcomm"   ∷ own_backup_gcoord_comm gcoord addrm gid γ ∗
                 "Hlocked" ∷ locked #muP ∗
                 "%Hready" ∷ ⌜if cont then True else bgpp_ready phase'⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HgppP Hgpp Hleader Hcomm Hlocked]"); last first; first 1 last.
    { by iFrame. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_loadField.
      wp_apply (wp_BackupGroupPreparer__ready_external with "Hgpp").
      iIntros "Hgpp".
      case_bool_decide as Hready'; wp_pures.
      { iApply "HΦ". by iFrame "∗ %". }
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ]").
      { by iFrame "Hlock Hcv ∗". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      iNamed "Hgcoord". do 2 iNamed "Hgpp".
      by iFrame.
    }
    iNamed 1.
    clear phase gppP.
    rename phase' into phase. rename gppP' into gppP.

    (*@     phase := gcoord.gpp.getPhase()                                      @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__getPhase with "Hgpp").
    iIntros "[Hgpp #Hsafep]".
    wp_pures.
    
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.

    (*@     if phase == BGPP_STOPPED {                                          @*)
    (*@         // TXN_PREPARED here is just a placeholder.                     @*)
    (*@         return tulip.TXN_PREPARED, false                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hstopped; wp_pures.
    { by iApply ("HΦ" $! TxnPrepared). }

    (*@     if phase == BGPP_COMMITTED {                                        @*)
    (*@         return tulip.TXN_COMMITTED, true                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcommitted; wp_pures.
    { iApply ("HΦ" $! TxnCommitted).
      by destruct phase.
    }

    (*@     if phase == BGPP_ABORTED {                                          @*)
    (*@         return tulip.TXN_ABORTED, true                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Haborted; wp_pures.
    { iApply ("HΦ" $! TxnAborted).
      by destruct phase.
    }

    (*@     return tulip.TXN_PREPARED, true                                     @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! TxnPrepared).
    by destruct phase.
  Qed.

End program.
