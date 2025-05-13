From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_gettermc paxos_getlsnc.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__WaitUntilSafe (px : loc) (lsn : u64) (term : u64) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
      Paxos__WaitUntilSafe #px #lsn #term
    {{{ (safe : bool), RET #safe; True }}}.
  Proof.
    iIntros "#Hpx" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) WaitUntilSafe(lsn uint64, term uint64) bool {          @*)
    (*@     var safe bool                                                       @*)
    (*@     var nretry uint64                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (safeP) "HsafeP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (nretryP) "HnretryP".

    (*@     for {                                                               @*)
    (*@                                                                         @*)
    set P := (λ cont : bool, ∃ (safe : bool) (nretry : u64),
                 "HsafeP"   ∷ safeP ↦[boolT] #safe ∗
                 "HnretryP" ∷ nretryP ↦[uint64T] #nretry)%I.
    wp_apply (wp_forBreak P with "[] [$HsafeP $HnretryP]"); last first; first 1 last.
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".

      (*@         px.mu.Lock()                                                    @*)
      (*@         termc := px.gettermc()                                          @*)
      (*@         lsnc := px.getlsnc()                                            @*)
      (*@         px.mu.Unlock()                                                  @*)
      (*@                                                                         @*)
      iNamed "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked [Hpx Hcomm]]".
      wp_apply (wp_Paxos__gettermc__weak with "Hpx").
      iIntros (termc) "Hpx".
      wp_apply (wp_Paxos__getlsnc__weak with "Hpx").
      iIntros (lsnc) "Hpx".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ HP]").
      { iFrame "Hlock Hlocked ∗". }
      wp_pures.

      (*@         if term != termc {                                              @*)
      (*@             // Term has changed after submission of the command, so this command @*)
      (*@             // is unlikely to be replicated.                            @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      case_bool_decide as Hterm; wp_pures; last first.
      { iApply "HΦ". by iFrame. }

      (*@         if lsn < lsnc {                                                 @*)
      (*@             // The term in which the command and the current term matches, and @*)
      (*@             // the committed LSN has passed the LSN of the command being waited, @*)
      (*@             // hence this command is guaranteed to be safe.             @*)
      (*@             safe = true                                                 @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      case_bool_decide as Hlsn; wp_pures.
      { iNamed "HP". wp_store. iApply "HΦ". by iFrame. }

      (*@         if nretry == params.N_RETRY_REPLICATED {                        @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "HP".
      wp_load.
      wp_pures.
      case_bool_decide as Hretry; wp_pures.
      { iApply "HΦ". by iFrame. }

      (*@         nretry++                                                        @*)
      (*@         primitive.Sleep(params.NS_REPLICATED_INTERVAL)                  @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_load. wp_store. wp_apply wp_Sleep. wp_pures.
      iApply "HΦ".
      by iFrame.
    }

    (*@     return safe                                                         @*)
    (*@ }                                                                       @*)
    iNamed 1.
    wp_load.
    by iApply "HΦ".
  Qed.

End program.
