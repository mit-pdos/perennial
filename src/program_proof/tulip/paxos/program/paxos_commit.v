From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Perennial.program_proof.tulip.paxos.invariance Require Import expand.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section commit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__commit
    (px : loc) (lsn : u64) (nidme term : u64) (logc : list string) nids γ :
    nidme ∈ nids ->
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}
      Paxos__commit #px #lsn
    {{{ RET #(); own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}.
  Proof.
    iIntros (Hnidme Hlenlogc) "#Hsafe #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) commit(lsn uint64) {                                   @*)
    (*@     if lsn <= px.lsnc {                                                 @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    wp_loadField.
    wp_if_destruct.
    { iApply "HΦ".
      iFrame "Hleader Hcand".
      by iFrame "∗ # %".
    }
    rename Heqb into Hgtlsnc.
    rewrite Z.nle_gt in Hgtlsnc.
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iAssert (⌜prefix log logc ∨ prefix logc log⌝)%I as %Horprefix.
    { iDestruct "Hsafe" as (p) "[Hsafe %Hple]".
      destruct (decide (p = uint.nat term)) as [-> | Hne]; last first.
      { iDestruct (safe_ledger_prefix_base_ledger_impl_prefix with "Hsafe Hgebase HinvO")
          as %Hprefix.
        { clear -Hple Hne. lia. }
        iPureIntro.
        by right.
      }
      iNamed "Hsafe".
      iDestruct (paxos_inv_impl_nodes_inv_psa with "HinvO") as (bs) "[Hnodes %Hdombs]".
      iApply (nodes_inv_is_accepted_proposal_lb_impl_prefix with "Hacpted Hvacpt Hnodes").
      { rewrite Hdombs. apply Hnidme. }
      { by rewrite Hdombs. }
    }
    iMod ("HinvC" with "HinvO") as "_".
    iModIntro.

    (*@     if uint64(len(px.log)) < lsn {                                      @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { rename Heqb into Hgtlog.

      (*@         px.lsnc = uint64(len(px.log))                                   @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply wp_slice_len.
      wp_storeField.
      destruct Horprefix as [Hprefix | Hprefix]; last first.
      { apply prefix_length in Hprefix. exfalso.
        clear -Hgtlog Hprefix Hszlog Hlenlogc. word.
      }
      set logc' := take (uint.nat logP.(Slice.sz)) log.
      iDestruct (safe_ledger_above_weaken logc' with "Hsafe") as "Hsafe'".
      { subst logc'. rewrite -Hszlog firstn_all. apply Hprefix. }

      (*@         // Logical action: Expand(len(px.log))                          @*)
      (*@                                                                         @*)
      iInv "Hinv" as "> HinvO" "HinvC".
      iMod (paxos_inv_expand (length log) with "[Hsafe'] Hterml Hlsnc Hlogn HinvO")
        as "(Hterml & Hlsnc & Hlogn & HinvO)".
      { apply Hnidme. }
      { clear -Hlsncub. lia. }
      { done. }
      { by rewrite Hszlog. }
      iMod ("HinvC" with "HinvO") as "_".

      (*@         return                                                          @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      iApply "HΦ".
      iFrame "Hcand Hleader".
      iFrame "Hsafe'".
      rewrite -Hszlog.
      iFrame "∗ # %".
      iPureIntro.
      clear -Hszlog. word.
    }
    rename Heqb into Hlelog.
    rewrite Z.nlt_ge in Hlelog.

    (*@     px.lsnc = lsn                                                       @*)
    (*@                                                                         @*)
    wp_storeField.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    assert (Hprefix : prefix logc log).
    { destruct Horprefix as [Hprefix | ?]; last done.
      rewrite (prefix_length_eq _ _ Hprefix); first done.
      lia.
    }
    set logc' := take (uint.nat lsn) log.
    iDestruct (safe_ledger_above_weaken logc' with "Hsafe") as "Hsafe'".
    { subst logc'. by rewrite -Hlenlogc take_length_prefix. }

    (*@     // Logical action: Expand(lsn)                                      @*)
    (*@                                                                         @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (paxos_inv_expand (uint.nat lsn) with "Hsafe' Hterml Hlsnc Hlogn HinvO")
      as "(Hterml & Hlsnc & Hlogn & HinvO)".
    { apply Hnidme. }
    { clear -Hgtlsnc. lia. }
    { rewrite Hszlog. clear -Hlelog. lia. }
    iMod ("HinvC" with "HinvO") as "_".
    iFrame "Hsafe'".
    iFrame "∗ # %".
    iPureIntro.
    clear -Hlelog Hszlog. word.

    (*@     // TODO: Write @px.lsnc to disk.                                    @*)
    (*@ }                                                                       @*)
  Qed.

End commit.
