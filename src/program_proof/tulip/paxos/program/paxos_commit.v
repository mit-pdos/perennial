From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_log.
From Perennial.program_proof.tulip.paxos.invariance Require Import expand.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section commit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__commit
    (px : loc) (lsn : u64) (nidme term : u64) (logc : list byte_string) nids γ :
    nidme ∈ nids ->
    length logc = uint.nat lsn ->
    safe_ledger_above γ nids (uint.nat term) logc -∗
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}
      Paxos__commit #px #lsn
    {{{ RET #(); own_paxos_with_termc_terml_iscand px nidme term term false nids γ }}}.
  Proof.
    iIntros (Hnidme Hlenlogc) "#Hsafe #Hfname #Hinvfile #Hinv".
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
      iNamed "Hfname".
      do 2 wp_loadField.
      wp_apply wp_logExpand.
      iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
      { solve_ndisj. }
      iNamed "Hdurable".
      iInv "Hinv" as "> HinvO" "HinvC".
      iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
      iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hnodefile HinvfileO]".
      { apply Hnidme. }
      iNamed "Hnodefile".
      iApply ncfupd_mask_intro; first solve_ndisj.
      iIntros "Hmask".
      iDestruct (node_wal_fname_agree with "Hfnameme Hwalfname") as %->.
      iFrame "Hfile %".
      iIntros (bs' failed) "Hfile".
      destruct failed.
      { (* Case: Write failed. Close the invariant without any updates. *)
        iMod "Hmask" as "_".
        iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
        { iFrame "∗ # %". }
        iMod ("HinvfileC" with "HinvfileO") as "_".
        iMod ("HinvC" with "HinvO") as "_".
        set dst := PaxosDurable term term log lsnc.
        iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
        by iIntros "!> %Hcontra".
      }
      (* Case: Write succeeded. *)
      iDestruct "Hfile" as "[Hfile %Hbs']".
      iMod (paxos_inv_expand (length log) with "[Hsafe'] Hwalfile Hterml Hlsnc Hlogn HinvO")
        as "(Hwalfile & Hterml & Hlsnc & Hlogn & HinvO)".
      { apply Hnidme. }
      { clear -Hlsncub. lia. }
      { done. }
      { by rewrite Hszlog. }
      rewrite -Hszlog in Hbs'.
      iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
      { iFrame "∗ # %".
        iPureIntro.
        apply Forall_app_2; first apply Hvdwal.
        rewrite Forall_singleton /=.
        word.
      }
      iMod "Hmask" as "_".
      iMod ("HinvfileC" with "HinvfileO") as "_".
      iMod ("HinvC" with "HinvO") as "_".
      set dst := PaxosDurable term term log logP.(Slice.sz).
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn Hlsnc]") as "Hdurable".
      { by rewrite Hszlog. }
      iIntros "!> _".
      wp_pures.

      (*@         return                                                          @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      iApply "HΦ".
      iFrame "Hcand Hleader".
      iFrame "Hsafe'".
      iFrame "∗ # %".
      iPureIntro.
      clear -Hszlog. word.
    }
    rename Heqb into Hlelog.
    rewrite Z.nlt_ge in Hlelog.

    (*@     px.lsnc = lsn                                                       @*)
    (*@                                                                         @*)
    wp_storeField.

    (*@     // Logical action: Expand(lsn)                                      @*)
    (*@                                                                         @*)
    iNamed "Hfname".
    wp_loadField.
    wp_apply wp_logExpand.
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    iInv "Hinv" as "> HinvO" "HinvC".
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hnodefile HinvfileO]".
    { apply Hnidme. }
    iNamed "Hnodefile".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iDestruct (node_wal_fname_agree with "Hfnameme Hwalfname") as %->.
    iFrame "Hfile %".
    iIntros (bs' failed) "Hfile".
    destruct failed.
    { (* Case: Write failed. Close the invariant without any updates. *)
      iMod "Hmask" as "_".
      iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
      { iFrame "∗ # %". }
      iMod ("HinvfileC" with "HinvfileO") as "_".
      iMod ("HinvC" with "HinvO") as "_".
      set dst := PaxosDurable term term log lsnc.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      by iIntros "!> %Hcontra".
    }
    (* Case: Write succeeded. *)
    iDestruct "Hfile" as "[Hfile %Hbs']".
    assert (Hprefix : prefix logc log).
    { destruct Horprefix as [Hprefix | ?]; last done.
      rewrite (prefix_length_eq _ _ Hprefix); first done.
      lia.
    }
    set logc' := take (uint.nat lsn) log.
    iDestruct (safe_ledger_above_weaken logc' with "Hsafe") as "Hsafe'".
    { subst logc'. by rewrite -Hlenlogc take_length_prefix. }
    iMod (paxos_inv_expand (uint.nat lsn) with "Hsafe' Hwalfile Hterml Hlsnc Hlogn HinvO")
      as "(Hwalfile & Hterml & Hlsnc & Hlogn & HinvO)".
    { apply Hnidme. }
    { clear -Hgtlsnc. lia. }
    { rewrite Hszlog. clear -Hlelog. lia. }
    iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
    { iFrame "∗ # %".
      iPureIntro.
      apply Forall_app_2; first apply Hvdwal.
      rewrite Forall_singleton /=.
      word.
    }
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HinvC" with "HinvO") as "_".
    set dst := PaxosDurable term term log lsn.
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iIntros "!> _".
    wp_pures.
    iApply "HΦ".
    iFrame "Hcand Hleader ∗ # %".
    iPureIntro.
    clear -Hlelog Hszlog. word.
  Qed.

End commit.
