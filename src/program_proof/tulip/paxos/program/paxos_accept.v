From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_log.
From Perennial.program_proof.tulip.paxos.invariance Require Import advance accept.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section accept.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__accept
    (px : loc) (lsn : u64) (term : u64) (entsP : Slice.t) (ents logleader : list byte_string)
    (nidme : u64) nids γ :
    nidme ∈ nids ->
    (uint.nat lsn ≤ length logleader)%nat ->
    drop (uint.nat lsn) logleader = ents ->
    prefix_base_ledger γ (uint.nat term) logleader -∗
    prefix_growing_ledger γ (uint.nat term) logleader -∗
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos_following_with_termc px nidme term nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents
    }}}
      Paxos__accept #px #lsn #term (to_val entsP)
    {{{ (lsna : u64) (loga : list byte_string), RET #lsna;
        own_paxos_following_with_termc px nidme term nids γ ∗
        (is_accepted_proposal_lb γ nidme (uint.nat term) loga ∨
         safe_ledger_above γ nids (uint.nat term) loga) ∗
        ⌜length loga = uint.nat lsna⌝
    }}}.
  Proof.
    iIntros (Hnidme Hlsnle Hents) "#Hpfb #Hpfg #Hfname #Hinvfile #Hinv".
    iIntros (Φ) "!> [Hpx Hents] HΦ".
    wp_rec.

    (*@ func (px *Paxos) accept(lsn uint64, term uint64, ents []string) uint64 { @*)
    (*@     if term != px.terml {                                               @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    set logc := take _ log.
    wp_loadField.
    wp_if_destruct.
    { rename Heqb into Htermne.
      wp_loadField.

      (*@         // Our log term does not match the term @term of @ents. Return an error @*)
      (*@         // if @px.lsnc < @lsn, as log consistency at @term cannot be guaranteed. @*)
      (*@         if px.lsnc != lsn {                                             @*)
      (*@             return px.lsnc                                              @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_loadField.
        rename Heqb into Hlsnne.
        iApply "HΦ".
        iSplit.
        { iFrame "Hcand Hleader HlogP".
          by iFrame "∗ # %".
        }
        iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat term) logc with "Hcmted")
          as "Hcmted'".
        { clear -Htermlc. word. }
        iFrame "Hcmted'".
        iPureIntro.
        rewrite length_take.
        lia.
      }

      (*@         // Append @ents to our own log starting at @lsn.                @*)
      (*@         px.log = px.log[: lsn]                                          @*)
      (*@         px.log = append(px.log, ents...)                                @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply (wp_SliceTake_full with "Hlog"); first word.
      iIntros "Hlog".
      iDestruct (own_slice_to_small with "Hents") as "Hents".
      wp_storeField.
      wp_loadField.
      wp_apply (wp_SliceAppendSlice with "[$Hlog $Hents]"); first done.
      iIntros (logP') "[Hlog Hents]".
      wp_storeField.

      (*@         // Update the log term to @term.                                @*)
      (*@         px.terml = term                                                 @*)
      (*@                                                                         @*)
      wp_storeField.

      (*@         // TODO: Write @px.log and @px.terml to disk.                   @*)
      (*@                                                                         @*)
      (*@         // Return LSN at the end of our log after accepting @ents.      @*)
      (*@         lsna := uint64(len(px.log))                                     @*)
      (*@                                                                         @*)
      wp_loadField.
      wp_apply wp_slice_len.
      wp_pures.

      (*@         // Logical action: Advance(term, log).                          @*)
      (*@                                                                         @*)
      iNamed "Hfname".
      wp_loadField.
      wp_apply (wp_logAdvance with "Hents").
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
        set dst := PaxosDurable term terml log lsn.
        iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
        by iIntros "!> [_ %Hcontra]".
      }
      (* Case: Write succeeded. *)
      iDestruct "Hfile" as "[Hfile %Hbs']".
      iAssert (⌜prefix logc logleader⌝)%I as %Hprefix.
      { iDestruct "Hcmted" as (p) "[Hcmted %Hple]".
        iApply (safe_ledger_prefix_base_ledger_impl_prefix with "Hcmted Hpfb HinvO").
        clear -Htermlc Htermne Hple. word.
      }
      iMod (paxos_inv_advance with "Hpfb Hpfg Hwalfile Htermc Hterml Hlsnc Hlogn HinvO")
        as "(Hwalfile & Htermc & Hterml & Hlsnc & Hlogn & HinvO & #Hacpted')".
      { apply Hnidme. }
      { clear -Htermlc Htermne. word. }
      { clear -Hlsncub. word. }
      { reflexivity. }
      { apply Hlsnle. }
      { apply Hprefix. }
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
      set dst := PaxosDurable term term logleader lsn.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      iIntros "!> Hents".
      wp_pures.

      (*@         return lsna                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      set log' := logc ++ _.
      set logc' := take (uint.nat lsn) log'.
      iInv "Hinv" as "> HinvO" "HinvC".
      iAssert (⌜logleader = log'⌝)%I as %Heq.
      { subst log'.
        iDestruct "Hcmted" as (p) "[Hsafep %Hple]".
        iPureIntro.
        rewrite -{1}(take_drop (uint.nat lsn) logleader).
        f_equal.
        subst logc.
        destruct Hprefix as [logtail ->].
        rewrite take_app_le; last first.
        { rewrite length_take. clear -Hlsncub. lia. }
        by rewrite take_idemp.
      }
      iMod ("HinvC" with "HinvO") as "_".
      iDestruct (safe_ledger_above_mono (uint.nat terml) (uint.nat term) logc' with "[]")
        as "Hcmted'".
      { word. }
      { subst logc'.
        rewrite take_app_le; last first.
        { rewrite length_take. lia. }
        by rewrite take_idemp.
      }
      iClear "Hcmted".
      iApply "HΦ".
      iModIntro.
      iSplit.
      { iFrame "Hcand Hleader HlogP HtermlP".
        iClear "Hpreped".
        case_decide; last done.
        iFrame "∗".
        rewrite Heq.
        iFrame "∗ # %".
        iPureIntro.
        split; first done.
        rewrite -Heq.
        word.
      }
      iFrame "Hacpted'".
      rewrite Heq.
      iApply (own_slice_sz with "Hlog").
    }

    (*@     // We're in the same term. Now we should skip appending @ents iff there's @*)
    (*@     // gap between @ents and @px.log OR appending @ents starting at @lsn @*)
    (*@     // actually shortens the log.                                       @*)
    (*@     nents := uint64(len(px.log))                                        @*)
    (*@     if nents < lsn || lsn + uint64(len(ents)) <= nents {                @*)
    (*@         return nents                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply (wp_or with "[Hents]").
    { iNamedAccu. }
    { wp_pures. done. }
    { iIntros "_".
      iNamed 1.
      wp_apply wp_slice_len.
      wp_pures.
      by iFrame.
    }
    iNamed 1.
    wp_if_destruct.
    { iApply "HΦ".
      iModIntro.
      iSplit.
      { iFrame "Hcand Hleader HlogP".
        by iFrame "∗ # %".
      }
      iFrame "Hacpted".
      iApply (own_slice_sz with "Hlog").
    }
    apply Classical_Prop.not_or_and in Heqb.
    destruct Heqb as [Hnogap Hlonger].
    rewrite Z.nlt_ge in Hnogap.
    rewrite Z.nle_gt in Hlonger.
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.

    (*@     // Append @ents to our own log starting at @lsn.                    @*)
    (*@     px.log = px.log[: lsn]                                              @*)
    (*@     px.log = append(px.log, ents...)                                    @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_SliceTake_full with "Hlog").
    { clear -Hnogap Hszlog. word. }
    iIntros "Hlog".
    wp_storeField.
    wp_loadField.
    iDestruct (own_slice_to_small with "Hents") as "Hents".
    wp_apply (wp_SliceAppendSlice with "[$Hlog $Hents]"); first done.
    iIntros (logP') "[Hlog Hents]".
    wp_storeField.

    (*@     lsna := uint64(len(px.log))                                         @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.

    (*@     // Logical action: Accept(term, log)                                @*)
    (*@     logAccept(px.fname, lsn, ents)                                      @*)
    (*@                                                                         @*)
    iDestruct (own_slice_small_sz with "Hents") as %Hszents.
    assert (length log ≤ length logleader)%nat as Hlenlog.
    { rewrite length_drop in Hszents.
      rewrite word.unsigned_add in Hlonger.
      clear -Hszlog Hszents Hnogap Hlonger.
      word.
    }
    iNamed "Hfname".
    wp_loadField.
    wp_apply (wp_logAccept with "Hents").
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
      set dst := PaxosDurable terml terml log lsnc.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      by iIntros "!> [_ %Hcontra]".
    }
    (* Case: Write succeeded. *)
    iDestruct "Hfile" as "[Hfile %Hbs']".
    iMod (paxos_inv_accept (uint.nat lsn) with "Hpfb Hpfg Hwalfile Htermc Hterml Hlogn HinvO")
      as "(Hwalfile & Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { apply Hnidme. }
    { apply Hlenlog. }
    { clear -Hnogap Hszlog. word. }
    { reflexivity. }
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
    set dst := PaxosDurable terml terml logleader lsnc.
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iIntros "!> Hents".
    wp_pures.

    (*@     return lsna                                                         @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! _ logleader).
    iAssert (⌜prefix log logleader⌝)%I as %Hprefix.
    { iDestruct (accepted_proposal_lb_prefix with "Hacpted Hacpted'") as %Hprefix.
      iPureIntro.
      destruct Hprefix as [? | Hprefix]; first done.
      by rewrite (prefix_length_eq _ _ Hprefix Hlenlog).
    }
    assert (take (uint.nat lsn) log = take (uint.nat lsn) logleader) as ->.
    { rewrite (take_prefix_le _ _ (uint.nat lsn) _ Hprefix); first done.
      clear -Hnogap Hszlog. word.
    }
    rewrite take_drop.
    iModIntro.
    iSplit.
    { iFrame "Hcand Hleader HlogP HtermlP".
      case_decide; last done.
      set logc' := take (uint.nat lsnc) logleader.
      iAssert (safe_ledger_above γ nids (uint.nat terml) logc')%I as "Hcmted'".
      { subst logc.
        rewrite (take_prefix_le _ _ (uint.nat lsnc) _ Hprefix); first done.
        clear -Hlsncub. word.
      }
      iFrame "Hcmted'".
      iFrame "∗ # %".
      iPureIntro.
      apply prefix_length in Hprefix.
      clear -Hlsncub Hprefix.
      word.
    }
    iFrame "Hacpted'".
    by iApply (own_slice_sz with "Hlog").
  Qed.

End accept.
