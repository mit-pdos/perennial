From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_leading paxos_log.
From Perennial.program_proof.tulip.paxos.invariance Require Import append.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section submit.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Submit (px : loc) (c : byte_string) nidme γ :
    is_paxos px nidme γ -∗
    {{{ True }}}
    <<< ∀∀ cpool, own_cpool_half γ cpool >>>
      Paxos__Submit #px #(LitString c) @ ↑paxosNS
    <<< own_cpool_half γ ({[c]} ∪ cpool) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Proof.
    iIntros "#Hinv" (Φ) "!> _ HAU".
    wp_rec.

    iNamed "Hinv".
    iApply ncfupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑paxosNS)) as "Hmask"; first solve_ndisj.
    iMod "HAU" as (cpoolcli) "[Hcpoolcli HAU]".
    iNamed "HinvO".
    iDestruct (cpool_agree with "Hcpool Hcpoolcli") as %->.
    iMod (cpool_update ({[c]} ∪ cpool) with "Hcpool Hcpoolcli") as "[Hcpool Hcpoolcli]".
    { set_solver. }
    iDestruct (cpool_witness c with "Hcpoolcli") as "#Hc".
    { set_solver. }
    iMod ("HAU" with "Hcpoolcli") as "HΦ".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[-HΦ]") as "_".
    { iFrame "∗ # %".
      iPureIntro.
      rewrite /cpool_subsume_log.
      apply (Forall_impl _ _ _ Hcsincl).
      set_solver.
    }
    iModIntro.
    (* Some cleanup to avoid name collision. *)
    iClear "Hsafelog". clear Hcsincl log.

    (*@ func (px *Paxos) Submit(v string) (uint64, uint64) {                    @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".

    (*@     if !px.leading() {                                                  @*)
    (*@         px.mu.Unlock()                                                  @*)
    (*@         return 0, 0                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__leading with "Hpx").
    iIntros (isleader) "Hpx".
    destruct isleader; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hpx $Hcomm]").
      wp_pures.
      by iApply "HΦ".
    }

    (*@     lsn := uint64(len(px.log))                                          @*)
    (*@     px.log = append(px.log, v)                                          @*)
    (*@     term := px.termc                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    subst terml.
    wp_loadField.
    wp_apply wp_slice_len.
    wp_loadField.
    wp_apply (wp_SliceAppend with "Hlog").
    iIntros (logP') "Hlog".
    wp_storeField.
    wp_loadField.
    wp_pures.

    (*@     // Logical action: Extend(@px.termc, @px.log).                      @*)
    (*@                                                                         @*)
    iNamed "Hfname".
    wp_loadField.
    wp_apply wp_logAppend.
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
      set dst := PaxosDurable termc termc log lsnc.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      by iIntros "!> %Hcontra".
    }
    (* Case: Write succeeded. *)
    iDestruct "Hfile" as "[Hfile %Hbs']".
    iMod (paxos_inv_append c with "[] Hps Hwalfile Htermc Hterml Hlogn HinvO")
      as "(Hps & Hwalfile & Htermc & Hterml & Hlogn & HinvO & #Hacpted')".
    { set_solver. }
    { by iApply big_sepL_singleton. }
    iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
    { iFrame "∗ # %".
      iPureIntro.
      apply Forall_app_2; first apply Hvdwal.
      by rewrite Forall_singleton.
    }
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HinvC" with "HinvO") as "_".
    set dst := PaxosDurable termc termc (log ++ [c]) lsnc.
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iIntros "!> Hents".
    wp_pures.

    (*@     // Potential batch optimization: Even though we update @px.log here, but it @*)
    (*@     // should be OK to not immediately write them to disk, but wait until those @*)
    (*@     // entries are sent in @LeaderSession. To prove the optimization, we'll need @*)
    (*@     // to decouple the "batched entries" from the actual entries @px.log, and @*)
    (*@     // relate only @px.log to the invariant.                            @*)
    (*@                                                                         @*)
    (*@     px.mu.Unlock()                                                      @*)
    (*@     return lsn, term                                                    @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked".
      iDestruct (terml_eq_termc_impl_not_nominiated with "Hcand") as %->; first done.
      set log' := log ++ [c].
      iAssert (own_paxos_leader px nidme termc termc log' true (dom addrm) γ)%I
        with "[$HisleaderP $HlsnpeersP $Hlsnpeers $Hps $Haocm]" as "Hleader".
      { iPureIntro.
        split; first done.
        split; last done.
        apply (map_Forall_impl _ _ _ Hlelog).
        intros _ lsn Hlsn.
        rewrite length_app /=.
        clear -Hlsn. lia.
      }
      iNamed "Hcand".
      iFrame "Hleader".
      set logc' := take (uint.nat lsnc) log'.
      iAssert (safe_ledger_above γ (dom addrm) (uint.nat termc) logc')%I as "Hcmted'".
      { subst logc'.
        rewrite (take_prefix_le _ log' (uint.nat lsnc) _); last first.
        { by apply prefix_app_r. }
        { clear -Hlsncub. word. }
        done.
      }
      iFrame "Hcmted'".
      iFrame "∗ # %".
      iSplit.
      { iDestruct "Hgebase" as (vlb) "[Hvlb %Hprefix]".
        iFrame "Hvlb".
        iPureIntro.
        trans log; [apply Hprefix | by apply prefix_app_r].
      }
      iSplit.
      { by case_decide. }
      iPureIntro.
      rewrite length_app /=.
      clear -Hlsncub. lia.
    }
    wp_pures.
    wp_loadField.
    wp_apply (wp_Cond__Broadcast with "Hcv").
    wp_pures.
    by iApply "HΦ".
  Qed.

End submit.
