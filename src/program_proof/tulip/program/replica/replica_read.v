From Perennial.program_proof.tulip.invariance Require Import execute read local_read.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_readable_key replica_bump_key replica_log.
From Perennial.program_proof.tulip.program.tuple Require Import tuple.
From Perennial.program_proof.tulip.program.index Require Import index.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__Read (rp : loc) (tsW : u64) (key : byte_string) gid rid γ :
    let ts := uint.nat tsW in
    ts ≠ O ->
    key ∈ keys_all ->
    key_to_group key = gid ->
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Read #rp #tsW #(LitString key)
    {{{ (ver : dbpver) (slow ok : bool), RET (dbpver_to_val ver, #slow, #ok);
        if ok
        then fast_or_slow_read γ rid key (uint.nat ver.1) ts ver.2 slow
        else True
    }}}.
  Proof.
    iIntros (ts Htsnz Hkey Hkg) "#Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Read(ts uint64, key string) (tulip.Version, bool, bool) { @*)
    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_Index__GetTuple with "Hidx"); first apply Hkey.
    iIntros (tpl) "#Htpl".

    (*@     v1, slow1 := tpl.ReadVersion(ts)                                    @*)
    (*@                                                                         @*)
    wp_apply (wp_Tuple__ReadVersion_xphys with "Htpl").
    { apply Htsnz. }
    iIntros (v1 slow1) "Hread1".
    wp_pures.

    (*@     if !slow1 {                                                         @*)
    (*@         // Fast-path read.                                              @*)
    (*@         return v1, false, true                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct slow1; wp_pures; last by iApply "HΦ".

    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".

    (*@     ok := rp.readableKey(ts, key)                                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_apply (wp_Replica__readableKey with "Hptsmsptsm"); first apply Hkey.
    iIntros (ok) "[Hptsmsptsm %Hreadable]".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         // Trying to read a tuple that is locked by a lower-timestamp   @*)
    (*@         // transaction. This read has to fail because the value to be read is @*)
    (*@         // undetermined---the prepared transaction might or might not commit. @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         return tulip.Version{}, false, false                            @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      by iApply ("HΦ" $! (W64 0, None)).
    }

    (*@     v2, slow2 := tpl.ReadVersion(ts)                                    @*)
    (*@                                                                         @*)
    assert (is_Some (histm !! key)) as [hist Hhist].
    { unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
      { by eauto 10. }
      pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
      by rewrite -elem_of_dom Hdomhistm.
    }
    iDestruct (big_sepM_lookup_acc with "Hhistm") as "[Hhist HhistmC]"; first apply Hhist.
    wp_apply (wp_Tuple__ReadVersion with "Htpl Hhist").
    { apply Htsnz. }
    iIntros (v2 slow2) "[Hhist #Hlb]".
    iDestruct ("HhistmC" with "Hhist") as "Hhistm".
    wp_pures.

    (*@     if !slow2 {                                                         @*)
    (*@         // Fast-path read.                                              @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         return v2, false, true                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct slow2; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Slow-path read.                                                  @*)
    (*@     rp.bumpKey(ts, key)                                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__bumpKey with "Hptsmsptsm").
    { clear -Htsnz. word. }
    { apply Hkey. }
    iIntros (spts) "[Hptsmsptsm %Hspts]".

    (*@     // TODO: An optimization is to create a log entry iff the smallest  @*)
    (*@     // preparable timestamp is actually bumped, which can be checked with the @*)
    (*@     // return value of @rp.bumpKey.                                     @*)
    (*@                                                                         @*)
    (*@     // Logical actions: Execute() and then LocalRead(@ts, @key)         @*)
    (*@     logRead(rp.fname, rp.lsna, ts, key)                                 @*)
    (*@                                                                         @*)
    wp_pures.
    iNamed "Hlsna".
    wp_loadField.
    iNamed "Hfname".
    wp_loadField.
    wp_apply wp_logRead.
    (* Open the crash, replica, and file invariants. *)
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    iNamed "Hinv".
    iInv "Hinv" as "> HinvO" "HinvC".
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iNamed "HinvfileO".
    (* Agree on the fname, and merge the two ilog quarter. *)
    iDestruct (replica_ilog_fname_agree with "Hfname Hilogfname") as %->.
    iDestruct (replica_ilog_combine with "Hilog Hilogfileinv") as "[Hilog ->]".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    (* Give the file points-to to the logging method. *)
    iFrame "Hfile %".
    iIntros (bs' failed) "Hfile".
    destruct failed.
    { (* Case: Write failed. Close the invariants without any updates. *)
      iMod "Hmask" as "_".
      iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
      iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
      { by iFrame "∗ # %". }
      iMod ("HinvC" with "HinvO") as "_".
      set dst := ReplicaDurable clog ilog.
      iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
      by iIntros "!> %Hcontra".
    }
    (* Case: Write succeeded. Update the logical state and re-establish invariant. *)
    iDestruct "Hfile" as "[Hfile %Hencilog']".
    iNamed "HinvO".
    iNamed "Hgidrid".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    (* Then snoc the new inconsistent command. *)
    iMod (replica_inv_local_read key ts with "Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp & #Hpromise & #Hrepllb)".
    { apply Hkey. }
    { apply Hkg. }
    { apply Hexec. }
    { simpl.
      rewrite /key_readable in Hreadable.
      destruct (ptsm !! key) as [pts |] eqn:Hpts; rewrite Hpts in Hreadable; last done.
      exists spts, pts.
      do 3 (split; first done).
      clear -Hreadable. word.
    }
    (* Close the file, replica, and crash invariants. *)
    iDestruct (replica_ilog_split with "Hilog") as "[Hilog Hilogfileinv]".
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "[Hfile Hilogfileinv]") as "_".
    { iFrame "∗ #".
      iPureIntro.
      split.
      { apply Forall_app_2; first apply Hvilog.
        rewrite Forall_singleton.
        simpl.
        split.
        { clear -Hlencloga HlsnaW. word. }
        split.
        { clear -Htsnz. rewrite /valid_ts. subst ts. word. }
        { apply Hkey. }
      }
      { by rewrite Hlencloga -HlsnaW. }
    }
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    set ilog' := ilog ++ _.
    set dst := ReplicaDurable (clog ++ cmdsa) ilog'.
    iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
    iIntros "!> _".

    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return v2, true, true                                               @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked ∗ # %".
      iPureIntro.
      split; first done.
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite list_elem_of_singleton in Hnewc.
        by inv Hnewc.
      }
      { rewrite merge_clog_ilog_snoc_ilog; last done.
        rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
        erewrite lookup_alter_Some; last apply Hspts.
        f_equal.
      }
    }
    wp_pures.
    iApply "HΦ".
    iDestruct "Hlb" as "[Hlb' %Hv2]".
    destruct Hv2 as (Hv2 & Ht2 & Hlenhist).
    rewrite Ht2.
    iFrame "Hrepllb".
    rewrite Hkg.
    iFrame "Hpromise".
    iPureIntro.
    split.
    { by rewrite -last_lookup. }
    { assert (length hist ≠ O) as Hlenhistnz.
      { intros Hz. apply nil_length_inv in Hz. by rewrite Hz in Hv2. }
      clear -Ht2 Hlenhist Hlenhistnz. word.
    }
  Qed.

End program.
