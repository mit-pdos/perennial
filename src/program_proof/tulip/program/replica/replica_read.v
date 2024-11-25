From Perennial.program_proof.tulip.invariance Require Import execute read local_read.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_readable_key replica_bump_key replica_log.
From Perennial.program_proof.tulip.program.tuple Require Import tuple.
From Perennial.program_proof.tulip.program.index Require Import index.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__Read (rp : loc) (tsW : u64) (key : string) gid rid γ :
    let ts := uint.nat tsW in
    ts ≠ O ->
    key ∈ keys_all ->
    key_to_group key = gid ->
    is_replica rp gid rid γ -∗
    {{{ True }}}
      Replica__Read #rp #tsW #(LitString key)
    {{{ (t : u64) (v : dbval) (ok : bool), RET (#t, dbval_to_val v, #ok);
        if ok
        then fast_or_slow_read γ rid key (uint.nat t) ts v
        else True
    }}}.
  Proof.
    iIntros (ts Htsnz Hkey Hkg) "#Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Read(ts uint64, key string) (uint64, tulip.Value, bool) { @*)
    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_Index__GetTuple with "Hidx"); first apply Hkey.
    iIntros (tpl) "#Htpl".

    (*@     t1, v1 := tpl.ReadVersion(ts)                                       @*)
    (*@                                                                         @*)
    wp_apply (wp_Tuple__ReadVersion_xphys with "Htpl").
    iIntros (t1 v1) "Hread1".
    wp_pures.

    (*@     if t1 == 0 {                                                        @*)
    (*@         // Fast-path read.                                              @*)
    (*@         return 0, v1, true                                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Ht1; wp_pures.
    { iApply "HΦ". by case_decide; last inv Ht1. }

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
    (*@         return 0, tulip.Value{}, false                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      by iApply ("HΦ" $! _ None).
    }

    (*@     t2, v2 := tpl.ReadVersion(ts)                                       @*)
    (*@                                                                         @*)
    assert (is_Some (histm !! key)) as [hist Hhist].
    { unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
      { by eauto 10. }
      pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
      by rewrite -elem_of_dom Hdomhistm.
    }
    iDestruct (big_sepM_lookup_acc with "Hhistm") as "[Hhist HhistmC]"; first apply Hhist.
    wp_apply (wp_Tuple__ReadVersion with "Htpl Hhist").
    iIntros (t2 v2) "[Hhist #Hlb]".
    iDestruct ("HhistmC" with "Hhist") as "Hhistm".
    wp_pures.

    (*@     if t2 == 0 {                                                        @*)
    (*@         // Fast-path read.                                              @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         return 0, v2, true                                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Ht2; wp_pures.
    { wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗ # %". }
      wp_pures.
      iApply "HΦ".
      by case_decide; last inv Ht2.
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
    (*@     rp.logRead(ts, key)                                                 @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply wp_Replica__logRead.
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
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
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iModIntro.

    (*@     rp.mu.Unlock()                                                      @*)
    (*@     return t2, v2, true                                                 @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked ∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split; first done.
      split.
      { rewrite Forall_forall.
        intros [n c] Hilog. simpl.
        apply elem_of_app in Hilog as [Hilog | Hnewc].
        { rewrite Forall_forall in Hvicmds. by specialize (Hvicmds _ Hilog). }
        rewrite elem_of_list_singleton in Hnewc.
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
    rewrite /fast_or_slow_read.
    case_decide as Hnz; first done.
    iDestruct "Hlb" as "[Hlb' %Hv2]".
    clear Ht2.
    destruct Hv2 as (Hv2 & Ht2 & Hlenhist).
    rewrite Ht2.
    iFrame "Hrepllb".
    rewrite Hkg.
    iFrame "Hpromise".
    iPureIntro.
    split.
    { by rewrite -last_lookup. }
    { clear -Ht2 Hnz Hlenhist. word. }
  Qed.

End program.
