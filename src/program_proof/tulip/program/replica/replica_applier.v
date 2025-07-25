From Perennial.program_proof.tulip.invariance Require Import learn.
From Perennial.program_proof Require Import std_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import  replica_repr replica_apply.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.paxos Require Import base.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__Applier rp gid rid γ :
    is_replica_plus_txnlog rp gid rid γ -∗
    {{{ True }}}
      Replica__Applier #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Start() {                                            @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    do 2 iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@         // TODO: a more efficient interface would return multiple safe commands @*)
    (*@         // at once (so as to reduce the frequency of acquiring Paxos mutex). @*)
    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@                                                                         @*)
    set P := (λ b : bool, own_replica rp gid rid γ α ∗ locked #mu)%I.
    wp_apply (wp_forBreak P with "[] [$Hrp $Hlocked]"); last first.
    { (* Get out of an infinite loop. *)
      iIntros "Hrp". wp_pures. by iApply "HΦ".
    }
    clear Φ. iIntros "!>" (Φ) "[Hrp Hlocked] HΦ".
    wp_rec.
    do 2 iNamed "Hrp". iNamed "Hlsna".
    wp_loadField.

    (*@         cmd, ok := rp.txnlog.Lookup(rp.lsna)                            @*)
    (*@                                                                         @*)
    iNamed "Htxnlog".
    wp_loadField.
    wp_apply (wp_TxnLog__Lookup with "Htxnlog").
    iNamed "Hinv".
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    (* Take the required group invariant. *)
    iNamed "Hgidrid".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    (* Separate out the ownership of the Paxos log from others. *)
    iDestruct (group_inv_extract_log_expose_cpool with "Hgroup") as (paxos cpool) "[Hpaxos Hgroup]".
    (* Obtain validity of command input on cpool. *)
    iDestruct (group_inv_impl_valid_ccommand_cpool with "[Hgroup Hpaxos]") as %Hvcmds.
    { iNamed "Hgroup". iFrame. }
    (* Obtain a lower bound before passing it to Paxos. *)
    iDestruct (txn_log_witness with "Hpaxos") as "#Hlb".
    iNamed "Hgroup".
    iFrame.
    iIntros (paxos') "[[Hpaxos Hcpool] %Hincl]".
    (* Obtain prefix between the old and new logs. *)
    iDestruct (txn_log_prefix with "Hpaxos Hlb") as %Hpaxos.
    destruct Hpaxos as [cmds Hpaxos].
    (* Obtain inclusion between the command pool and the log. *)
    (* iAssert (⌜txn_cpool_subsume_log cpool paxos'⌝)%I as %Hincl. *)
    (* { iNamed "Hgroup". *)
    (*   by iDestruct (txn_log_cpool_incl with "Hpaxos Hcpool") as %?. *)
    (* } *)
    (* Transfer validity of command input on cpool to log; used when executing @apply. *)
    pose proof (set_Forall_Forall_subsume _ _ _ Hvcmds Hincl) as Hvc.
    (* Obtain prefix between the applied log and the new log; needed later. *)
    iDestruct (txn_log_prefix with "Hpaxos Hclogalb") as %Hloga.
    (* Obtain a witness of the new log; needed later. *)
    iDestruct (txn_log_witness with "Hpaxos") as "#Hlbnew".
    subst paxos'.

    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@                                                                         @*)
    iAssert (group_inv_no_log_with_cpool γ gid paxos cpool)%I with "[$Hgroup $Hcpool]" as "Hgroup".
    iMod (group_inv_learn with "Htxnsys Hkeys Hgroup") as "(Htxnsys & Hkeys & Hgroup)".
    { apply Hincl. }
    iDestruct (group_inv_merge_log_hide_cpool with "Hpaxos Hgroup") as "Hgroup".
    (* Put back the group invariant. *)
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    (* Close the entire invariant. *)
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iIntros "!>" (cmd ok pwrsS) "[HpwrsS  %Hcmd]".
    wp_pures.

    (*@         if !ok {                                                        @*)
    (*@             // Sleep for 1 ms.                                          @*)
    (*@             rp.mu.Unlock()                                              @*)
    (*@             primitive.Sleep(1 * 1000000)                                @*)
    (*@             rp.mu.Lock()                                                @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    destruct ok; wp_pures; last first.
    { (* Have applied all the commands known to be committed. *)
      wp_loadField.
      iClear "Hlb Hlbnew".
      wp_apply (wp_Mutex__Unlock with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
      wp_apply wp_Sleep.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hrp]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    (* Obtain a witness for the newly applied log. *)
    iClear "Hlb".
    (* Prove the newly applied log is a prefix of the new log. *)
    assert (Hprefix : prefix (cloga ++ [cmd]) (paxos ++ cmds)).
    { clear -Hloga Hcmd HlsnaW Hlencloga.
      destruct Hloga as [l Hl].
      rewrite Hl.
      apply prefix_app, prefix_singleton.
      rewrite Hl lookup_app_r in Hcmd; last lia.
      by rewrite HlsnaW Hlencloga /= Nat.sub_diag in Hcmd.
    }
    iDestruct (txn_log_lb_weaken (cloga ++ [cmd]) with "Hlbnew") as "#Hlb"; first apply Hprefix.
    (* Obtain lbs of replicated history over the new history map. *)
    iApply fupd_wp.
    iInv "Hinv" as "> HinvO" "HinvC".
    (* Take the required group invariant. *)
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (group_inv_witness_group_histm_lbs_from_log with "Hlb Hgroup") as "#Hhistmlb".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iModIntro.

    (*@         rp.apply(cmd)                                                   @*)
    (*@                                                                         @*)
    iAssert (own_replica_with_cloga_no_lsna rp cloga gid rid γ α)%I
      with "[Hcm Hhistm Hcpm Hpgm Hptsmsptsm Hpsmrkm Hdurable]" as "Hrp".
    { iFrame "∗ # %". }
    wp_apply (wp_Replica__apply with "Hhistmlb Hlb Hidx [$HpwrsS $Hrp]").
    { rewrite Forall_forall in Hvc.
      apply Hvc.
      by apply list_elem_of_lookup_2 in Hcmd.
    }
    iIntros "Hrp".


    (*@         rp.lsna = std.SumAssumeNoOverflow(rp.lsna, 1)                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hnoof).
    wp_storeField.

    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    iPureIntro. simpl.
    exists (S lsna).
    split.
    { rewrite uint_nat_word_add_S; last word.
      by rewrite HlsnaW.
    }
    { rewrite length_app /= Hlencloga. lia. }
  Qed.

End program.
