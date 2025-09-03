From Perennial.program_proof.rsm.pure Require Import serialize.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import  replica_repr.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program.util Require Import
  decode_string decode_ints.
From Goose.github_com.mit_pdos.tulip Require Import replica.
From Perennial.program_proof.tulip.paxos Require Import prelude.

(* for replay *)
From Perennial.program_proof.tulip.program.util Require Import
  decode_string decode_kvmap_into_slice.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_apply replica_bump_key replica_acquire replica_memorize
  replica_advance replica_accept.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.invariance Require Import learn.

Opaque u64_le.

(* Copy pasted from grove_ffi_typed.v *)
Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.
Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Local Ltac solve_atomic2 :=
  solve_atomic;
  (* TODO(Joe): Cleanup *)
  repeat match goal with
    | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
    | _ => progress monad_inv
    | _ => case_match
    end; eauto.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__replay (rp : loc) (lsnW : u64) ilog gid γ α :
    let lsn := uint.nat lsnW in
    gid ∈ gids_all ->
    Forall (λ nc : nat * icommand, (nc.1 <= lsn)%nat) ilog ->
    know_tulip_inv γ -∗
    is_replica_idx rp γ α -∗
    is_replica_txnlog rp gid γ -∗
    {{{ own_replica_replaying_in_lsn rp lsn ilog gid γ α }}}
      Replica__replay #rp #lsnW
    {{{ RET #(); own_replica_replaying_in_lsn rp (S lsn) ilog gid γ α }}}.
  Proof.
    iIntros (lsn Hgid Hlsn) "#Hinv #Hidx #Htxnlog".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) replay(lsn uint64) {                                 @*)
    (*@     var cmd txnlog.Cmd                                                  @*)
    (*@     var ok bool = false                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (cmdP) "HcmdP".
    wp_apply wp_ref_to; first by auto.
    iIntros (okP) "HokP".

    (*@     for !ok {                                                           @*)
    (*@         cmd, ok = rp.txnlog.Lookup(lsn)                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    set P := (λ cont : bool,
                ∃ (pwrsS : Slice.t) (cmd : ccommand) (ok : bool),
                  "HcmdP"  ∷ cmdP ↦[struct.t Cmd] (ccommand_to_val pwrsS cmd) ∗
                  "HokP"   ∷ okP ↦[boolT] #ok ∗
                  "Hpwrs"  ∷ (if ok then own_pwrs_slice pwrsS cmd else True) ∗
                  "#Hlb"   ∷ (if ok then is_txn_log_lb γ gid (clog ++ [cmd]) else True) ∗
                  "%Hcont" ∷ ⌜if cont then True else ok⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HcmdP HokP]"); last first; first 1 last.
    { iFrame.
      iExists Slice.nil, (CmdAbort O).
      rewrite /= Nat2Z.inj_0.
      by iFrame.
    }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      destruct ok; wp_pures.
      { (* Loop exit. *)
        iApply "HΦ".
        by iFrame "HcmdP HokP Hpwrs Hlb".
      }
      iNamed "Htxnlog".
      wp_loadField.
      wp_apply (wp_TxnLog__Lookup with "Htxnlog").
      iDestruct "Hinv" as (proph) "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
      { apply Hgid. }
      iNamed "Hgroup".
      iDestruct (txn_log_witness with "Hlog") as "#Hloglb".
      (* Pass the consensus resources to the paxos library. *)
      iFrame "Hlog Hcpool".
      (* Get back the updated resources. *)
      iIntros (log') "[[Hlog Hcpool] %Hincl]".
      iDestruct (txn_log_witness with "Hlog") as "#Hloglb'".
      iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
      destruct Hprefix as [l Hprefix].
      iDestruct (txn_log_prefix with "Hlog Hcloglb") as %Hprefixc.
      iAssert (group_inv_no_log_with_cpool γ gid log cpool)%I with "[$Hgroup $Hcpool]" as "Hgroup".
      iMod (group_inv_learn with "Htxnsys Hkeys Hgroup") as "(Htxnsys & Hkeys & Hgroup)".
      { by rewrite Hprefix in Hincl. }
      rewrite -Hprefix.
      iDestruct (group_inv_merge_log_hide_cpool with "Hlog Hgroup") as "Hgroup".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod "Hmask" as "_".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iModIntro.
      iClear "Hpwrs".
      iIntros (c ok pwrsP) "[Hpwrs %Hc]".
      wp_pures.
      wp_apply (wp_StoreAt with "HcmdP").
      { destruct c; simpl; by auto 10. }
      iIntros "HcmdP".
      wp_store.
      iApply "HΦ".
      iFrame.
      destruct ok; last done.
      iDestruct (txn_log_lb_weaken (clog ++ [c]) with "Hloglb'") as "Hcloglb'".
      { destruct Hprefixc as [lc Hprefixc].
        rewrite Hprefixc.
        apply prefix_app, prefix_singleton.
        rewrite Hprefixc lookup_app_r in Hc; last first.
        { clear -Hlenclog. lia. }
        by rewrite Hlenclog Nat.sub_diag in Hc.
      }
      by iFrame "#".
    }

    (*@     rp.apply(cmd)                                                       @*)
    (*@ }                                                                       @*)
    iNamed 1.
    destruct ok; last done.
    iAssert (|={⊤}=>
               group_histm_lbs_from_log γ gid (clog ++ [cmd]) ∗
               ⌜valid_ccommand gid cmd⌝)%I as "> [#Hhistm %Hvcmd]".
    { iDestruct "Hinv" as (proph) "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
      { apply Hgid. }
      iDestruct (group_inv_impl_valid_ccommand_log with "Hlb Hgroup")
        as %Hvcmds.
      apply Forall_app in Hvcmds as [_ Hvcmd].
      rewrite Forall_singleton in Hvcmd.
      iDestruct (group_inv_witness_group_histm_lbs_from_log with "Hlb Hgroup")
        as "#Hhistm".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iModIntro.
      by iFrame "Hhistm".
    }
    wp_load.
    wp_apply (wp_Replica__apply__replaying with "[] Hidx [$Hrp $Hpwrs]").
    { rewrite Hlenclog. apply Hlsn. }
    { apply Hvcmd. }
    { iFrame "Hhistm". }
    iIntros "Hrp".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ #".
    iPureIntro.
    rewrite length_app /= Hlenclog.
    lia.
  Qed.

  Theorem wp_Replica__replayBetween
    (rp : loc) (lsnxW : u64) (lsnyW : u64) ilog gid γ α :
    let lsnx := uint.nat lsnxW in
    let lsny := uint.nat lsnyW in
    gid ∈ gids_all ->
    Forall (λ nc : nat * icommand, (nc.1 <= lsnx)%nat) ilog ->
    (lsnx ≤ lsny)%nat ->
    know_tulip_inv γ -∗
    is_replica_idx rp γ α -∗
    is_replica_txnlog rp gid γ -∗
    {{{ own_replica_replaying_in_lsn rp lsnx ilog gid γ α }}}
      Replica__replayBetween #rp #lsnxW #lsnyW
    {{{ RET #(); own_replica_replaying_in_lsn rp lsny ilog gid γ α }}}.
  Proof.
    iIntros (lsnx lsny Hgid Hlsnx Hxy) "#Hinv #Hidx #Htxnlog".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) replayBetween(lsnx, lsny uint64) {                   @*)
    (*@     for lsn := lsnx; lsn < lsny; lsn++ {                                @*)
    (*@         rp.replay(lsn)                                                  @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (lsnP) "HlsnP".
    set P := (λ lsnW : u64,
                "Hrp"  ∷ own_replica_replaying_in_lsn rp (uint.nat lsnW) ilog gid γ α ∗
                "%Hge" ∷ ⌜(lsnx ≤ uint.nat lsnW)%nat⌝)%I.
    wp_pures.
    wp_apply (wp_forUpto P with "[] [$Hrp $HlsnP]").
    { clear -Hxy. word. }
    { clear Φ.
      iIntros (lsnW Φ) "!> (HP & HlsnP & %Hbound) HΦ".
      wp_load.
      iNamed "HP".
      wp_apply (wp_Replica__replay with "Hinv Hidx Htxnlog Hrp").
      { apply Hgid. }
      { apply (Forall_impl _ _ _ Hlsnx). clear -Hge. intros. word. }
      iIntros "Hrp".
      wp_pures.
      iApply "HΦ".
      subst P. simpl.
      rewrite uint_nat_word_add_S; last first.
      { clear -Hbound. word. }
      iFrame.
      iPureIntro. clear -Hge. word.
    }
    { done. }
    iIntros "[HP HlsnP]".
    iNamed "HP".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_Replica__resume
    (rp : loc) (clog : dblog) (ilog : list (nat * icommand)) gid rid γ α :
    let dst := ReplicaDurable clog ilog in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    know_tulip_inv γ -∗
    know_replica_file_inv γ gid rid -∗
    is_replica_fname rp gid rid γ -∗
    is_replica_idx rp γ α -∗
    is_replica_txnlog rp gid γ -∗
    {{{ own_replica_replaying rp [] [] α ∗
        own_replica_lsna rp O ∗
        own_crash_ex (stagedG0 := tulip_ghostG0.(@tulip_stagedG Σ)) rpcrashNS (own_replica_durable γ gid rid) dst
    }}}
      Replica__resume #rp
    {{{ RET #();
        own_replica_replaying rp clog ilog α ∗
        own_replica_lsna rp (length clog) ∗
        own_crash_ex (stagedG0 := tulip_ghostG0.(@tulip_stagedG Σ)) rpcrashNS (own_replica_durable γ gid rid) dst
    }}}.
  Proof.
    iIntros (dst Hgid Hrid) "#Hinv #Hinvfile #Hfname #Hidx #Htxnlog".
    iIntros (Φ) "!> (Hrp & Hlsna & Hdurable) HΦ".
    wp_rec.

    (*@ func (rp *Replica) resume() {                                           @*)
    (*@     // Set the starting LSN to 0.                                       @*)
    (*@     var lsnx uint64 = 0                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (lsnxP) "HlsnxP".

    (*@     // Read the inconsistent log.                                       @*)
    (*@     var data = grove_ffi.FileRead(rp.fname)                             @*)
    (*@                                                                         @*)
    iNamed "Hfname".
    wp_loadField.
    wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    (* Open the file invariant to obtain (1) the file points-to, (2) encoding
    relation between the file content and the inconsistent log. *)
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iNamed "HinvfileO".
    iDestruct (replica_ilog_fname_agree with "Hfname Hilogfname") as %->.
    iDestruct (replica_ilog_agree with "Hilog Hilogfileinv") as %->.
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    wp_apply (wp_FileReadOp with "Hfile").
    iIntros (err p len) "[Hfile HdataP]".
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "[Hilogfileinv Hfile]") as "_".
    { iFrame "∗ # %". }
    iMod ("HdurableC" $! dst with "[$Hclog $Hilog]") as "Hdurable".
    iModIntro.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    iDestruct "HdataP" as "[%Hlen HdataP]".
    set dataP := Slice.mk p len len.
    iDestruct (pointsto_vals_own_slice_small_byte dataP with "HdataP") as "Hdata".
    { done. }
    { subst dataP; simpl. word. }
    wp_apply wp_ref_to.
    { apply (slice_val_ty dataP). }
    iIntros (dataPP) "HdataPP".
    wp_pures.

    iAssert (|NC={⊤}=>
               (own_crash_ex (stagedG0 := tulip_ghostG0.(@tulip_stagedG Σ)) rpcrashNS
                  (own_replica_durable γ gid rid) dst ∗
                is_txn_log_lb γ gid clog ∗
                ⌜ilog_lsn_sorted ilog⌝ ∗
                ⌜eq_lsn_last_ilog (length clog) ilog⌝))%I
      with "[Hdurable]" as "> (Hdurable & #Hloglb & %Hsorted & %Heqlast)".
    { iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
      { solve_ndisj. }
      iNamedSuffix "Hdurable" "X".
      iDestruct "Hinv" as (proph) "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
      { apply Hgid. }
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]".
      { apply Hrid. }
      do 2 iNamed "Hrp".
      iDestruct (replica_clog_agree with "HclogX Hclog") as %->.
      iDestruct (replica_ilog_agree with "HilogX Hilog") as %->.
      iDestruct ("HrgC" with "[$Hvtss $Hclog $Hilog $Hkvdm $Hbm $Hbackup]") as "Hrg".
      { by iFrame "# %". }
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iMod ("HdurableC" $! dst with "[$HclogX $HilogX]") as "Hdurable".
      by iFrame "∗ # %".
    }

    (*@     for 0 < uint64(len(data)) {                                         @*)
    (*@                                                                         @*)
    set P := (λ cont : bool,
                ∃ (q : Slice.t) (remaining : list w8) (ilogrbs : list byte_string)
                  (iloga ilogr : list (nat * icommand)) (lsnx : u64),
                  "HdataPP"  ∷ dataPP ↦[slice.T byteT] q ∗
                  "Hdata"    ∷ own_slice_small q byteT (DfracOwn 1) remaining ∗
                  "HlsnxP"   ∷ lsnxP ↦[uint64T] #lsnx ∗
                  "Hrp"      ∷ own_replica_replaying_in_lsn rp (uint.nat lsnx) iloga gid γ α ∗
                  "%Hlsnx"   ∷ ⌜eq_lsn_last_ilog (uint.nat lsnx) iloga⌝ ∗
                  "%Hlelsnx" ∷ ⌜Forall (λ nc : nat * icommand, (nc.1 <= uint.nat lsnx)%nat) iloga⌝ ∗
                  "%Hilogar" ∷ ⌜ilog = iloga ++ ilogr⌝ ∗
                  "%Hserial" ∷ ⌜serialize id ilogrbs = remaining⌝ ∗
                  "%Hilogr"  ∷ ⌜encode_ilog_frag ilogr ilogrbs⌝ ∗
                  "%Hcont"   ∷ ⌜if cont then True else length remaining = O⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [$Hdata $HdataPP $HlsnxP $Hrp]");
      last first; first 1 last.
    { iDestruct (txn_log_lb_weaken [] with "Hloglb") as "Hloglbnil".
      { apply prefix_nil. }
      iFrame "Hloglbnil".
      iPureIntro. simpl.
      destruct Hencilog as (ilogbytes & Hencfrag & Hserial).
      by exists ilogbytes, ilog.
    }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      wp_apply wp_slice_len.
      wp_pures.
      iDestruct (own_slice_small_sz with "Hdata") as %Hlenr.
      case_bool_decide as Hbound; wp_pures; last first.
      { iApply "HΦ".
        iFrame "∗ # %".
        iPureIntro.
        clear -Hbound Hlenr. word.
      }
      assert (Hrem : length remaining ≠ O).
      { clear -Hbound Hlenr. word. }
      destruct ilogr as [| cmd ilogr'] eqn:Hilogreq.
      { apply length_not_nil_inv in Hrem.
        rewrite /encode_ilog_frag in Hilogr.
        apply Forall2_nil_inv_l in Hilogr. subst ilogrbs.
        by rewrite serialize_nil in Hserial.
      }
      apply Forall2_cons_inv_l in Hilogr as (cmdbs & ilogrbs' & Hcmd & Hilogr & ->).
      destruct Hcmd as (cmddata & Hdata & Henc).
      rewrite serialize_cons /= Hdata -app_assoc in Hserial.
      rewrite -Hserial.
      wp_load.

      (*@         lsny, bs1 := marshal.ReadInt(data)                              @*)
      (*@                                                                         @*)
      wp_apply (wp_ReadInt with "Hdata").
      iIntros (q') "Hdata".

      (*@         rp.replayBetween(lsnx, lsny)                                    @*)
      (*@                                                                         @*)
      assert (Hinilog : cmd ∈ ilog).
      { clear -Hilogar. set_solver. }
      rewrite Forall_forall in Hvilog.
      specialize (Hvilog _ Hinilog).
      destruct Hvilog as [Hvlsn Hvicmd].
      wp_load.
      assert (Hlsnxle : (uint.nat lsnx <= uint.nat (W64 cmd.1))%nat).
      { rewrite /eq_lsn_last_ilog in Hlsnx.
        destruct (last iloga) as [[n icmd] |] eqn:Hn; last first.
        { rewrite Hlsnx. lia. }
        rewrite last_lookup in Hn.
        unshelve epose proof (prefix_lookup_Some _ ilog _ _ Hn _) as Hprev.
        { rewrite Hilogar. by apply prefix_app_r. }
        assert (Hcur : ilog !! length iloga = Some cmd).
        { by rewrite Hilogar list_lookup_middle. }
        rewrite /ilog_lsn_sorted in Hsorted.
        unshelve epose proof (Hsorted _ _ _ _ _ Hprev Hcur) as Hle.
        { lia. }
        simpl in Hle.
        rewrite -Hlsnx.
        clear -Hle Hvlsn.
        word.
      }
      wp_apply (wp_Replica__replayBetween with "Hinv Hidx Htxnlog [$Hrp]").
      { apply Hgid. }
      { apply Hlelsnx. }
      { apply Hlsnxle. }
      iIntros "Hrp".

      (*@         lsnx = lsny                                                     @*)
      (*@                                                                         @*)
      wp_store.

      (*@         kind, bs2 := marshal.ReadInt(bs1)                               @*)
      (*@         ts, bs3 := marshal.ReadInt(bs2)                                 @*)
      (*@                                                                         @*)

      destruct cmd.2 eqn:Heqcmd.
      { (* Case: Read. *)

        (*@         if kind == CMD_READ {                                           @*)
        (*@             key, bs4 := util.DecodeString(bs3)                          @*)
        (*@             data = bs4                                                  @*)
        (*@             // Apply read.                                              @*)
        (*@             rp.bumpKey(ts, key)                                         @*)
        (*@                                                                         @*)
        rewrite Henc -2!app_assoc.
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs2P) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs3P) "Hdata".
        wp_apply (wp_DecodeString with "Hdata").
        iIntros (bs4P) "Hdata".
        wp_store.
        wp_pures.
        do 2 iNamed "Hrp". rename clog0 into cloga.
        wp_apply (wp_Replica__bumpKey with "Hptsmsptsm").
        { rewrite /= /valid_ts in Hvicmd. clear -Hvicmd. word. }
        { rewrite /= /valid_key in Hvicmd. by destruct Hvicmd as [_ ?]. }
        iIntros (spts) "[Hptsmsptsm %Hspts]".
        wp_pures.
        iApply "HΦ".
        subst P. simpl.
        iFrame "HdataPP Hdata HlsnxP".
        iExists ilogrbs', (iloga ++ [cmd]), ilogr'.
        iSplitL.
        { iClear "Hloglb".
          iFrame "∗ # %".
          iPureIntro.
          destruct cmd as [lsn icmd].
          rewrite merge_clog_ilog_snoc_ilog; last first.
          { clear -Hlenclog. simpl in Hlenclog. word. }
          simpl in Heqcmd.
          rewrite execute_cmds_snoc Heqcmd Hexec /=.
          rewrite (lookup_alter_Some _ _ _ _ Hspts).
          do 4 f_equal.
          (* Prove tid fits in u64 *)
          rewrite /= /valid_ts in Hvicmd.
          clear -Hvicmd. word.
        }
        iPureIntro.
        split.
        { rewrite /eq_lsn_last_ilog last_snoc /=.
          destruct cmd as [lsn icmd].
          simpl. simpl in Hvlsn.
          clear -Hvlsn. word.
        }
        split.
        { apply Forall_app.
          split.
          { apply (Forall_impl _ _ _ Hlelsnx). clear -Hlsnxle. intros. lia. }
          rewrite Forall_singleton. clear -Hvlsn. word.
        }
        by rewrite -app_assoc /= Hilogar.
      }
      { (* Case: Acquire. *)

        (*@         } else if kind == CMD_ACQUIRE {                                 @*)
        (*@             pwrs, bs4 := util.DecodeKVMapIntoSlice(bs3)                 @*)
        (*@             data = bs4                                                  @*)
        (*@             // Apply validate.                                          @*)
        (*@             rp.acquire(ts, pwrs)                                        @*)
        (*@             rp.memorize(ts, pwrs, ptgs)                                 @*)
        (*@                                                                         @*)
        destruct Henc as (mdata & gdata & Hcmddata & Hmdata & Hgdata).
        rewrite Hcmddata -!app_assoc.
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs2P) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs3P) "Hdata".
        wp_apply (wp_DecodeKVMapIntoSlice with "Hdata").
        { apply Hmdata. }
        iIntros (pwrsS bs4P) "[Hpwrs Hdata]".
        wp_pures.
        wp_apply (wp_DecodeInts__encode_txnptgs with "Hdata").
        { apply Hgdata. }
        iIntros (ptgsP bs5P) "[#Hptgs Hdata]".
        wp_store.
        assert (Hvpwrs : valid_wrs pwrs).
        { rewrite /= in Hvicmd. by destruct Hvicmd as [_ ?]. }
        do 2 iNamed "Hrp". rename clog0 into cloga.
        iMod (own_dbmap_in_slice_persist with "Hpwrs") as "#Hpwrs".
        wp_apply (wp_Replica__acquire with "Hpwrs Hptsmsptsm").
        { apply Hvpwrs. }
        iIntros "Hptsmsptsm".
        wp_apply (wp_Replica__memorize with "Hpwrs Hptgs [$Hcpm $Hpgm]").
        iIntros "[Hcpm Hpgm]".
        wp_pures.
        iApply "HΦ".
        subst P. simpl.
        iFrame "HdataPP Hdata HlsnxP".
        iExists ilogrbs', (iloga ++ [cmd]), ilogr'.
        iSplitL.
        { iClear "Hloglb".
          iFrame "∗ # %".
          iPureIntro. simpl.
          split.
          { apply map_Forall_insert_2; [apply Hvpwrs | apply Hvcpm]. }
          destruct cmd as [lsn icmd].
          rewrite merge_clog_ilog_snoc_ilog; last first.
          { clear -Hlenclog. simpl in Hlenclog. word. }
          simpl in Heqcmd.
          rewrite execute_cmds_snoc Heqcmd Hexec /=.
          rewrite uint_nat_W64_of_nat; first done.
          rewrite /= /valid_ts in Hvicmd.
          clear -Hvicmd. lia.
        }
        iPureIntro.
        split.
        { rewrite /eq_lsn_last_ilog last_snoc /=.
          destruct cmd as [lsn icmd].
          simpl. simpl in Hvlsn.
          clear -Hvlsn. word.
        }
        split.
        { apply Forall_app.
          split.
          { apply (Forall_impl _ _ _ Hlelsnx). clear -Hlsnxle. intros. lia. }
          rewrite Forall_singleton. clear -Hvlsn. word.
        }
        by rewrite -app_assoc /= Hilogar.
      }
      { (* Case: Advance. *)

        (*@         } else if kind == CMD_ADVANCE {                                 @*)
        (*@             rank, bs4 := marshal.ReadInt(bs3)                           @*)
        (*@             data = bs4                                                  @*)
        (*@             rp.advance(ts, rank)                                        @*)
        (*@                                                                         @*)
        rewrite Henc -2!app_assoc.
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs2P) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs3P) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs4P) "Hdata".
        wp_store.
        do 2 iNamed "Hrp". rename clog0 into cloga.
        wp_apply (wp_Replica__advance with "Hpsmrkm").
        { simpl in Hvicmd. clear -Hvicmd. word. }
        iIntros "Hpsmrkm".
        wp_pures.
        iApply "HΦ".
        subst P. simpl.
        iFrame "HdataPP Hdata HlsnxP".
        iExists ilogrbs', (iloga ++ [cmd]), ilogr'.
        iSplitL.
        { iClear "Hloglb".
          iFrame "∗ # %".
          iPureIntro.
          destruct cmd as [lsn icmd].
          rewrite merge_clog_ilog_snoc_ilog; last first.
          { clear -Hlenclog. simpl in Hlenclog. word. }
          simpl in Heqcmd.
          rewrite execute_cmds_snoc Heqcmd Hexec /=.
          rewrite /= /valid_ts in Hvicmd.
          destruct Hvicmd as [Hvtid Hvrank].
          rewrite uint_nat_W64_of_nat; last word.
          rewrite uint_nat_W64_of_nat; last word.
          done.
        }
        iPureIntro.
        split.
        { rewrite /eq_lsn_last_ilog last_snoc /=.
          destruct cmd as [lsn icmd].
          simpl. simpl in Hvlsn.
          clear -Hvlsn. word.
        }
        split.
        { apply Forall_app.
          split.
          { apply (Forall_impl _ _ _ Hlelsnx). clear -Hlsnxle. intros. lia. }
          rewrite Forall_singleton. clear -Hvlsn. word.
        }
        by rewrite -app_assoc /= Hilogar.
      }
      { (* Case: Accept. *)

        (*@         } else if kind == CMD_ACCEPT {                                  @*)
        (*@             rank, bs4 := marshal.ReadInt(bs3)                           @*)
        (*@             dec, bs5 := marshal.ReadBool(bs4)                           @*)
        (*@             data = bs5                                                  @*)
        (*@             // Apply accept.                                            @*)
        (*@             rp.accept(ts, rank, dec)                                    @*)
        (*@         }                                                               @*)
        (*@                                                                         @*)
        rewrite Henc -2!app_assoc.
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs2P) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs3P) "Hdata".
        wp_apply (wp_ReadInt with "[Hdata]").
        { by list_simplifier. }
        iIntros (bs4P) "Hdata".
        wp_apply (wp_ReadBool with "Hdata").
        iIntros (dec bs5P) "[%Hdec Hdata]".
        wp_store.
        do 2 iNamed "Hrp". rename clog0 into cloga.
        wp_apply (wp_Replica__accept with "Hpsmrkm").
        iIntros "Hpsmrkm".
        wp_pures.
        iApply "HΦ".
        subst P. simpl.
        iFrame "HdataPP Hdata HlsnxP".
        iExists ilogrbs', (iloga ++ [cmd]), ilogr'.
        iSplitL.
        { iClear "Hloglb".
          iFrame "∗ # %".
          iPureIntro.
          destruct cmd as [lsn icmd].
          rewrite merge_clog_ilog_snoc_ilog; last first.
          { clear -Hlenclog. simpl in Hlenclog. word. }
          simpl in Heqcmd.
          rewrite execute_cmds_snoc Heqcmd Hexec /=.
          rewrite /= /valid_ts in Hvicmd.
          destruct Hvicmd as [Hvtid Hvrank].
          rewrite uint_nat_W64_of_nat; last word.
          rewrite uint_nat_W64_of_nat; last word.
          assert (pdec = dec) as ->.
          { by destruct dec, pdec. }
          done.
        }
        iPureIntro.
        split.
        { rewrite /eq_lsn_last_ilog last_snoc /=.
          destruct cmd as [lsn icmd].
          simpl. simpl in Hvlsn.
          clear -Hvlsn. word.
        }
        split.
        { apply Forall_app.
          split.
          { apply (Forall_impl _ _ _ Hlelsnx). clear -Hlsnxle. intros. lia. }
          rewrite Forall_singleton. clear -Hvlsn. word.
        }
        by rewrite -app_assoc /= Hilogar.
      }

      (*@     }                                                                   @*)
      (*@                                                                         @*)
    }

    (*@     rp.lsna = lsnx                                                      @*)
    (*@ }                                                                       @*)
    iNamed 1. iNamed "Hrp". rename clog0 into cloga.
    iNamed "Hlsna".
    wp_load.
    wp_storeField.
    iApply "HΦ".
    assert (iloga = ilog) as ->.
    { destruct ilogr as [| c ilogr'].
      { by rewrite app_nil_r in Hilogar. }
      exfalso.
      apply Forall2_cons_inv_l in Hilogr as (bs & ilogrbs' & Henc & _ & Heq).
      rewrite Heq serialize_cons in Hserial.
      apply nil_length_inv in Hcont.
      rewrite Hcont /= in Hserial.
      destruct bs eqn:Hbs; last done.
      by apply encode_lsn_icommand_not_nil in Henc.
    }
    iDestruct (txn_log_lb_prefix with "Hcloglb Hloglb") as %Horprefix.
    assert (cloga = clog) as ->.
    { rewrite /eq_lsn_last_ilog in Hlsnx, Heqlast.
      destruct (last ilog) as [[n icmd] |].
      { rewrite -Hlsnx in Hlenclog.
        destruct Horprefix.
        { apply prefix_length_eq; [done | lia]. }
        { symmetry. apply prefix_length_eq; [done | lia]. }
      }
      { rewrite Hlsnx in Hlenclog.
        destruct Horprefix.
        { apply prefix_length_eq; [done | lia]. }
        { symmetry. apply prefix_length_eq; [done | lia]. }
      }
    }
    by iFrame.
  Qed.

End program.
