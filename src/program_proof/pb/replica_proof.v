From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

From Perennial.program_proof.pb Require Export ghost_proof.

Section replica_proof.
Record ConfigurationC :=
{
  replicas: list u64
}.

Context `{!heapGS Σ}.
Implicit Type γ:pb_names.

Definition own_ReplicaServer (s:loc) (me:u64) γ
  : iProp Σ :=
  ∃ (cn commitIdx:u64) (matchIdx_sl opLog_sl replicaClerks_sl : Slice.t) (isPrimary:bool)
    (matchIdx:list u64) (opLog:list u8) (replicaClerks:list loc) ,
  "Hcn" ∷ s ↦[ReplicaServer :: "cn"] #cn ∗
  (* don't need use the conf field right now *)
  "HisPrimary" ∷ s ↦[ReplicaServer :: "isPrimary"] #isPrimary ∗
  "HreplicaClerks" ∷ s ↦[ReplicaServer :: "replicaClerks"] (slice_val replicaClerks_sl) ∗
  "HreplicaClerks_slice" ∷ is_slice replicaClerks_sl (struct.ptrT ReplicaClerk) 1%Qp replicaClerks ∗
  "HopLog" ∷ s ↦[ReplicaServer :: "opLog"] (slice_val opLog_sl) ∗
  "HopLog_slice" ∷ is_slice opLog_sl byteT 1%Qp opLog ∗
  "HcommitIdx" ∷ s ↦[ReplicaServer :: "commitIdx"] #commitIdx ∗
  "HmatchIdx" ∷ s ↦[ReplicaServer :: "matchIdx"] (slice_val matchIdx_sl) ∗
  "HmatchIdx_slice" ∷ is_slice matchIdx_sl uint64T 1%Qp matchIdx∗

  (* ghost stuff *)
  "Haccepted" ∷ accepted_ptsto γ cn me opLog ∗
  "HacceptedUnused" ∷ ([∗ set] cn_some ∈ (fin_to_set u64),
                      ⌜int.Z cn_some ≤ int.Z cn⌝ ∨ accepted_ptsto γ cn_some me []
                      ) ∗
  "#Hproposal_lb" ∷ proposal_lb γ cn opLog ∗
  "#HoldConfMax" ∷ oldConfMax γ cn opLog ∗
  "HprimaryOwnsProposal" ∷ (if isPrimary then (proposal_ptsto γ cn opLog) else True) ∗
  "#Hcommit_lb" ∷ commit_lb_by γ cn (take (int.nat commitIdx) opLog) ∗
  "%HcommitLeLogLen" ∷ ⌜int.Z commitIdx <= length opLog⌝
.

Definition ReplicaServerN := nroot .@ "ReplicaServer".

Definition is_ReplicaServer (s:loc) (rid:u64) γ: iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[ReplicaServer :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock ReplicaServerN mu (own_ReplicaServer s rid γ)
.

(* TODO: move to a different file *)
Record AppendArgsC :=
{
  AA_cn:u64;
  AA_commitIdx: u64;
  AA_log: list u8;
}.

Definition own_AppendArgs (args_ptr:loc) (args:AppendArgsC) : iProp Σ :=
  ∃ (log_sl:Slice.t),
  "HAcn" ∷ args_ptr ↦[AppendArgs :: "cn"] #args.(AA_cn) ∗
  "HAcommitIdx" ∷ args_ptr ↦[AppendArgs :: "commitIdx"] #args.(AA_commitIdx) ∗
  "HAlog" ∷ args_ptr ↦[AppendArgs :: "log"] (slice_val log_sl) ∗
  "HAlog_slice" ∷ is_slice log_sl byteT 1%Qp args.(AA_log)
.

Lemma wp_ReplicaServer__AppendRPC (s:loc) rid γ (args_ptr:loc) args :
  {{{
       "#HisRepl" ∷ is_ReplicaServer s rid γ ∗
       "Hargs" ∷ own_AppendArgs args_ptr args ∗
       "#Hproposal_lb_in" ∷ proposal_lb γ args.(AA_cn) args.(AA_log) ∗
       "#HoldConfMax_in" ∷ oldConfMax γ args.(AA_cn) args.(AA_log) ∗
       "#Hcommit_lb_in" ∷ commit_lb_by γ args.(AA_cn) (take (int.nat args.(AA_commitIdx)) args.(AA_log)) ∗
       "%HcommitLength" ∷ ⌜int.Z args.(AA_commitIdx) < length args.(AA_log)⌝
  }}}
    ReplicaServer__AppendRPC #s #args_ptr
  {{{
       (r:bool), RET #r; ⌜r = true⌝ ∗ accepted_lb γ args.(AA_cn) rid args.(AA_log) ∨ ⌜r = false⌝
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisRepl".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_pures.
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.

  wp_if_destruct.
  { (* args.cn < s.cn *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
    iFrame "HmuInv Hlocked". iNext.
    iExists _, _, _, _, _, _, _, _.
    iExists _. (* can only iExists 8 things at a time *)
    iFrame "∗#".
    done.
    }
    wp_pures.
    iApply "HΦ".
    iRight.
    done.
  }
  (* args.cn ≥ s.cn *)

  wp_loadField.
  wp_loadField.
  wp_apply (wp_or with "[HopLog HAlog]").
  { iNamedAccu. }
  { by wp_pures. }
  {
    iIntros "% HH"; iNamed "HH".
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_pures.
    by iFrame.
  }
  iNamed 1.

  iDestruct (is_slice_sz with "HopLog_slice") as %HopLogLen.
  iDestruct (is_slice_sz with "HAlog_slice") as %HALogLen.
  wp_apply (wp_If_join_evar with "[Haccepted HacceptedUnused HopLog HopLog_slice Hcn HAlog HAlog_slice HAcn]").
  {
    iIntros.
    wp_if_destruct; last first.
    { (* won't grow log *)
    iModIntro; iSplitL ""; first done.
    iAssert (∃ opLog_sl' opLog',
              "HopLog" ∷ s ↦[ReplicaServer :: "opLog"] (slice_val opLog_sl') ∗
                       "HopLog_slice" ∷ is_slice opLog_sl' byteT 1 opLog' ∗
                       "Haccepted" ∷ accepted_ptsto γ args.(AA_cn) rid opLog' ∗
                       "HacceptedUnused" ∷ ([∗ set] cn_some ∈ fin_to_set u64, ⌜int.Z cn_some ≤ int.Z args.(AA_cn)⌝
                                                                              ∨ accepted_ptsto γ cn_some rid []) ∗
                       "#Hproposal_lb" ∷ proposal_lb γ args.(AA_cn) opLog' ∗
                       "#HoldConfMax" ∷ oldConfMax γ args.(AA_cn) opLog' ∗
                       "Hcn" ∷ s ↦[ReplicaServer :: "cn"] #args.(AA_cn) ∗
                       "#Hcommit_lb_oldIdx" ∷ commit_lb_by γ args.(AA_cn) (take (int.nat commitIdx) opLog') ∗
                       "%HnewLog" ∷ ⌜args.(AA_log) ⪯ opLog'⌝ ∗
                       "#Hacc_lb" ∷ accepted_lb γ args.(AA_cn) rid args.(AA_log) ∗
                       "%HcommitIdxLeNewLogLen" ∷ ⌜int.Z commitIdx ≤ length opLog'⌝
            )%I with "[HopLog HopLog_slice Haccepted HacceptedUnused Hproposal_lb HoldConfMax Hcn]" as "HH".
    {
      replace (cn) with (args.(AA_cn)); last by word.
      iDestruct (accepted_witness with "Haccepted") as "#Hacc_lb".
      iExists _, _; iFrame "∗#".
      assert (int.nat opLog_sl.(Slice.sz) >= int.nat log_sl.(Slice.sz))%Z as HopLogBigger.
      { word. }

      iDestruct (proposal_lb_comparable with "Hproposal_lb_in Hproposal_lb") as %Hcomparable.
      destruct Hcomparable as [|].
      { (* case 1: args.log ⪯ opLog *)
        iSplitL ""; first done.
        iSplitR ""; last done.
        by iApply accepted_lb_monotonic.
      }
      { (* case 2: opLog ⪯ args.log; this will imply that the two are actually equal *)
        rewrite -HopLogLen in HopLogBigger.
        rewrite -HALogLen in HopLogBigger.
        assert (opLog = args.(AA_log)) as ->.
        { (* FIXME: pure list prefix fact *)
          admit.
        }
        iFrame "#".
        done.
      }
    }
    iClear "HAlog HAcn HAlog_slice".
    iNamedAccu.
    }
    { (* will grow the log *)
      wp_loadField.
      wp_apply (wp_storeField with "HopLog").
      { apply slice_val_ty. }
      iIntros "HopLog".
      wp_pures.
      wp_loadField.
      wp_apply wp_fupd.
      wp_storeField.
      iSplitL ""; first done.
      iExists _, _.
      iFrame "HopLog ∗#".
      (* TODO: Ghost stuff. *)
      (* destruct into cases; in case we increase cn, use oldConfMax to maintain commit_lb *)
      assert (int.Z cn > int.Z args.(AA_cn) ∨ int.Z cn = int.Z args.(AA_cn) ∨ int.Z cn < int.Z args.(AA_cn)) as Htrichotomy.
      { word. }
      destruct Htrichotomy as [Hbad|[Heq|HlargerLog]].
      { exfalso. word. }
      { (* in this case, must have len(args.log) ≥ len(s.cn) *)
        assert (int.nat opLog_sl.(Slice.sz) < int.nat log_sl.(Slice.sz)) as HlargerLog2.
        { word. }
        rewrite -HopLogLen -HALogLen in HlargerLog2.
        assert (cn = args.(AA_cn)) as -> by word.
        iFrame "∗#".
        iDestruct (proposal_lb_comparable with "Hproposal_lb_in Hproposal_lb") as %Hcomparable.
        destruct Heqb0 as [Hbad|HargLogLenLarger].
        { exfalso. word. }
        assert (opLog ⪯ args.(AA_log)) as HargLogLarger.
        { (* TODO: comparable + longer length -> larger log *)
          admit. }
        iMod (accepted_update with "Haccepted") as "Haccepted".
        { done. }
        iDestruct (accepted_witness with "Haccepted") as "#Hacc_lb".
        iFrame "Hacc_lb".
        iSplitL "Haccepted"; first done.
        assert (take (int.nat commitIdx) args.(AA_log) ⪯ take (int.nat commitIdx) opLog).
        { (* TODO: Use the fact that commitIdx ≤ len(opLog) to make this work *)
          admit.
        }
        iSplitR "".
        {
          iApply (commit_lb_by_monotonic with "Hcommit_lb").
          { done. }
          { done. }
        }
        iSplitR ""; first done.
        iPureIntro.
        word.
      }
      { (* args.cn > s.cn: in this case, we want to increase our cn to args.cn *)
        iClear "Haccepted". (* throw away the old accepted↦ *)
        iDestruct (big_sepS_elem_of_acc_impl args.(AA_cn) with "HacceptedUnused") as "[Haccepted Hunused]".
        { set_solver. }
        iDestruct "Haccepted" as "[%Hbad|Haccepted]".
        { exfalso; word. }
        iMod (accepted_update _ _ _ _ args.(AA_log) with "Haccepted") as "Haccepted".
        { admit. }
        iDestruct (accepted_witness with "Haccepted") as "#Hacc_lb".
        iSplitL "Haccepted"; first done.
        iSplitL "Hunused".
        {
          iApply "Hunused".
          {
            iModIntro.
            iIntros (???) "[%Hcase|Hcase]".
            { iLeft. iPureIntro. word. }
            { iFrame. }
          }
          {
            iLeft. iPureIntro. word.
          }
        }
        iFrame "Hacc_lb".

        iDestruct (oldConfMax_commit_lb_by with "HoldConfMax_in Hcommit_lb") as %HlogLe.
        { done. }
        iSplitR ""; last first.
        {
          iSplitL ""; first done.
          iPureIntro.
          admit. (* TODO: Pure fact about lists *)
        }

        iApply (commit_lb_by_monotonic with "Hcommit_lb").
        { word. }
        clear -HlogLe.
        (* TODO: pure fact about lists and prefixes *)
        admit.
      }
    }
  }
  iIntros "HH".
  wp_loadField.
  wp_loadField.

  wp_pures.
  iClear "Hproposal_lb HoldConfMax".
  iRename "Hcommit_lb" into "Hcommit_lb_old".
  iNamed "HH".
  iNamed "HH".
  wp_apply (wp_If_join_evar with "[HcommitIdx HAcommitIdx]").
  {
    iIntros.
    wp_if_destruct.
    { (* args.commitIdx > commitIdx *)
      wp_loadField.
      wp_storeField.
      iSplitL ""; first done.
      iAssert (∃ (commitIdx':u64), "Hcommit" ∷ s ↦[ReplicaServer :: "commitIdx"] #commitIdx' ∗
                                   "#Hcommit_lb" ∷ commit_lb_by γ args.(AA_cn) (take (int.nat commitIdx') opLog') ∗
                                   "%HcommitLeLogLen" ∷ ⌜int.Z commitIdx' ≤ length opLog'⌝
              )%I with "[HcommitIdx]" as "HH".
      {
        iExists _.
        iFrame.
        (* prove that args.(AA_log) ≤ opLog' or that
           opLog' ≤ args.(AA_log);
         *)
        (* Use the fact that args.(AA_log) and opLog' are comparable. *)
        assert ( take (int.nat args.(AA_commitIdx)) opLog' ⪯
                (take (int.nat args.(AA_commitIdx)) args.(AA_log)))%I.
        {
          set (l1:=args.(AA_log)) in *.
          set (l2:=opLog') in *.
          set (e:=int.nat args.(AA_commitIdx)) in *.
          assert (e < length l1) by word.
          clear -H0 HnewLog.
          admit. (* TODO: pure list fact *)
        }
        iSplitR "".
        {
          iApply (commit_lb_by_monotonic with "Hcommit_lb_in").
          { word. }
          done.
        }
        {
          iPureIntro.
          assert (length args.(AA_log) ≤ length opLog').
          { admit. (* TODO: pure fact *) }
          word.
        }
      }
      iNamedAccu.
    }
    { (* args.commitIdx is not larger than commitIdx. boils down to the newly
         proposed value not contradicting the previously committed stuff, the
         proof is done earlier for conveneince. *)
        iModIntro. iSplitL ""; first done.
        iFrame.
        iExists commitIdx.
        iFrame.
        iFrame "#".
        {
          iPureIntro.
          assert (length args.(AA_log) ≤ length opLog').
          { admit. (* TODO: pure fact *) }
          word.
        }
    }
  }
  iIntros "HH".
  iNamed "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    do 9 iExists _.
    iFrame "∗#".
    done.
  }
  wp_pures.
  iApply "HΦ".
  iLeft.
  iFrame "#".
  by iModIntro.
Admitted.

End replica_proof.
