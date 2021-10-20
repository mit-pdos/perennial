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
                      ⌜int.Z cn_some < int.Z cn⌝ ∨ accepted_ptsto γ cn_some me []
                      ) ∗
  "#Hproposal_lb" ∷ proposal_lb γ cn opLog ∗
  "#HoldConfMax" ∷ φ γ cn opLog ∗
  "HprimaryOwnsProposal" ∷ (if isPrimary then (proposal_ptsto γ cn opLog) else True) ∗
  "#Hcommit_lb" ∷ commit_lb γ (take (int.nat commitIdx) opLog)
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
       is_ReplicaServer s rid γ ∗
       own_AppendArgs args_ptr args ∗
       proposal_lb γ args.(AA_cn) args.(AA_log) ∗
       φ γ args.(AA_cn) args.(AA_log) ∗
       commit_lb γ (take (int.nat args.(AA_commitIdx)) args.(AA_log)) ∗
       ⌜int.Z args.(AA_commitIdx) < length args.(AA_log)⌝
  }}}
    ReplicaServer__AppendRPC #s #args_ptr
  {{{
       (r:bool), RET #r; True
  }}}
.
Proof.
  iIntros (Φ) "(#HisRepl & Hargs & #Hpre) HΦ".
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
    }
    wp_pures.
    iApply "HΦ".
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

  (* Idea: weaken context to the thing that'll be true after the if statement *)
  (*
  iAssert (∃ cn' opLog_sl' opLog',
  "HopLog" ∷ s ↦[ReplicaServer :: "opLog"] (slice_val opLog_sl') ∗
  "HopLog_slice" ∷ is_slice opLog_sl' byteT 1 opLog' ∗
  "Haccepted" ∷ accepted_ptsto γ cn' rid opLog' ∗
  "HacceptedUnused" ∷ ([∗ set] cn_some ∈ fin_to_set u64, ⌜int.Z cn_some < int.Z cn'⌝
                                                        ∨ accepted_ptsto γ cn_some rid []) ∗
  "#Hproposal_lb" ∷ proposal_lb γ cn' opLog' ∗
  "#HoldConfMax" ∷ φ γ cn' opLog'
  )%I with "[HopLog HopLog_slice Haccepted HacceptedUnused Hproposal_lb HoldConfMax]" as "HH".
  {
  admit.
  }
  wp_apply (wp_If_optional with ) *)

  (* TODO: Should do if-join here *)
  Search Slice.sz.
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
                       "HacceptedUnused" ∷ ([∗ set] cn_some ∈ fin_to_set u64, ⌜int.Z cn_some < int.Z args.(AA_cn)⌝
                                                                              ∨ accepted_ptsto γ cn_some rid []) ∗
                       "#Hproposal_lb" ∷ proposal_lb γ args.(AA_cn) opLog' ∗
                       "#HoldConfMax" ∷ φ γ args.(AA_cn) opLog' ∗
                       "Hcn" ∷ s ↦[ReplicaServer :: "cn"] #args.(AA_cn) ∗
                       "#Hcommit_lb" ∷ commit_lb γ (take (int.nat commitIdx) opLog') ∗
                       "%HnewLog" ∷ ⌜args.(AA_log) ⪯ opLog'⌝
            )%I with "[HopLog HopLog_slice Haccepted HacceptedUnused Hproposal_lb HoldConfMax Hcn]" as "HH".
    {
      replace (cn) with (args.(AA_cn)); last by word.
      iExists _, _; iFrame "∗#".
      assert (int.Z opLog_sl.(Slice.sz) >= int.Z log_sl.(Slice.sz))%Z.
      { word. }
      iDestruct "Hpre" as "[Hproposal _]".
      (* TODO: want to combine Hproposal and Hproposal_lb to conclude that they
         are comparable, and combine with length inequality *)
      admit.
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
      wp_storeField.
      iSplitL ""; first done.
      iExists _, _.
      iFrame "HopLog ∗".
      (* TODO: Ghost stuff. *)
      (* destruct into cases; in case we increase cn, use oldConfMax to maintain commit_lb *)
      admit.
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
      iAssert (∃ (commitIdx':u64), "Hcommit" ∷ s ↦[ReplicaServer :: "commitIdx"] #commitIdx'
                                     ∗ "#Hcommit_lb" ∷ commit_lb γ (take (int.nat commitIdx') opLog')
              )%I with "[HcommitIdx]" as "HH".
      {
        iExists _.
        iFrame.
        (* prove that args.(AA_log) ≤ opLog' or that
           opLog' ≤ args.(AA_log);
         *)
        (* iDestruct "Hpre" as "(_&_&$&_)". *)
        iDestruct "Hpre" as "(Hproposal_lb2 & _ & Hcommit & %HcommitLen)".
        (* Use the fact that args.(AA_log) and opLog' are comparable. *)
        assert ( take (int.nat args.(AA_commitIdx)) opLog' ⪯
                (take (int.nat args.(AA_commitIdx)) args.(AA_log)))%I.
        {
          set (l1:=args.(AA_log)) in *.
          set (l2:=opLog') in *.
          set (e:=int.nat args.(AA_commitIdx)) in *.
          assert (e < length l1) by word.
          clear -H0 HnewLog.
          admit.
        }
        iApply (commit_lb_monotonic with "Hcommit").
        done.
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
    }
  }
  iIntros "HH".
  iNamed "HH".
  iClear "Hcommit_lb".
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
  }
  wp_pures.
  iApply "HΦ".
  by iModIntro.
Admitted.

End replica_proof.
