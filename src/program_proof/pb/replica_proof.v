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
  "#Hcommit_lb" ∷ commit_lb γ (subslice 0 (int.nat commitIdx) opLog)
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

Search "Subslice".
Lemma wp_ReplicaServer__AppendRPC (s:loc) rid γ (args_ptr:loc) args :
  {{{
       is_ReplicaServer s rid γ ∗
       own_AppendArgs args_ptr args ∗
       proposal_lb γ args.(AA_cn) args.(AA_log) ∗
       φ γ args.(AA_cn) args.(AA_log) ∗
       commit_lb γ (subslice 0 (int.nat args.(AA_commitIdx)) args.(AA_log))
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

  (* TODO: Should do if-join here *)
  wp_loadField.
  wp_loadField.

  wp_pures.
  wp_bind (if: _ then #true else _)%E.
  wp_if_destruct.
  { (* case: args.cn > s.cn *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_storeField with "HopLog").
    { apply slice_val_ty. }
    iIntros "HopLog".
    wp_pures.
    wp_loadField.
    wp_storeField.

    (* TODO: upgrade accepted_ptsto and HacceptedUnused to the new CN *)

    (* FIXME: This reasoning should only happen once, not be repeated in the different branches *)
    wp_loadField.
    wp_loadField.
    wp_pures.
    wp_apply (wp_If_join_evar with "[HcommitIdx HAcommitIdx]").
    {
      iIntros.
      wp_if_destruct.
      { (* args.commitIdx > commitIdx *)
        wp_loadField.
        wp_storeField.
        iSplitL ""; first done.
        iAssert (∃ (commitIdx':u64), s ↦[ReplicaServer :: "commitIdx"] #commitIdx'
                 ∗ commit_lb γ (subslice 0 (int.nat commitIdx') args.(AA_log))
                )%I with "[HcommitIdx]" as "HH".
        {
          iExists _.
          iFrame.
          iDestruct "Hpre" as "(_&_&$)".
        }
        iNamedAccu.
      }
      {
        iModIntro. iSplitL ""; first done.
        iFrame.
        iExists commitIdx.
        iFrame.
        (* FIXME: The context is messed up. We want to have the bigger opLog already picked *)
        admit.
      }
    }
    admit.
  }
  { (* case: args.cn == s.cn *)
    admit.
  }
Admitted.

End replica_proof.
