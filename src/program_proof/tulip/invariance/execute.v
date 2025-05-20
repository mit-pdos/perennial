From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import
  execute_commit execute_abort.

Section execute.
  Context `{!tulip_ghostG Σ}.

  (** Note on PCR crash-recovery proof. To support crash-recovery, we'll have to
  add an invariant saying that ``the length of the consistent log is equal to
  the LSN of the last inconsistent log entry (which is the largest among all
  inconsistent log)''. The lock invariant maintains an in-memory copy of the
  replica state, which runs ahead of the replica state in the atomic invariant,
  which, to provide some intuition, is the state produced from executing [clog]
  and [ilog], and is also the state to which the recovery procedure restore. *)

  (** We use the lemmas [replica_inv_local_read], [replica_inv_validate],
  [replica_inv_execute] as follows: At the point where we want to write an
  inconsistent log entry, we first apply [replica_inv_execute] to sync the
  consistent log. To do this, we would need to relax the abovementioned
  invariant to say that "the former is greater than or equal to the
  latter". Then we apply [replica_inv_local_read] or [replica_inv_validate] and
  re-establish the invariant. *)

  Lemma replica_inv_execute_strong γ gid rid ilog ccmds :
    ∀ clog,
    is_txn_log_lb γ gid (clog ++ ccmds) -∗
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    group_inv γ gid -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid (clog ++ ccmds) ∗
    own_replica_ilog_half γ gid rid ilog ∗
    group_inv γ gid ∗
    replica_inv_weak γ gid rid.
  Proof.
    iInduction ccmds as [| c l] "IH"; iIntros (clog) "#Hloglb Hclog Hilog Hgroup Hrp".
    { rewrite app_nil_r. by iFrame. }
    rewrite cons_middle app_assoc.
    destruct c as [ts pwrs | ts].
    { (* Case: [CmdCommit ts pwrs] *)
      iMod (replica_inv_execute_commit with "[] Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      { iApply (txn_log_lb_weaken (clog ++ [CmdCommit ts pwrs]) with "Hloglb").
        by apply prefix_app_r.
      }
      iApply ("IH" with "Hloglb Hclog Hilog Hgroup Hrp").
    }
    { (* Case: [CmdAbort ts] *)
      iMod (replica_inv_execute_abort with "[] Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      { iApply (txn_log_lb_weaken (clog ++ [CmdAbort ts]) with "Hloglb").
        by apply prefix_app_r.
      }
      iApply ("IH" with "Hloglb Hclog Hilog Hgroup Hrp").
    }
  Qed.

  Lemma replica_inv_execute γ gid rid ilog ccmds :
    ∀ clog,
    is_txn_log_lb γ gid (clog ++ ccmds) -∗
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    group_inv γ gid -∗
    replica_inv γ gid rid ==∗
    own_replica_clog_half γ gid rid (clog ++ ccmds) ∗
    own_replica_ilog_half γ gid rid ilog ∗
    group_inv γ gid ∗
    replica_inv_weak γ gid rid.
  Proof.
    iIntros (clog) "#Hlb Hclog Hilog Hgroup Hrp".
    iAssert (replica_inv_weak γ gid rid)%I with "[Hrp]" as "Hrp".
    { do 2 iNamed "Hrp".
      apply eq_lsn_last_ilog_weaken in Heqlast.
      by iFrame "∗ # %".
    }
    iApply (replica_inv_execute_strong with "Hlb Hclog Hilog Hgroup Hrp").
  Qed.

End execute.
