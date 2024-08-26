From Perennial.program_proof.rsm.distx Require Import prelude.
From Perennial.program_proof.rsm.distx.invariance Require Import
  learn_read learn_prepare learn_commit learn_abort.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma group_inv_learn γ p gid cpool cmds :
    ∀ log,
    cpool_subsume_log cpool (log ++ cmds) ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ cmds) cpool.
  Proof.
    iInduction cmds as [| c l] "IH".
    { iIntros (log Hsubsume) "Htxn Hkeys Hgroup". rewrite app_nil_r. by iFrame. }
    (* rewrite Forall_cons in Hcpool. *)
    (* destruct Hcpool as [Hc Hcpool]. *)
    iIntros (log Hsubsume) "Htxn Hkeys Hgroup".
    rewrite cons_middle app_assoc in Hsubsume.
    rewrite cons_middle app_assoc.
    destruct c.
    { (* Case: [CmdRead tid key] *)
      iMod (group_inv_learn_read with "Hkeys Hgroup") as "[Hkeys Hgroup]".
      { rewrite /cpool_subsume_log 2!Forall_app Forall_singleton in Hsubsume.
        by destruct Hsubsume as [[_ Hc] _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
    { (* Case: [CmdPrep tid wrs] *)
      iMod (group_inv_learn_prepare with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log 2!Forall_app Forall_singleton in Hsubsume.
        by destruct Hsubsume as [[_ Hc] _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
    { (* Case: [CmdCmt tid] *)
      iMod (group_inv_learn_commit with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log Forall_app in Hsubsume.
        by destruct Hsubsume as [Hsubsume _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
    { (* Case: [CmdAbt tid] *)
      iMod (group_inv_learn_abort with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
      { rewrite /cpool_subsume_log Forall_app in Hsubsume.
        by destruct Hsubsume as [Hsubsume _].
      }
      by iApply ("IH" with "[] Htxn Hkeys Hgroup").
    }
  Qed.

End inv.
