From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

From Perennial.program_proof.pb Require Export ghost_proof replica_proof.

Section become_primary_proof.

Context `{!heapGS Σ}.

(* TODO: move to a different file *)
Record BecomePrimaryArgsC :=
{
  BP_cn:u64;
  BP_conf: ConfigurationC;
}.

Definition own_Configuration (cptr:loc) (c:ConfigurationC) : iProp Σ :=
  ∃ replicas_sl,
  "Hreplicas" ∷ cptr ↦[Configuration :: "Replicas"] (slice_val replicas_sl) ∗
  "Hreplicas_sl" ∷ is_slice replicas_sl uint64T 1%Qp c.(C_replicas)
.

Definition own_BecomePrimaryArgs (args_ptr:loc) (args:BecomePrimaryArgsC) : iProp Σ :=
  ∃ (conf_ptr:loc),
  "HBcn" ∷ args_ptr ↦[BecomePrimaryArgs :: "Cn"] #args.(BP_cn) ∗
  "HBconf" ∷ args_ptr ↦[BecomePrimaryArgs :: "Conf"] #conf_ptr ∗
  "HBconf_own" ∷ own_Configuration conf_ptr args.(BP_conf)
.

Lemma wp_ReplicaServer__BecomePrimaryRPC(s:loc) rid γ (args_ptr:loc) args :
  {{{
       "#HisRepl" ∷ is_ReplicaServer s rid γ ∗
       "Hargs" ∷ own_BecomePrimaryArgs args_ptr args
  }}}
    ReplicaServer__BecomePrimaryRPC #s #args_ptr
  {{{
       RET #(); True
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
  wp_pures.

  iNamed "Hargs".
  iNamed "Hown".
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* Old BecomePrimary request *)
    (* FIXME: let go of lock here *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      do 9 iExists _.
      iFrame "∗# Hown".
      done.
    }
    wp_pures.
      by iApply "HΦ".
  }
  wp_loadField.
  wp_loadField.
  wp_apply (wp_and with "[Hcn]").
  {
    iNamedAccu.
  }
  {
    by wp_pures.
  }
  {
    iIntros.
    wp_loadField.
    iFrame.
    by wp_pures.
  }
  iNamed 1.
  wp_if_destruct.
  {
    admit.
  }
  (* become primary in new config *)

  (* Physical part of proof *)
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_pures.
  iNamed "HBconf_own".
  wp_loadField.
  wp_apply (wp_slice_len).
  (* FIXME: what's going on with this wp_apply? *)
  wp_apply (wp_NewSlice with "[] [-]").
  { done. }
  iNext.
  iClear "HmatchIdx_slice".
  rename matchIdx_sl into matchIdx_sl_old.
  iIntros (matchIdx_sl) "HmatchIdx_slice".

  wp_apply (wp_storeField with "[$HmatchIdx]").
  { apply slice_val_ty. }
  iIntros "HmatchIdx".
  wp_pures.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSlice).
  iClear "HreplicaClerks_slice".
  rename replicaClerks_sl into replicaClerks_sl_old.
  iIntros (replicaClerks_sl) "HreplicaClerks_slice".

  wp_apply (wp_storeField with "[$HreplicaClerks]").
  { apply slice_val_ty. }
  iIntros "HreplicaClerks".
  wp_pures.
  wp_loadField.
  wp_apply (wp_forSlice with "[] [] [-]").
  { (* step of loop *)
    admit.
  }
  { (* initial loop invariant *)
    admit.
  }
  (* rest of proof *)
  iNext.
Admitted.

End become_primary_proof.
