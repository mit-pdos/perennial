From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial Require Import configservice.config_proof replica.protocol replica.definitions.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section proof.

Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.

Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!pbG Σ}.

Existing Instance toConfigParams.
Lemma lease_renewal_step γ γsrv γconf γl newLeaseExpiration st :
  is_lease config_proof.epochLeaseN γl (own_latest_epoch γconf st.(server.epoch)) -∗
  is_lease_valid_lb γl newLeaseExpiration -∗
  is_conf_inv γ γconf -∗
  own_Server_ghost_eph_f st γ γsrv -∗
  own_Server_ghost_eph_f (st <| server.leaseValid := true |>
                            <| server.leaseExpiration := newLeaseExpiration |>)
          γ γsrv
.
Proof.
  iIntros "#Hnew_lease #Hlb #Hconf".
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed 1.
  iFrame "∗#%".
  iNamed "Hlease".
  iClear "Hlease".
  repeat iExists _.
  iFrame "#%".
Qed.

Lemma wp_Server__leaseRenewalThread (s:loc) γ γsrv :
  {{{
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    Server__leaseRenewalThread #s
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "H _".
  iNamed "H".
  iNamed "Hsrv".
  wp_rec.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (latestEpoch_ptr) "HlatestEpoch".
  iAssert (∃ (latestEpoch:u64), "HlatestEpoch" ∷ latestEpoch_ptr ↦[uint64T] #latestEpoch)%I with "[-]" as "HH".
  { iExists _; iFrame. }
  wp_pures.
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  wp_load.
  wp_loadField.
  wp_bind (Clerk__GetLease _ _).
  wp_apply (wp_frame_wand with "[-]"); first iNamedAccu.
  wp_apply (config_proof.wp_Clerk__GetLease with "[$HconfCk_is]").
  iModIntro.
  iSplit.
  {
    (* got a lease *)
    iIntros (??) "#? #?".
    iNamed 1.
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    iNamed "Hvol".
    wp_loadField.
    wp_apply (wp_and' with "[HlatestEpoch] [] []"); first iNamedAccu.
    { iNamed 1. wp_load. wp_pures. iFrame. done. }
    { iIntros. wp_pures. iFrame. done. }
    iNamed 1.
    wp_if_destruct.
    { (* case: got lease in current epoch *)
      wp_storeField.
      wp_storeField.
      wp_loadField.
      destruct Heqb as [Heqb _].
      injection Heqb as Heqb.
      subst.
      iDestruct (lease_renewal_step with "[$] [$] [$] HghostEph") as "HghostEph".
      wp_apply (wp_Mutex__Unlock with "[- HlatestEpoch]").
      {
        iFrame "# Hlocked".
        iNext.
        repeat iExists _.
        iFrame "HghostEph".
        repeat iExists _.
        iFrame "∗#%".
      }
      wp_apply (wp_Sleep).
      wp_pures.
      iLeft.
      eauto with iFrame.
    }
    (* case: either got an RPC error or wrong epoch number *)
    wp_load.
    wp_loadField.
    wp_if_destruct.
    { (* have a new epoch to try getting a lease for *)
      wp_loadField.
      wp_store.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[- HlatestEpoch]").
      {
        iFrame "# Hlocked".
        iNext. repeat iExists _. iFrame "HghostEph".
        repeat iExists _. iFrame "∗#%".
      }
      wp_pures.
      iLeft. eauto with iFrame.
    }
    (* no new epoch. Sleep a bit and try again later. *)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[- HlatestEpoch]").
    {
      iFrame "# Hlocked".
      iNext. repeat iExists _. iFrame "HghostEph".
      repeat iExists _. iFrame "∗#%".
    }
    wp_apply wp_Sleep.
    wp_pures.
    iLeft. eauto with iFrame.
  }
  { (* the spec we wrote down for GetLease was a bit bad because it forces these
       two cases to be two different branches too early. There's really nothing
       going on here. *)
    iIntros (??). iNamed 1.
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    iNamed "Hvol".
    wp_loadField.
    wp_load.
    wp_apply (wp_and' with "[] [] []"); first iNamedAccu.
    { iNamed 1. wp_pures. iFrame. done. }
    { iIntros. wp_pures. iFrame. done. }
    iIntros "_".
    wp_if_destruct.
    { exfalso. destruct Heqb as [? Heqb]. by injection Heqb. }
    wp_load.
    wp_loadField.
    wp_if_destruct.
    { (* have a new epoch to try getting a lease for *)
      wp_loadField.
      wp_store.
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[- HlatestEpoch]").
      {
        iFrame "# Hlocked".
        iNext. repeat iExists _. iFrame "HghostEph".
        repeat iExists _. iFrame "∗#%".
      }
      wp_pures.
      iLeft. eauto with iFrame.
    }
    (* no new epoch. Sleep a bit and try again later. *)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[- HlatestEpoch]").
    {
      iFrame "# Hlocked".
      iNext. repeat iExists _. iFrame "HghostEph".
      repeat iExists _. iFrame "∗#%".
    }
    wp_apply wp_Sleep.
    wp_pures.
    iLeft. eauto with iFrame.
  }
Qed.

End proof.
