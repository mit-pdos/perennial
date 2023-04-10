From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import config_proof pb_definitions pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_leaserenewal_proof.

Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation "server.t" := (server.t (pb_record:=pb_record)).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!pbG Σ}.

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
  simpl.
  repeat iExists _; iFrame "#".
Qed.

Lemma wp_Server__leaseRenewalThread (s:loc) γ γsrv (epoch:u64) :
  {{{
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    pb.Server__leaseRenewalThread #s #epoch
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (?) "H HΦ".
  iNamed "H".
  iNamed "Hsrv".
  wp_lam.
  iApply (wp_frame_wand with "[HΦ]").
  { iNamedAccu. }
  wp_pures.
  wp_forBreak.

  wp_pures.
  wp_loadField.
  wp_apply (config_proof.wp_Clerk__GetLease with "[$HconfCk_is]").
  iModIntro.
  iSplit.
  2: { (* case: got error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    2: by exfalso.
    iModIntro.
    by iLeft.
  }
  (* otherwise, got a lease *)
  iIntros.
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  iNamed "Hvol".
  wp_loadField.
  wp_if_destruct.
  2:{ (* case: epoch mismatch *)
    wp_loadField.
    wp_apply (release_spec with "[-]").
    {
      iFrame "# Hlocked".
      iNext.
      repeat iExists _.
      iFrame "HghostEph".
      repeat iExists _.
      iFrame "∗#%".
    }
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    iModIntro.
    iNamed 1.
    by iApply "HΦ".
  }
  (* case: got lease and the epoch is still the server's epoch *)
  wp_storeField.
  wp_storeField.
  iDestruct (lease_renewal_step with "[$] [$] [$] HghostEph") as "HghostEph".
  wp_loadField.
  wp_apply (release_spec with "[-]").
  {
    iFrame "# Hlocked".
    iNext.
    repeat iExists _.
    iFrame "HghostEph".
    repeat iExists _.
    iFrame "∗#%".
  }
  wp_pures.
  wp_apply (wp_Sleep).
  wp_pures.
  by iLeft.
Qed.

End pb_leaserenewal_proof.
