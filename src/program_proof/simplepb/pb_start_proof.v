From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_applybackup_proof pb_setstate_proof pb_getstate_proof pb_becomeprimary_proof pb_apply_proof pb_makeclerk_proof.

Section pb_start_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__ApplyAsBackup := (wp_Clerk__ApplyAsBackup (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).
Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__BecomePrimary := (wp_Clerk__BecomePrimary (pb_record:=pb_record)).
Notation wp_Clerk__Apply := (wp_Clerk__Apply (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Implicit Type (own_StateMachine: u64 → list OpType → bool → (u64 → list OpType → bool → iProp Σ) → iProp Σ).
Lemma wp_MakeServer sm_ptr own_StateMachine (epoch:u64) σ (sealed:bool) (nextIndex:u64) γ γsrv :
  {{{
        "Hstate" ∷ own_StateMachine epoch σ.*1 sealed (own_Server_ghost γ γsrv) ∗
        "#His_sm" ∷ is_StateMachine sm_ptr own_StateMachine (own_Server_ghost γ γsrv) ∗
        "#Hsys_inv" ∷ sys_inv γ ∗
        "%HnextIndex" ∷ ⌜int.nat nextIndex = length σ⌝ ∗

        (* FIXME: the pb user shouldn't need to know about these. Wrap this up in something *)
        (* It should be possible to get rid of these from *)
        "#Hs_acc_lb" ∷ is_accepted_lb γsrv epoch σ ∗
        "#Hs_prop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hs_prop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "#Hs_epoch_lb" ∷ is_epoch_lb γsrv epoch
  }}}
    pb.MakeServer #sm_ptr #nextIndex #epoch #sealed
  {{{
        s, RET #s; is_Server s γ γsrv
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  Opaque zero_val.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. Transparent zero_val. repeat econstructor. Opaque slice.T. Opaque zero_val. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  simpl.
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iExists _, _.
  iFrame "Hmu Hsys_inv".
  iMod (alloc_lock with "HmuInv [-]") as "$"; last done.

  (* now just need to establish lock invariant *)
  iNext.
  iExists _,_,_,_,_,_,_.
  iFrame "∗".
  iSplitL "clerks".
  {
    iApply to_named.
    instantiate (1:=Slice.nil).
    iExact "clerks".
  }
  iSplitR; first iExact "His_sm".
  iFrame "#".
  done.
Qed.

End pb_start_proof.
