From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof pb_definitions pb_applybackup_proof pb_setstate_proof pb_getstate_proof pb_becomeprimary_proof pb_apply_proof pb_makeclerk_proof.

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
        "Hstate" ∷ own_StateMachine epoch σ sealed (own_Server_ghost γ γsrv) ∗
        "#His_sm" ∷ is_StateMachine sm_ptr own_StateMachine (own_Server_ghost γ γsrv) ∗
        "#Hsys_inv" ∷ sys_inv γ ∗
        "%HnextIndex" ∷ ⌜int.nat nextIndex = length σ⌝
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

  iAssert (_) with "His_sm" as "His_sm2".
  iNamed "His_sm2".
  wp_storeField.
  wp_pures.

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

  (* FIXME: need is_epoch_lb γsrv epoch upon initialization. Can put it as a
     second "synchronous" predicate in own_StateMachine. *)
  iSplitL; first admit.
  done.
Admitted.

Lemma wp_Server__Serve s host γ γsrv :
  {{{
        "#Hhost" ∷ is_pb_host host γ γsrv ∗
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    pb.Server__Serve #s #host
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.

  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_pures.
  wp_apply (map.wp_MapInsert with "Hhandlers").
  iIntros "Hhandlers".
  wp_pures.

  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  wp_apply (wp_StartServer2 with "[$Hr]").
  {
    set_solver.
  }
  {
    rewrite is_pb_host_unfold.
    iDestruct "Hhost" as "(H1&H2&H3&H4&H5&Hhandlers)".
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "Hhandlers".
      f_equal.
      set_solver.
    }

    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (??) "Hspec".
      iMod (readonly_alloc_1 with "Hreq_sl") as "#Hreq_sl".
      wp_apply (wp_Server__Apply with "Hsrv Hreq_sl [-Hspec] Hspec").
      iIntros (?) "Hspec".
      iIntros (?) "Hreply".
      wp_apply (ApplyReply.wp_Encode with "[$]").
      iIntros (??) "(%Henc_reply & Henc_rep_sl & Hreply)".
      iDestruct (is_slice_to_small with "Henc_rep_sl") as "Henc_rep_sl".
      wp_store.
      iApply ("HΦ" with "[Hspec] Hrep Henc_rep_sl").
      { iApply "Hspec". done. }
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (???) "[%Henc Hspec]".
      wp_apply (BecomePrimaryArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__BecomePrimary with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".
      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (int.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply ("HΦ" with "[HΨ] Hrep Hrep_sl").
      { iApply "HΨ". done. }
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (??) "[%Henc Hspec]".
      wp_apply (GetStateArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__GetState with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".
      iIntros (?) "Hreply".
      wp_apply (GetStateReply.wp_Encode with "Hreply").
      iClear "Hrep_sl".
      iIntros (??) "(%Henc_rep & Hrep_sl)".
      wp_store.
      simpl.
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply ("HΦ" with "[HΨ] Hrep Hrep_sl").
      { iApply "HΨ". done. }
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (??) "[%Henc Hspec]".
      wp_apply (SetStateArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__SetState with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".

      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (int.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply ("HΦ" with "[HΨ] Hrep Hrep_sl").
      { iApply "HΨ". done. }
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      unfold impl_handler_spec2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      iDestruct "Hspec" as (????) "[%Henc Hspec]".
      wp_apply (ApplyAsBackupArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__ApplyAsBackup with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".

      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iClear "Hrep_sl".
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (int.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply ("HΦ" with "[HΨ] Hrep Hrep_sl").
      { iApply "HΨ". done. }
    }
    iApply big_sepM_empty.
    done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End pb_start_proof.
