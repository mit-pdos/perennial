From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof pb_definitions pb_applybackup_proof pb_setstate_proof pb_getstate_proof pb_becomeprimary_proof pb_apply_proof pb_makeclerk_proof.
From iris.algebra Require Import mono_list.

Section pb_start_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__ApplyAsBackup := (wp_Clerk__ApplyAsBackup (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).
Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__BecomePrimary := (wp_Clerk__BecomePrimary (pb_record:=pb_record)).
Notation wp_Clerk__Apply := (wp_Clerk__Apply (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Implicit Type (own_StateMachine: u64 → list OpType → bool → (u64 → list OpType → bool → iProp Σ) → iProp Σ).
Lemma wp_MakeServer sm_ptr own_StateMachine (epoch:u64) opsfull (sealed:bool) (nextIndex:u64) γ γsrv γeph :
  {{{
        "Hstate" ∷ own_StateMachine epoch (get_rwops opsfull) sealed (own_Server_ghost γ γsrv γeph) ∗
        "#His_sm" ∷ is_StateMachine sm_ptr own_StateMachine (own_Server_ghost γ γsrv γeph) ∗
        "#Hsys_inv" ∷ sys_inv γ ∗
        "%HnextIndex" ∷ ⌜int.nat nextIndex = length (get_rwops opsfull)⌝ ∗
        "Heph" ∷ own_ephemeral_proposal γeph epoch opsfull ∗
        "Heph_unused" ∷ own_unused_ephemeral_proposals γeph epoch ∗
        (* XXX: this is basically a guarantee that the list of ops being
           implicitly passed in via own_StateMachine has been made durable. It
           would now be buggy to buffer an op in memory before passing a
           StateMachine into MakeServer because the Server tracks the
           durableNextIndex and initializes it here to be nextIndex. *)
        "#Hacc_lb" ∷ is_accepted_lb γsrv epoch opsfull
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
  wp_pure1_credit "Hlc".
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.

  iAssert (_) with "His_sm" as "His_sm2".
  iEval (rewrite /is_StateMachine /tc_opaque) in "His_sm2".
  iNamed "His_sm2".

  iMod ("HaccP" with "Hlc [] Hstate") as "Hstate".
  {
    instantiate (1:=(is_epoch_lb γsrv epoch ∗ is_proposal_lb γ epoch opsfull)%I).
    iIntros(???). iIntros "Hghost".
    iNamed "Hghost".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hlb".
    iNamed "Hghost".
    iAssert (⌜prefix opsfull opsfull0⌝)%I with "[-]" as %Hdone.
    {
      destruct sealedold.
      {
        iDestruct (own_valid_2 with "Haccepted_ro Hacc_lb") as %Hvalid.
        iPureIntro.
        rewrite singleton_op singleton_valid mono_list_both_dfrac_valid_L in Hvalid.
        destruct Hvalid as [_ H]. done.
      }
      {
        iDestruct (own_valid_2 with "Haccepted Hacc_lb") as %Hvalid.
        iPureIntro.
        rewrite singleton_op singleton_valid mono_list_both_dfrac_valid_L in Hvalid.
        destruct Hvalid as [_ H]. done.
      }
    }
    iFrame "Hlb".
    iSplitL.
    { iExists _; iFrame "∗#%". iModIntro. done. }
    iModIntro.
    iApply (own_mono with "Hproposal_lb").
    rewrite singleton_included.
    right.
    rewrite csum.Cinr_included.
    apply mono_list_lb_mono.
    done.
  }
  Search wpc_nval.
  wp_apply (wpc_nval_elim_wp with "Hstate").
  { done. }
  { done. }
  wp_storeField.
  iIntros "(Hstate & #Hepochlb & #Hprop_lb)".

  wp_pures.
  wp_storeField.

  wp_apply (wp_NewMap).
  iIntros (?) "Hmap".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "HmuInv").
  iIntros (durableCond) "[HmuInv #Hdurcond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "HmuInv").
  iIntros (roCond) "[HmuInv #Hrocond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "HmuInv").
  iIntros (commitCond) "[HmuInv #Hcommitcond]".
  wp_storeField.

  iApply "HΦ".
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  iExists _, _.
  iFrame "Hmu Hsys_inv".
  iExists γeph.
  iMod (alloc_lock with "HmuInv [-]") as "$"; last first.
  { time done. } (* PERF: why is this slow? *)

  (* now just need to establish lock invariant *)
  iNext.
  repeat iExists _.
  iFrame "∗".
  iSplitL "clerks".
  {
    iApply to_named.
    instantiate (1:=Slice.nil).
    iExact "clerks".
  }
  iFrame "#".
  iSplitR.
  { iApply big_sepM_empty. done. }
  iFrame "%".
  iSplitR.
  { admit. } (* FIXME: prove that is_proposal_valid is downwards closed. *)
  iSplitR.
  { iPureIntro. word. }
  { iPureIntro. word. }
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

  rewrite is_pb_host_unfold.
  iNamed "Hhost".
  wp_apply (wp_StartServer2 with "[$Hr]").
  {
    set_solver.
  }
  {
    iDestruct "Hhost" as "(H1&H2&H3&H4&H5&Hhandlers)".
    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "Hhandlers".
      f_equal.
      admit. (* FIXME: more RPC specs *)
    }

    iApply (big_sepM_insert_2 with "").
    { admit. }
    iApply (big_sepM_insert_2 with "").
    { admit. }

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
Admitted.

End pb_start_proof.
