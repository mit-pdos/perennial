From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export definitions applyasfollower_proof enternewepoch_proof becomeleader_proof.

Section start_proof.

Context `{!heapGS Σ}.
Context {mp_record:MPRecord}.
Notation OpType := (mp_OpType mp_record).
Notation has_op_encoding := (mp_has_op_encoding mp_record).
Notation next_state := (mp_next_state mp_record).
Notation compute_reply := (mp_compute_reply mp_record).
Notation is_Server := (is_Server (mp_record:=mp_record)).
Notation apply_core_spec := (apply_core_spec (mp_record:=mp_record)).
Notation is_singleClerk := (is_singleClerk (mp_record:=mp_record)).
Notation is_applyFn := (is_applyFn (mp_record:=mp_record)).
Notation is_mpaxos_host:= (is_mpaxos_host (mp_record:=mp_record)).

Context (conf:list mp_server_names).
Context `{!mpG Σ}.

Lemma wp_makeServer γ γsrv (fname:string) applyFn conf_sl (hosts:list u64) :
  {{{
        "#HapplyFn" ∷ is_applyFn applyFn ∗
        "Hconf_sl" ∷ own_slice_small conf_sl uint64T 1 hosts ∗
        "#Hhost" ∷ ([∗ list] _ ↦ host ; γsrv' ∈ hosts ; conf, is_mpaxos_host conf host γ γsrv' ) ∗
        "Hghost" ∷ own_replica_ghost conf γ γsrv (mkMPaxosState 0 0 [])
  }}}
    makeServer #(str fname) applyFn (slice_val conf_sl)
  {{{
        s, RET #s; is_Server conf s γ γsrv
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (mu) "HmuInv".
  wp_storeField.

  wp_apply (wp_NewSlice).
  iIntros (state_sl) "Hstate_sl".
  wp_storeField.

  wp_apply (wp_storeField with "[applyFn]").
  {
    unfold Server.
    unfold field_ty.
    simpl.
    admit. (* typecheck applyFn *)
  }
  { iFrame. }
  iIntros "applyFn".
  wp_pures.

  iDestruct (own_slice_small_sz with "Hconf_sl") as %Hconf_sz.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (clerks_sl) "Hclerks_sl".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_slice_len).
  iDestruct (own_slice_sz with "Hclerks_sl") as %Hclerks_sz.
  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (i_ptr) "Hi".
  wp_pures.
Admitted.

Lemma wp_StartServer γ γsrv (me:u64) (fname:string) applyFn conf_sl (hosts:list u64) :
  {{{
        "#HapplyFn" ∷ is_applyFn applyFn ∗
        "Hconf_sl" ∷ own_slice_small conf_sl uint64T 1 hosts ∗
        "#Hhost" ∷ is_mpaxos_host conf me γ γsrv ∗
        "#Hhosts" ∷ ([∗ list] _ ↦ host ; γsrv' ∈ hosts ; conf, is_mpaxos_host conf host γ γsrv' ) ∗
        "Hghost" ∷ own_replica_ghost conf γ γsrv (mkMPaxosState 0 0 [])
  }}}
    StartServer #(str fname) #me applyFn (slice_val conf_sl)
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_makeServer with "[$Hconf_sl $Hghost]").
  { iFrame "#". }
  iIntros (s) "#His_srv".
  wp_pures.

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

  simpl.

  wp_apply (urpc_proof.wp_MakeServer with "Hhandlers").
  iIntros (r) "Hr".
  wp_pures.

  wp_apply (wp_StartServer2 with "[$Hr]").
  {
    set_solver.
  }
  {
    iNamed "Hhost".

    unfold handlers_complete.
    repeat rewrite dom_insert_L.
    rewrite dom_empty_L.
    iSplitL "".
    {
      iExactEq "Hdom".
      f_equal.
      set_solver.
    }

    iApply (big_sepM_insert_2 with "").
    { (* becomeLeader *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      unfold becomeleader_spec.
      simpl.
      wp_apply (wp_Server__becomeLeader with "His_srv [HΦ Hrep Hrep_sl] Hspec").
      iIntros "HΨ".
      wp_pures.

      iApply ("HΦ" with "[HΨ] Hrep [Hrep_sl]").
      2:{
        iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      }
      { iApply "HΨ". }
    }

    iApply (big_sepM_insert_2 with "").
    { (* apply *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      unfold apply_spec.
      simpl.
      wp_apply (wp_allocStruct).
      { Transparent slice.T. repeat econstructor. Opaque slice.T. }
      iIntros (rep_ptr) "Hreply".

      iMod (readonly_alloc_1 with "Hreq_sl") as "#Hreq_sl".
      iDestruct "Hspec" as (??) "Hspec".
      wp_apply (wp_Server__Apply with "His_srv Hreq_sl [Hreply] [Hrep HΦ] Hspec").
      {
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        iExists _.
        instantiate (1:=applyReply.mkC _ _).
        replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done.
        simpl.
        iFrame "∗".
        iApply (own_slice_small_nil).
        done.
      }

      iIntros (?) "HΨ Hreply".
      wp_pures.
      wp_apply (applyReply.wp_Encode with "Hreply").
      iIntros (enc_reply rep_enc_sl) "[%Hrep_enc Hrep_sl]".
      wp_store.
      iApply ("HΦ" with "[HΨ] Hrep [Hrep_sl]").
      2:{
        iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      }
      { iApply "HΨ". done. }
    }
    iApply (big_sepM_insert_2 with "").
    { (* enterNewEpoch *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      unfold apply_spec.
      simpl.
      wp_apply (wp_allocStruct).
      { Transparent slice.T. repeat econstructor. Opaque slice.T. }
      iIntros (rep_ptr) "Hreply".

      iDestruct "Hspec" as (??) "Hspec".
      wp_pures.
      rewrite H.
      wp_apply (enterNewEpochArgs.wp_Decode with "[$Hreq_sl]").
      { done. }
      iIntros (?) "Hargs".
      wp_pures.


      iDestruct (own_slice_small_nil byteT 1 Slice.nil) as "Hsl".
      { done. }
      iMod (readonly_alloc_1 with "Hsl") as "#Hsl2".
      wp_apply (wp_Server__enterNewEpoch with "His_srv Hargs [Hreply] [Hrep HΦ] Hspec").
      {
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        iExists _.
        instantiate (1:=enterNewEpochReply.mkC _ _ _ _).
        replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done.
        simpl.
        iFrame "∗#".
      }

      iIntros (?) "HΨ Hreply".
      wp_pures.
      wp_apply (enterNewEpochReply.wp_Encode with "Hreply").
      iIntros (enc_reply rep_enc_sl) "[%Hrep_enc Hrep_sl]".
      wp_store.
      iApply ("HΦ" with "[HΨ] Hrep [Hrep_sl]").
      2:{
        iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      }
      { iApply "HΨ". done. }
    }
    iApply (big_sepM_insert_2 with "").
    { (* enterNewEpoch *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred2.
      iIntros (???????) "!# Hreq_sl Hrep Hrep_sl HΦ Hspec".
      wp_pures.
      unfold apply_spec.
      simpl.
      wp_apply (wp_allocStruct).
      { Transparent slice.T. repeat econstructor. Opaque slice.T. }
      iIntros (rep_ptr) "Hreply".

      iDestruct "Hspec" as (????) "Hspec".
      wp_pures.
      rewrite H.
      wp_apply (applyAsFollowerArgs.wp_Decode with "[$Hreq_sl]").
      { done. }
      iIntros (?) "Hargs".
      wp_pures.

      wp_apply (wp_Server__applyAsFollower with "His_srv Hargs [Hreply] [Hrep HΦ] Hspec").
      {
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        instantiate (1:=applyAsFollowerReply.mkC _).
        iFrame.
      }

      iIntros (?) "HΨ Hreply".
      wp_pures.
      wp_apply (applyAsFollowerReply.wp_Encode with "Hreply").
      iIntros (enc_reply rep_enc_sl) "[%Hrep_enc Hrep_sl]".
      wp_store.
      iApply ("HΦ" with "[HΨ] Hrep [Hrep_sl]").
      2:{
        iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      }
      { iApply "HΨ". done. }
    }
    iApply big_sepM_empty.
    done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_proof.
