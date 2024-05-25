From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export replica.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial Require Import replica.marshal_proof
     replica.definitions replica.applybackup_proof replica.setstate_proof replica.getstate_proof
     replica.becomeprimary_proof replica.apply_proof replica.roapply_proof replica.makeclerk_proof
     replica.increasecommit_proof replica.leaserenewal_proof replica.sendcommitthread_proof.
From Perennial Require Import replica.config_protocol_proof.
From iris.algebra Require Import mono_list.

Section proof.

Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!heapGS Σ}.
Context `{!pbG Σ}.

Implicit Type (own_StateMachine: u64 → list OpType → bool → (u64 → list OpType → bool → iProp Σ) → iProp Σ).
Lemma wp_MakeServer sm_ptr own_StateMachine (epoch:u64) (confHosts:list u64) opsfull (sealed:bool) (nextIndex:u64) γ γsrv
      confHosts_sl host :
  {{{
        "Hstate" ∷ own_StateMachine epoch (get_rwops opsfull) sealed (own_Server_ghost_f γ γsrv) ∗
        "#His_sm" ∷ is_StateMachine sm_ptr own_StateMachine (own_Server_ghost_f γ γsrv) ∗

        "#Hconf_host" ∷ is_pb_config_hosts confHosts γ ∗
        "#Hhost" ∷ is_pb_host host γ γsrv ∗

        "#Hconf_host_sl" ∷ readonly (own_slice_small (confHosts_sl) uint64T (DfracOwn 1) confHosts) ∗
        "%HnextIndex" ∷ ⌜uint.nat nextIndex = length (get_rwops opsfull)⌝ ∗
        (* XXX: this is basically a guarantee that the list of ops being
           implicitly passed in via own_StateMachine has been made durable. It
           would now be buggy to buffer an op in memory before passing a
           StateMachine into MakeServer because the Server tracks the
           durableNextIndex and initializes it here to be nextIndex. *)
        "#Hacc_lb" ∷ is_accepted_lb γsrv.(r_pb) epoch opsfull
  }}}
    MakeServer #sm_ptr (slice_val confHosts_sl) #nextIndex #epoch #sealed
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
  repeat wp_storeField.

  iAssert (_) with "His_sm" as "His_sm2".
  iEval (rewrite /is_StateMachine /tc_opaque) in "His_sm2".
  iNamed "His_sm2".

  iMod ("HaccP" with "Hlc [] Hstate") as "Hstate".
  {
    instantiate (1:=(is_epoch_lb γsrv.(r_pb) epoch ∗ is_proposal_lb γ.(s_pb) epoch opsfull ∗
                     is_proposal_facts γ.(s_pb) epoch opsfull ∗
                     is_proposal_facts_prim γ.(s_prim) epoch opsfull ∗
                     is_in_config γ γsrv epoch)%I).
    iIntros(???). iIntros "Hghost".
    iNamed "Hghost".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hlb".
    iNamed "Hghost".
    iAssert (⌜prefix opsfull opsfull0⌝)%I with "[-]" as %Hdone.
    {
      destruct sealedold.
      { by iDestruct (fmlist_ptsto_lb_agree with "Haccepted_ro Hacc_lb") as %?. }
      { by iDestruct (fmlist_ptsto_lb_agree with "Haccepted Hacc_lb") as %?. }
    }
    apply list_prefix_eq in Hdone.
    2:{
      apply prefix_length in H, Hdone.
      apply (f_equal length) in Hre.
      rewrite fmap_length in H, Hre.
      rewrite fmap_length in H, Hre.
      word.
    }
    subst.
    by iFrame "#∗%".
  }

  iDestruct "Hstate" as "(Hstate & #Hepochlb & #Hprop_lb & #Hprop_facts & #Hprim_facts & #Hin_conf)".

  wp_apply (wp_NewMap u64).
  iIntros (?) "Hmap".
  wp_storeField.

  iDestruct "Hconf_host" as (?) "[#Hconf_host1 #Hconf_inv]".
  wp_apply (config_proof.wp_MakeClerk with "[]").
  { iFrame "#%". }
  iIntros (confCk) "#HconfCk".
  wp_storeField.

  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pb_protocolN)) as "Hmask".
  { set_solver. }
  iNamed "Hhost".
  iDestruct "Hinvs" as "(#? & #? & #? & #?)".
  iMod (pb_log_get_nil_lb with "[$]") as "#Hcommit_nil_lb".
  iMod "Hmask".
  iModIntro.

  wp_loadField.
  wp_apply (wp_newCond' with "HmuInv").
  iIntros (commitCond) "[HmuInv #Hcommitcond]".
  wp_storeField.


  wp_loadField.
  wp_apply (wp_newCond' with "HmuInv").
  iIntros (primaryCond) "[HmuInv #HisPrimary_cond]".
  wp_storeField.

  iApply "HΦ".
  iMod (readonly_alloc_1 with "mu") as "#Hmu".
  repeat iExists _. iFrame "Hmu #".
  iMod (readonly_alloc_1 with "confCk") as "#confCk".
  iMod (alloc_lock with "HmuInv [-]") as "$"; last first.
  { repeat iExists _.
    iNamed "Hconf_inv".
    iModIntro. iFrame "#".
  }

  (* now just need to establish lock invariant *)
  iNext.
  repeat iExists _.
  iSplitL.
  {
    repeat iExists _.
    instantiate (1:=(server.mkC _ _ _ _ _ _ _ _ _)).
    simpl.
    iFrame "∗".
    iSplitL "nextIndex".
    {
      iApply to_named. iExactEq "nextIndex".
      repeat f_equal. word.
    }
    iSplitL "clerks".
    {
      iApply to_named.
      instantiate (1:=Slice.nil).
      iExact "clerks".
    }
    iFrame "#".
    iSplitL.
    { iApply big_sepM_empty. done. }
    iSplitL.
    { by iLeft. }
    iPureIntro. unfold no_overflow. word.
  }
  rewrite /own_Server_ghost_eph_f /tc_opaque /=.
  repeat iExists _; iFrame.
  instantiate (1:=[]).
  iSplitL.
  {
    rewrite /own_Primary_ghost_f /tc_opaque.
    by iFrame "#".
  }
  iFrame "#".
  iSplitR; first by iModIntro.
  iSplitR.
  { iModIntro. iIntros (????) "_ _". iPureIntro. apply prefix_nil. }
  iSplitR.
  { iDestruct (fmlist_ptsto_lb_mono with "Hprop_lb") as "$".
    apply prefix_nil.
  }
  by iPureIntro.
Qed.

Lemma wp_Server__Serve s host γ γsrv :
  {{{
        "#Hhost" ∷ is_pb_host host γ γsrv ∗
        "#Hsrv" ∷ is_Server s γ γsrv
  }}}
    Server__Serve #s #host
  {{{
        RET #(); True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre". iNamed "Hhost".
  wp_call.

  wp_apply (map.wp_NewMap u64).
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

  rewrite is_pb_rpcs_unfold.
  iNamed "Hhost".
  wp_apply (wp_StartServer_pred with "[$Hr]").
  {
    set_solver.
  }
  {
    iDestruct "Hhost" as "(H1&H2&H3&H4&H5&H6&H7&Hhandlers)".
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
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "[% Hspec]".
      subst. wp_call.
      wp_apply (wp_ReadInt with "[$]").
      iIntros (?) "_". wp_pures.
      wp_apply (wp_Server__IncreaseCommit with "Hsrv [-Hspec] Hspec").
      iIntros "Hspec".
      wp_pures.
      iApply "HΦ". iFrame.
      instantiate (1:=DfracOwn 1).
      iApply own_slice_small_nil.
      done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "Hspec".
      iMod (readonly_alloc_1 with "Hreq_sl") as "#Hreq_sl".
      wp_apply (wp_Server__ApplyRo with "Hsrv Hreq_sl [-Hspec] Hspec").
      iIntros (?) "Hspec".
      iIntros (?) "Hreply".
      wp_apply (ApplyReply.wp_Encode with "[$]").
      iIntros (??) "(%Henc_reply & Henc_rep_sl & Hreply)".
      iDestruct (own_slice_to_small with "Henc_rep_sl") as "Henc_rep_sl".
      wp_store.
      iApply "HΦ". iFrame.
      iApply "Hspec". done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (?) "Hspec".
      iMod (readonly_alloc_1 with "Hreq_sl") as "#Hreq_sl".
      wp_apply (wp_Server__Apply with "Hsrv Hreq_sl [-Hspec] Hspec").
      iIntros (?) "Hspec".
      iIntros (?) "Hreply".
      wp_apply (ApplyReply.wp_Encode with "[$]").
      iIntros (??) "(%Henc_reply & Henc_rep_sl & Hreply)".
      iDestruct (own_slice_to_small with "Henc_rep_sl") as "Henc_rep_sl".
      wp_store.
      iApply "HΦ". iFrame.
      iApply "Hspec". done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (???) "[%Henc Hspec]".
      wp_apply (BecomePrimaryArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__BecomePrimary with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".
      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (uint.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ". iFrame.
      iApply "HΨ". done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (??) "[%Henc Hspec]".
      wp_apply (GetStateArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__GetState with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".
      iIntros (?) "Hreply".
      wp_apply (GetStateReply.wp_Encode with "Hreply").
      iIntros (??) "(%Henc_rep & Hrep_sl)".
      wp_store.
      simpl.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ". iFrame.
      iApply "HΨ". done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (??) "[%Henc Hspec]".
      wp_apply (SetStateArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__SetState with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".

      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (uint.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ". iFrame.
      iApply "HΨ". done.
    }
    iApply (big_sepM_insert_2 with "").
    {
      iExists _; iFrame "#".
      clear Φ.
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      iDestruct "Hspec" as (????) "[%Henc Hspec]".
      wp_apply (ApplyAsBackupArgs.wp_Decode with "[$Hreq_sl //]").
      iIntros (?) "Hargs".

      wp_apply (wp_Server__ApplyAsBackup with "Hsrv Hargs [-Hspec] Hspec").
      iIntros (?) "HΨ".

      wp_call.
      wp_apply (wp_NewSliceWithCap).
      { done. }
      iIntros (?) "Hrep_sl".
      wp_apply (marshal_stateless_proof.wp_WriteInt with "[$]").
      iIntros (?) "Hrep_sl".
      wp_store.
      simpl.
      replace (uint.nat 0%Z) with (0) by word.
      simpl.
      iDestruct (own_slice_to_small with "Hrep_sl") as "Hrep_sl".
      iApply "HΦ". iFrame.
      iApply "HΨ". done.
    }
    iApply big_sepM_empty.
    done.
  }
  wp_pures.
  wp_apply wp_fork.
  {
    wp_apply wp_Server__leaseRenewalThread.
    { iFrame "#". }
    done.
  }
  wp_pures.

  wp_apply wp_fork.
  {
    wp_apply wp_Server__increaseCommitThread.
    { iFrame "#". }
    done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
