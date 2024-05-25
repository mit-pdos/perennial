From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial Require Export paxos.definitions paxos.applyasfollower_proof
     paxos.enternewepoch_proof paxos.becomeleader_proof paxos.clerk_proof.

Section start_proof.
Context `{!heapGS Σ}.
Context `{!paxosG Σ}.
Context `{Hparams:!paxosParams.t Σ}.
Import paxosParams.

Lemma wp_makeServer γ γsrv (fname:string) data conf_sl (hosts:list u64) init_sl :
  {{{
        "Hfile" ∷ crash_borrow (own_file_inv γ γsrv data ∗ fname f↦ data)
                (∃ d : list u8, own_file_inv γ γsrv d ∗ fname f↦d) ∗
        "#HP" ∷ (□ Pwf initstate) ∗
        "Hconf_sl" ∷ own_slice_small conf_sl uint64T (DfracOwn 1) hosts ∗
        "#Hhosts" ∷ is_paxos_hosts hosts γ ∗
        "#HinvHelping" ∷ is_helping_inv γ ∗
        "Hinitstate" ∷ own_slice_small init_sl byteT (DfracOwn 1) initstate

  }}}
    makeServer #(str fname) (slice_val init_sl) (slice_val conf_sl)
  {{{
        s, RET #s; is_Server s γ γsrv
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
  wp_apply wp_NewSlice.
  iIntros (?) "Hcls_sl".
  wp_bind (struct.storeF _ _ _ _)%E.
  iApply (wpc_wp _ _ _ _ True).
  wpc_apply (wpc_crash_borrow_open with "Hfile").
  { done. }
  iSplit; first done.
  iIntros "[Hinv Hf]".
  iNamed "Hinv".
  iAssert (□ Pwf _)%I with "[-]" as "#Hpwf".
  { iNamed "Hghost". iFrame "#". }
  iCache with "Hf Hghost".
  { by iFrame. }
  wpc_storeField.
  iSplitL "Hf Hghost".
  { by iFrame. }
  iIntros "Hfile". iSplit; first done.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hconf_sl") as %Hsz.
  iDestruct (big_sepL2_to_sepL_1 with "Hhosts") as "#Hhosts2".
  wp_apply (wp_forSlice'
              (λ i,
               ∃ sl cls,
               "Hcls" ∷ s ↦[Server :: "clerks"] (slice_val sl) ∗
               "Hcls_sl" ∷ own_slice sl ptrT (DfracOwn 1) (cls) ∗
               "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ cls ; (take (uint.nat i) γ.(s_hosts)),
                                   is_singleClerk ck γ γsrv') ∗
               "%Hsz" ∷ ⌜ length cls = uint.nat i ⌝
               )%I
             with "[] [clerks Hcls_sl $Hconf_sl]").
  2:{
    iFrame "Hhosts2".
    repeat iExists _.
    iFrame.
    iSplitR; last done.
    by iApply big_sepL2_nil.
  }
  {
    clear Φ.
    iIntros (???) "!# Hpre HΦ".
    wp_pures.
    iDestruct "Hpre" as "(%Hineq & %Hlookup & #Hhost & Hpre)".
    iNamed "Hpre".
    iDestruct "Hhost" as (?) "[%Hlookup2 Hhost]".
    wp_apply wp_makeSingleClerk.
    { iFrame "#". }
    iIntros (?) "#Hcl".
    wp_loadField.
    wp_bind (SliceAppend _ _ _).
    wp_apply (wp_SliceAppend with "[$Hcls_sl]").
    iIntros (?) "Hcls_sl".
    wp_storeField.
    iApply "HΦ".
    repeat iExists _; iFrame.
    iSplitL.
    2:{ iPureIntro. rewrite app_length. simpl. word. }
    replace (uint.nat (word.add i 1%Z)) with (S (uint.nat i)) by word.
    erewrite take_S_r; last done.
    iApply (big_sepL2_app with "[$]").
    iFrame "#". done.
  }
  iNamed 1.

  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (?) "Hencstate".
  wp_pures.
  wp_apply (wp_MakeAsyncFile _ fileN with "[$]").
  iIntros "* [#Hsl Hfile]".
  wp_pures.
  wp_store.
  wp_storeField.
  wp_load.
  wp_apply wp_slice_len.
  iMod (readonly_load with "Hsl") as (?) "Hsl2".
  rename Hsz into HhostSz.
  iDestruct (own_slice_small_sz with "[$Hsl2]") as %Hsz.
  iMod (readonly_alloc_1 with "mu") as "#mu".
  iMod (readonly_alloc_1 with "Hcls") as "#Hclerks".
  iDestruct (own_slice_to_small with "Hcls_sl") as "Hcls_sl".
  iMod (readonly_alloc_1 with "Hcls_sl") as "#Hcls_sl".
  wp_if_destruct.
  { (* case: empty file *)
    destruct data.
    2:{ exfalso. rewrite Heqb /= in Hsz. replace (uint.nat 0%Z) with 0%nat in Hsz by word. discriminate. }
    wp_apply wp_allocStruct; first by val_ty.
    iIntros (?) "Hps".
    iDestruct (struct_fields_split with "Hps") as "HH".
    iNamed "HH".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    simpl.
    iApply "HΦ".
    iMod (readonly_alloc_1 with "Hinitstate") as "#Hinit_sl".
    repeat iExists _.
    iFrame "#".
    iMod (alloc_lock with "HmuInv [-]") as "$".
    {
      iNext. repeat iExists _. iFrame.
      iSplitL.
      { repeat iExists _. instantiate (1:=paxosState.mk _ _ _ _ _). iFrame "∗#". }
      simpl. iFrame "HP".
      iPureIntro. right. done.
    }
    iDestruct (big_sepL2_length with "Hhosts") as %Hlen.
    rewrite Hlen.
    rewrite take_ge.
    2:{ rewrite -Hlen. word. }
    by iFrame "#".
  }
  { (* case: file had contents *)
    wp_load.
    destruct Henc as [Henc|[-> ->]].
    2:{
      exfalso.
      simpl in *. apply Heqb. repeat f_equal. word.
    }
    subst.
    wp_apply (paxosState.wp_decode with "[$Hsl2]").
    iIntros (?) "Hvol".
    wp_storeField.
    iApply "HΦ".
    repeat iExists _; iFrame "#".
    iMod (alloc_lock with "HmuInv [-]") as "$".
    {
      iNext. repeat iExists _. iFrame "∗#".
      iPureIntro. left. done.
    }
    iDestruct (big_sepL2_length with "Hhosts") as %Hlen.
    rewrite Hlen.
    rewrite take_ge.
    2:{ rewrite -Hlen. word. }
    by iFrame "#".
  }
Qed.

Lemma wp_StartServer γ γsrv (me:u64) (fname:string) data init_sl conf_sl (hosts:list u64) :
  {{{
        "Hfile" ∷ crash_borrow (own_file_inv γ γsrv data ∗ fname f↦ data)
                (∃ d : list u8, own_file_inv γ γsrv d ∗ fname f↦d) ∗
        "#HP" ∷ (□ Pwf initstate) ∗
        "Hconf_sl" ∷ own_slice_small conf_sl uint64T (DfracOwn 1) hosts ∗
        "#Hhost" ∷ is_paxos_server_host me γ γsrv ∗
        "#Hhosts" ∷ is_paxos_hosts hosts γ ∗
        "Hinitstate" ∷ own_slice_small init_sl byteT (DfracOwn 1) initstate

  }}}
    StartServer #(str fname) (slice_val init_sl) #me (slice_val conf_sl)
  {{{
        s, RET #s; is_Server s γ γsrv
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre". iNamed "Hhost".
  wp_call.
  wp_apply (wp_makeServer with "[$Hconf_sl $Hfile $Hinitstate]").
  { iFrame "#". }
  iIntros (s) "#His_srv".
  wp_pures.

  wp_apply (map.wp_NewMap).
  iIntros (handlers) "Hhandlers".


  wp_pures.
  wp_apply (map.wp_MapInsert u64 with "Hhandlers").
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

  iNamed "Hhost".
  wp_apply (wp_StartServer_pred with "[$Hr]").
  {
    set_solver.
  }
  {
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
      rewrite /is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      unfold becomeLeader_spec.
      simpl.
      wp_apply (wp_Server__TryBecomeLeader with "His_srv [HΦ Hrep] Hspec").
      iIntros "HΨ".
      wp_pures.

      iApply ("HΦ" with "[HΨ $Hrep]").
      iDestruct (own_slice_small_nil _ (DfracOwn 1)) as "$"; first done.
      iApply "HΨ".
    }

    iApply (big_sepM_insert_2 with "").
    { (* enterNewEpoch *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
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


      iDestruct (own_slice_small_nil byteT (DfracOwn 1) Slice.nil) as "Hsl".
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
      iApply ("HΦ" with "[HΨ $Hrep Hrep_sl]").
      iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      by iApply "HΨ".
    }
    iApply (big_sepM_insert_2 with "").
    { (* enterNewEpoch *)
      iExists _; iFrame "#".

      clear Φ.
      unfold is_urpc_handler_pred.
      iIntros (?????) "!# (Hreq_sl & Hrep & Hspec) HΦ".
      wp_pures.
      wp_apply (wp_allocStruct).
      { Transparent slice.T. repeat econstructor. Opaque slice.T. }
      iIntros (rep_ptr) "Hreply".

      iDestruct "Hspec" as (???) "Hspec".
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
      iApply ("HΦ" with "[HΨ $Hrep Hrep_sl]").
      iDestruct (own_slice_to_small with "Hrep_sl") as "$".
      by iApply "HΨ".
    }
    iApply big_sepM_empty.
    done.
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End start_proof.
