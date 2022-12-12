From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions config_proof pb_setstate_proof pb_getstate_proof pb_becomeprimary_proof pb_makeclerk_proof.

Section config_global.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).

Context `{!gooseGlobalGS Σ}.
Context `{!configG Σ}.
Context `{!pbG Σ}.

Definition adminN := nroot .@ "admin".

Definition is_conf_inv γpb γconf : iProp Σ :=
  inv adminN (∃ epoch conf (confγs:list pb_server_names) epoch_lb,
      "Hepoch" ∷ config_proof.own_epoch γconf epoch ∗
      "Hconf" ∷ own_config γconf conf ∗
      "#His_conf" ∷ is_epoch_config γpb epoch_lb confγs ∗
      "#His_conf_prop" ∷ is_epoch_config_proposal γpb epoch_lb confγs ∗
      "#His_hosts" ∷ ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γpb γsrv) ∗
      "#His_lbs" ∷ (∀ γsrv, ⌜γsrv ∈ confγs⌝ → pb_ghost.is_epoch_lb γsrv epoch_lb) ∗
      "Hunused" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch < int.nat epoch'⌝ → config_proposal_unset γpb epoch' ∗ config_unset γpb epoch' ∗ own_proposal_unused γpb epoch' ∗ own_init_proposal_unused γpb epoch') ∗
      "Hunset_or_set" ∷ (config_unset γpb epoch ∨ ⌜int.nat epoch_lb = int.nat epoch⌝) ∗
      "#His_skip" ∷ (∀ epoch_skip, ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch⌝ → is_epoch_skipped γpb epoch_skip)
      )
.

(* before calling this lemma, have to already allocate pb ghost state *)
Lemma config_ghost_init_2 γsys conf confγs :
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γsys γsrv) -∗
  pb_init_config γsys confγs
  ={⊤}=∗ ∃ γconf, is_conf_inv γsys γconf ∗ makeConfigServer_pre γconf.
Proof.
  iIntros "#Hhosts Hinitconf".
  iMod (config_ghost_init conf) as (γconf) "(Hconfpre & Hepoch & Hconf)".
  iExists _; iFrame "Hconfpre".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iNext.
  iExists (U64 0), conf, confγs, (U64 0).
  iFrame.
  iNamed "Hinitconf".
  iFrame "∗#%".
  iSplitR.
  { iRight. done. }
  iIntros (???).
  exfalso.
  word.
Qed.

End config_global.

Section admin_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.
Context `{!configG Σ}.
Context `{!waitgroupG Σ}.

Definition is_conf_host confHost γpb : iProp Σ :=
  ∃ γconf,
  config_proof.is_host confHost γconf ∗ is_conf_inv γpb γconf.

Definition is_Clerk2 ck γpb : iProp Σ :=
  ∃ γconf,
    "#Hinv" ∷ is_conf_inv γpb γconf ∗
    "#Hck" ∷ is_Clerk ck γconf.

Lemma wp_MakeClerk2 (configHost:u64) γpb :
  {{{
        is_conf_host configHost γpb
  }}}
    config.MakeClerk #configHost
  {{{
      ck, RET #ck; is_Clerk2 ck γpb
  }}}.
Proof.
  iIntros (Φ) "#Hhost HΦ".
  iDestruct "Hhost" as (?) "[Hhost Hinv]".
  wp_apply (config_proof.wp_MakeClerk with "[$Hhost]").
  iIntros.
  iApply "HΦ".
  iExists  _; iFrame "#".
Qed.

Lemma wp_Clerk__GetConfig2 ck γpb Φ :
  is_Clerk2 ck γpb -∗
  □(∀ confγs (conf:list u64) config_sl,
  (is_slice_small config_sl uint64T 1 conf ∗
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γpb γsrv) -∗
   Φ (slice_val config_sl)%V
  )) -∗
  WP config.Clerk__GetConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__GetConfig with "[$Hck]").
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _.
  iFrame.
  iIntros "Hconfig".
  iMod "Hmask".
  iMod ("Hclose" with "[-]").
  {
    iNext. iExists _, _, _, _.
    iFrame "∗#%".
  }
  iModIntro.
  iIntros (?) "Hconf".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_Clerk__GetEpochAndConfig2 ck γpb Φ :
  is_Clerk2 ck γpb -∗
  □(∀ (epoch epoch_lb:u64) confγs (conf:list u64) config_sl,
  (is_slice_small config_sl uint64T 1 conf ∗
  config_proposal_unset γpb epoch ∗
  own_proposal_unused γpb epoch ∗
  own_init_proposal_unused γpb epoch ∗
  is_epoch_config γpb epoch_lb confγs ∗
  (∀ epoch_skip, ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch⌝ → is_epoch_skipped γpb epoch_skip) ∗
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γpb γsrv) ∗
  (∀ γsrv, ⌜γsrv ∈ confγs⌝ → pb_ghost.is_epoch_lb γsrv epoch_lb)) -∗
   Φ (#epoch, slice_val config_sl)%V
  ) -∗
  WP config.Clerk__GetEpochAndConfig #ck {{ Φ }}
.
Proof.
  iIntros "#Hck #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__GetEpochAndConfig with "[$Hck]").
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _, _.
  iFrame.
  iIntros "%Hno_overflow Hepoch Hconf".
  iMod "Hmask".

  (* Hunset becomes skipped, and the first unused becomes unset. *)
  iDestruct (big_sepS_elem_of_acc_impl (word.add epoch (U64 1)) with "Hunused") as "[Hunset_new Hunused]".
  { set_solver. }

  iSpecialize ("Hunset_new" with "[]").
  { done. }
  iDestruct "Hunset_new" as "(Hunset_new & Hunset_new2 & Hprop)".

  iDestruct "Hunset_or_set" as "[Hunset|%Hset]".
  {
    iMod (own_update with "Hunset") as "Hskip1".
    {
      apply singleton_update.
      apply dfrac_agree_persist.
    }
    iDestruct "Hskip1" as "#Hskip1".

    iMod ("Hclose" with "[Hunset_new2 Hunused Hepoch Hconf]").
    {
      iNext. iExists _, _, _, _.
      iFrame "∗#".
      iSplitL "Hunused".
      {
        iApply "Hunused".
        {
          iModIntro.
          iIntros (???) "H". iIntros.
          iApply "H".
          iPureIntro.
          word.
        }
        {
          iIntros. exfalso. word.
        }
      }
      iIntros (???).
      assert (int.nat epoch_skip = int.nat epoch ∨ int.nat epoch_skip < int.nat epoch ∨ int.nat epoch_skip >= int.nat (word.add epoch (U64 1))) as Hineq.
      { word. }
      destruct Hineq as [Heq|[Hineq|Hineq]].
      {
        replace (epoch_skip) with (epoch) by word.
        iFrame "Hskip1".
      }
      {
        iApply "His_skip".
        { done. }
        { done. }
      }
      { exfalso. word. }
    }
    iModIntro.
    iIntros.
    iApply "HΦ".
    iDestruct "Hprop" as "[$ $]".
    iFrame "∗#".

    (* TODO: repetetive proof *)
    iIntros.
    assert (int.nat epoch_skip = int.nat epoch ∨ int.nat epoch_skip < int.nat epoch ∨ int.nat epoch_skip >= int.nat (word.add epoch (U64 1))) as Hineq.
    { word. }
    destruct Hineq as [Heq|[Hineq|Hineq]].
    {
      replace (epoch_skip) with (epoch) by word.
      iFrame "Hskip1".
    }
    {
      iApply "His_skip".
      { done. }
      { done. }
    }
    { exfalso. word. }
  }
  {
    iClear "His_skip".

    iMod ("Hclose" with "[Hunset_new2 Hunused Hepoch Hconf]").
    {
      iNext. iExists _, _, _, _.
      iFrame "∗#".
      iSplitL "Hunused".
      {
        iApply "Hunused".
        {
          iModIntro.
          iIntros (???) "H". iIntros.
          iApply "H".
          iPureIntro.
          word.
        }
        {
          iIntros. exfalso. word.
        }
      }
      iIntros (???).
      exfalso.
      rewrite Hset in H.
      replace (int.nat (word.add epoch 1%Z)) with (int.nat epoch + 1) in H0 by word.
      word.
    }
    iModIntro.
    iIntros.
    iApply "HΦ".
    iDestruct "Hprop" as "[$ $]".
    iFrame "∗#".
    iIntros (???).
    exfalso.
    rewrite Hset in H.
    replace (int.nat (word.add epoch 1%Z)) with (int.nat epoch + 1) in H0 by word.
    word.
  }
Qed.

Lemma wp_Clerk__WriteConfig2 ck γpb Φ config_sl conf confγ epoch :
  is_Clerk2 ck γpb -∗
  is_slice_small config_sl uint64T 1 conf -∗
  is_epoch_config_proposal γpb epoch confγ -∗
  ([∗ list] γsrv ; host ∈ confγ ; conf, is_pb_host host γpb γsrv) -∗
  (∀ γsrv, ⌜γsrv ∈ confγ⌝ → pb_ghost.is_epoch_lb γsrv epoch) -∗
  □ (∀ (err:u64),
      (if (decide (err = U64 0)) then
        is_epoch_config γpb epoch confγ
      else
        True) -∗
      is_slice_small config_sl uint64T 1 conf -∗
      Φ #err)
  -∗
  WP config.Clerk__WriteConfig #ck #epoch (slice_val config_sl) {{ Φ }}
.
Proof.
  iIntros "#Hck Hsl #Hconf_prop #Hhosts #Hlbs #HΦ".
  iNamed "Hck".
  wp_apply (wp_Clerk__WriteConfig with "Hck Hsl"); last first.
  {
    iIntros.
    iApply ("HΦ" with "[] [$]").
    destruct (decide _).
    { exfalso. done. }
    done.
  }
  iModIntro.
  iIntros "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iApply fupd_mask_intro.
  { set_solver. }
  iIntros "Hmask".
  iNamed "Hi".
  iExists _.
  iFrame "∗".
  destruct (decide (_)); last first.
  { (* write failed because of stale epoch. *)
    iIntros "Hepoch".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[Hepoch Hconf Hunused Hunset_or_set]").
    {
      iNext.  iExists _, _, _, _.
      iFrame "∗#".
    }
    iModIntro.
    iIntros (??) "Hsl".
    wp_pures.
    iApply ("HΦ" with "[] Hsl").
    destruct (decide (_)).
    { exfalso. done. }
    done.
  }
  { (* successful write *)
    rewrite e.
    iExists _.
    iFrame.
    iIntros "Hconf Hepoch".
    iMod "Hmask" as "_".

    iDestruct "Hunset_or_set" as "[Hunset|%Hset]"; last first.
    { (* config was already set before *)
      replace (epoch) with (epoch_lb) by word.
      iDestruct "Hconf_prop" as "[Hconf_prop %Hle]".
      iDestruct "His_conf_prop" as "[His_conf_prop _]".
      iDestruct (own_valid_2 with "His_conf_prop Hconf_prop") as %Hvalid.
      rewrite singleton_op in Hvalid.
      rewrite singleton_valid in Hvalid.
      rewrite dfrac_agree_op_valid in Hvalid.
      replace confγ with confγs in * by naive_solver.

      iMod ("Hclose" with "[Hepoch Hconf Hunused]").
      {
        iNext.  iExists _, _, _, _.
        iFrame "∗#".
        iSplitL; first done.
        by iRight.
      }
      iApply "HΦ".
      iModIntro.
      iFrame "#".
    }
    { (* config is being set for the first time *)
      iMod (own_update with "Hunset") as "Hset".
      {
        apply singleton_update.
        apply cmra_update_exclusive.
        instantiate (1:=(to_dfrac_agree (DfracOwn 1) ((Some confγ) : (leibnizO _)))).
        done.
      }
      iMod (own_update with "Hset") as "Hset".
      { apply singleton_update. apply dfrac_agree_persist. }
      iDestruct "Hset" as "#Hset".
      iMod ("Hclose" with "[Hconf Hepoch Hunused]").
      {
        iNext. iExists _, _, _, _.
        iFrame "∗#".
        iDestruct "Hconf_prop" as "[_ %Hineq]".
        iSplitR; first done.
        iSplitL.
        { by iRight. }
        iIntros (???).
        exfalso.
        word.
      }
      iApply "HΦ".
      iDestruct "Hconf_prop" as "[_ %Hineq]".
      iFrame "#".
      done.
    }
  }
Qed.

Lemma wp_Reconfig γ (configHost:u64) (servers:list u64) (servers_sl:Slice.t) server_γs :
  {{{
        "Hservers_sl" ∷ is_slice servers_sl uint64T 1 servers ∗
        "#Hhost" ∷ ([∗ list] γsrv ; host ∈ server_γs ; servers, is_pb_host host γ γsrv) ∗
        "#Hconf_host" ∷ is_conf_host configHost γ
  }}}
    EnterNewConfig #configHost (slice_val servers_sl)
  {{{
        (err:u64), RET #err; True
  }}}.
Proof using waitgroupG0.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.

  wp_apply (wp_slice_len).
  wp_pures.
  iDestruct (is_slice_sz with "Hservers_sl") as %Hservers_sz.
  wp_if_destruct.
  {
    by iApply "HΦ".
  }

  wp_apply (wp_MakeClerk2 with "Hconf_host").
  iIntros (ck) "#Hck".
  wp_pures.
  wp_bind (Clerk__GetEpochAndConfig _).
  iApply (wp_frame_wand with "[HΦ Hservers_sl]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__GetEpochAndConfig2 with "[$Hck]").
  iModIntro.
  iIntros (?????) "Hpost1".
  iNamed 1.
  wp_pures.
  unfold prelude.Data.randomUint64.
  wp_pures.
  set (s:=(u64_instance.u64.(word.add) (U64 0) (U64 1))).
  generalize s as randId.
  clear s.
  intros randId.
  wp_apply (wp_slice_len).
  wp_pures.

  iDestruct "Hpost1" as "(Hconf_sl & Hconf_unset & Hprop & Hinit & #His_conf & #Hskip & #His_hosts & #Hlb)".

  iAssert (⌜length conf ≠ 0⌝)%I as %Hold_conf_ne.
  {
    iDestruct "His_conf" as "[_ %Hconfγ_nz]".
    iDestruct (big_sepL2_length with "His_hosts") as %Heq.
    iPureIntro.
    lia.
  }
  iDestruct (is_slice_small_sz with "Hconf_sl") as %Hconf_len.
  set (oldNodeId:=word.modu randId config_sl.(Slice.sz)).
  assert (int.nat oldNodeId < length conf) as Hlookup_conf.
  { rewrite Hconf_len.
    unfold oldNodeId.
    enough (int.Z randId `mod` int.Z config_sl.(Slice.sz) < int.Z config_sl.(Slice.sz))%Z.
    { word. }
    apply Z.mod_pos_bound.
    word.
  }
  apply lookup_lt_is_Some_2 in Hlookup_conf as [host Hlookup_conf].
  wp_apply (wp_SliceGet with "[$Hconf_sl]").
  { done. }
  iIntros "Hconf_sl".
  simpl.
  (* FIXME: how does wp_MakeClerk work here? *)
  iDestruct (big_sepL2_lookup_2_some with "His_hosts") as %HH.
  { done. }
  destruct HH as [γsrv_old Hconfγ_lookup].
  wp_apply (wp_MakeClerk with "[]").
  {
    iDestruct (big_sepL2_lookup_acc with "His_hosts") as "[$ _]"; done.
  }
  iIntros (oldClerk) "#HoldClerk".
  wp_pures.

  (* Get the old state *)
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_apply (wp_Clerk__GetState with "[$HoldClerk $Epoch]").
  {
    iApply "Hlb".
    iPureIntro.
    eapply elem_of_list_lookup_2.
    done.
  }
  iIntros (reply err) "Hpost".
  wp_pures.
  destruct (decide (err = _)); last first.
  { (* err ≠ 0; error. *)
    iNamed "Hpost".
    wp_loadField.
    wp_pures.
    rewrite bool_decide_false; last naive_solver.
    wp_pures.
    wp_loadField.
    simpl.
    iApply "HΦ".
    done.
  }
  (* err = 0; keep going with reconfig *)
  (* Got the old state now *)
  iDestruct "Hpost" as (???) "(%Hepoch_lb_ineq & %Hepoch_ub_ineq & #Hacc_ro & #Hprop_facts & #Hprop_lb & Hreply & %Henc & %Hlen_no_overflow)".
  destruct (decide (int.nat epochacc = int.nat epoch)) as [Heq|Hepochacc_ne_epoch].
  {
    replace (epochacc) with (epoch) by word.
    iDestruct (own_valid_2 with "Hprop Hprop_lb") as %Hvalid.
    exfalso.
    rewrite singleton_op singleton_valid in Hvalid.
    rewrite auth_map.Cinl_Cinr_op in Hvalid.
    done.
  }
  iMod (ghost_init_primary with "Hprop_lb Hprop_facts His_conf Hacc_ro Hskip Hprop Hinit") as "(Hprop & #Hprop_facts2 & #Hinit)".
  { by eapply elem_of_list_lookup_2. }
  { word. }
  { word. }

  iNamed "Hreply".
  wp_loadField.
  simpl.
  wp_pures.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (clerks_sl) "Hclerks_sl".
  wp_pures.

  iDestruct (is_slice_to_small with "Hservers_sl") as "Hservers_sl".
  rewrite -Hservers_sz.
  iDestruct (is_slice_to_small with "Hclerks_sl") as "Hclerks_sl".
  iDestruct (is_slice_small_sz with "Hclerks_sl") as %Hclerks_sz.
  rewrite replicate_length in Hclerks_sz.
  simpl.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (i_ptr) "Hi".
  wp_pures.

  (* weaken to loop invariant *)
  iAssert (
        ∃ (i:u64) clerksComplete clerksLeft,
          "Hi" ∷ i_ptr ↦[uint64T] #i ∗
          "%HcompleteLen" ∷ ⌜length clerksComplete = int.nat i⌝ ∗
          "%Hlen" ∷ ⌜length (clerksComplete ++ clerksLeft) = length servers⌝ ∗
          "Hclerks_sl" ∷ is_slice_small clerks_sl ptrT 1 (clerksComplete ++ clerksLeft) ∗
          "Hservers_sl" ∷ is_slice_small servers_sl uint64T 1 servers ∗
          "#Hclerks_is" ∷ ([∗ list] ck ; γsrv ∈ clerksComplete ; (take (length clerksComplete) server_γs),
                              pb_definitions.is_Clerk ck γ γsrv
                              )
          )%I with "[Hclerks_sl Hservers_sl Hi]" as "HH".
  {
    iExists _, [], _.
    simpl.
    iFrame "∗#".
    iPureIntro.
    split; first word.
    apply replicate_length.
  }
  wp_forBreak_cond.

  wp_pures.
  iNamed "HH".
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.
  clear host Hlookup_conf.
  wp_if_destruct.
  { (* loop not finished *)
    wp_pures.
    wp_load.
    assert (int.nat i < length servers) as Hlookup.
    { word. }
    apply list_lookup_lt in Hlookup as [host Hlookup].
    wp_apply (wp_SliceGet with "[$Hservers_sl]").
    { done. }

    iIntros "Hserver_sl".

    iDestruct (big_sepL2_lookup_2_some with "Hhost") as %HH.
    { done. }
    destruct HH as [γsrv Hserver_γs_lookup].
    wp_apply (wp_MakeClerk with "[]").
    {
      iDestruct (big_sepL2_lookup_acc with "Hhost") as "[$ _]"; done.
    }
    iIntros (pbCk) "#HpbCk".
    wp_load.
    wp_apply (wp_SliceSet (V:=loc) with "[Hclerks_sl]").
    {
      iFrame "Hclerks_sl".
      iPureIntro.
      apply list_lookup_lt.
      word.
    }
    iIntros "Hclerks_sl".
    wp_load.
    wp_store.
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame "∗#".
    iExists _, _, _.
    iFrame "∗".
    instantiate (1:=clerksComplete ++ [pbCk]).
    iSplitR.
    {
      iPureIntro.
      rewrite app_length.
      simpl.
      word.
    }
    instantiate (2:=tail clerksLeft).
    destruct clerksLeft.
    {
      exfalso.
      rewrite app_nil_r in Hlen.
      word.
    }

    iSplitR.
    {
      iPureIntro.
      rewrite app_length.
      rewrite app_length.
      simpl.
      rewrite -Hlen.
      rewrite app_length.
      simpl.
      word.
    }
    iSplitL.
    {
      iApply to_named.
      iExactEq "Hclerks_sl".
      {
        f_equal.
        simpl.
        rewrite -HcompleteLen.
        replace (length _) with (length clerksComplete + 0) by lia.
        rewrite insert_app_r.
        simpl.
        rewrite -app_assoc.
        f_equal.
      }
    }
    rewrite app_length.
    simpl.
    iDestruct (big_sepL2_length with "Hhost") as %Hserver_len_eq.
    rewrite take_more; last first.
    { lia. }

    iApply (big_sepL2_app with "Hclerks_is []").

    replace (take 1 (drop (_) server_γs)) with ([γsrv]); last first.
    {
      apply ListSolver.list_eq_bounded.
      {
        simpl.
        rewrite take_length.
        rewrite drop_length.
        word.
      }
      intros.
      rewrite list_lookup_singleton.
      destruct i0; last first.
      {
        exfalso. simpl in *. word.
      }
      rewrite lookup_take; last first.
      { word. }
      rewrite lookup_drop.
      rewrite HcompleteLen.
      rewrite -Hserver_γs_lookup.
      f_equal.
      word.
      (* TODO: list_solver. *)
    }
    iApply big_sepL2_singleton.
    iFrame "#".
  }
  (* done with for loop *)
  iRight.
  iSplitR; first done.
  iModIntro.
  assert (int.nat i = length servers) as Hi_done.
  {
    rewrite Hclerks_sz.
    rewrite app_length in Hlen.
    word.
  }

  wp_pures.
  replace (clerksLeft) with ([] : list loc) in *; last first.
  {
    (* TODO: list_solver. pure fact *)
    enough (length clerksLeft = 0).
    {
      symmetry.
      apply nil_length_inv.
      done.
    }
    rewrite app_length in Hlen.
    word.
  }
  wp_apply (wp_NewWaitGroup_free).
  iIntros (wg) "Hwg".
  wp_pures.
  wp_apply (wp_slice_len).

  wp_apply (wp_new_slice). (* XXX: untyped *)
  { done. }
  clear err e.
  iIntros (errs_sl) "Herrs_sl".
  iDestruct (slice.is_slice_sz with "Herrs_sl") as "%Herrs_sz".
  wp_pures.
  wp_store.
  wp_pures.

  rewrite app_nil_r.
  rename clerksComplete into clerks.
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑adminN)) as "Hmask".
  { set_solver. }
  set (P:= (λ i, ∃ (err:u64) γsrv',
      ⌜server_γs !! int.nat i = Some γsrv'⌝ ∗
        readonly ((errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z i)↦[uint64T] #err) ∗
        □ if (decide (err = U64 0)) then
            pb_ghost.is_epoch_lb γsrv' epoch
          else
            True
  )%I : u64 → iProp Σ).
  iMod (free_WaitGroup_alloc adminN _ P with "Hwg") as (γwg) "Hwg".
  iMod "Hmask" as "_".
  iModIntro.

  (* iMod (readonly_alloc_1 with "Hreply_epoch") as "#Hreply_epoch". *)
  iMod (readonly_alloc_1 with "Hreply_state") as "#Hreply_state".
  iMod (readonly_alloc_1 with "Hreply_next_index") as "#Hreply_next_index".
  iDestruct "Hreply_state_sl" as "#Hreply_state_sl".

  (* weaken to loop invariant *)
  iAssert (
        ∃ (i:u64),
          "Hi" ∷ i_ptr ↦[uint64T] #i ∗
          "%Hi_ineq" ∷ ⌜int.nat i ≤ length clerks⌝ ∗
          "Herrs" ∷ (errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z i)↦∗[uint64T] (replicate (int.nat clerks_sl.(Slice.sz)- int.nat i) #0) ∗
          "Hwg" ∷ own_WaitGroup adminN wg γwg i P
          )%I with "[Herrs_sl Hi Hwg]" as "HH".
  {
    unfold is_slice.
    unfold slice.is_slice. unfold slice.is_slice_small.
    clear Hlen.
    iDestruct "Herrs_sl" as "[[Herrs_sl %Hlen] _]".
    destruct Hlen as [Hlen _].
    iExists _; iFrame.
    iSplitR; first iPureIntro.
    { word. }
    simpl.
    replace (1 * int.Z _)%Z with (0%Z) by word.
    rewrite loc_add_0.
    replace (int.nat _ - int.nat 0) with (int.nat clerks_sl.(Slice.sz)) by word.
    iFrame "Herrs_sl".
  } (* FIXME: copy/pasted from pb_apply_proof *)
  wp_forBreak_cond.

  clear i HcompleteLen Heqb0 Hi_done.
  iNamed "HH".
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.

  iDestruct (ghost_get_propose_lb with "Hprop") as "#Hprop_lb2".
  wp_if_destruct.
  { (* loop continues *)
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    wp_load.

    assert (int.nat i < int.nat clerks_sl.(Slice.sz)) as Hlookup by word.
    rewrite -Hclerks_sz in Hlookup.
    rewrite app_nil_r in Hlen.
    rewrite -Hlen in Hlookup.
    apply list_lookup_lt in Hlookup as [pbCk Hlookup].
    wp_apply (wp_SliceGet with "[$Hclerks_sl]").
    { done. }
    iIntros "Hclerks_sl".

    wp_pures.

    replace (int.nat clerks_sl.(Slice.sz) - int.nat i) with (S (int.nat clerks_sl.(Slice.sz) - (int.nat (word.add i 1)))) by word.
    rewrite replicate_S.
    iDestruct (array_cons with "Herrs") as "[Herr_ptr Herr_ptrs]".
    wp_load.
    wp_pures.

    iDestruct (own_WaitGroup_to_is_WaitGroup with "[Hwg]") as "#His_wg".
    { by iExactEq "Hwg". }
    wp_apply (wp_fork with "[Hwg_tok Herr_ptr]").
    {
      iNext.
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_allocStruct).
      { repeat econstructor. done. }
      iIntros (args_ptr) "Hargs".
      iDestruct (struct_fields_split with "Hargs") as "HH".
      iNamed "HH".

      iDestruct (big_sepL2_lookup_1_some with "Hclerks_is") as %[γsrv Hlookup2].
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hclerks_is") as "[HH _]".
      { done. }
      { done. }
      wp_apply (wp_Clerk__SetState with "[Epoch NextIndex State]").
      {
        iFrame "∗#".
        iSplitR.
        {
          iPureIntro.
          done.
        }
        iSplitR.
        {
          iPureIntro.
          done.
        }
        iExists _.
        iFrame "∗#".
      }
      iIntros (err) "#Hpost".

      unfold SliceSet.
      unfold slice.ptr.
      wp_pures.
      wp_store.

      iMod (readonly_alloc_1 with "Herr_ptr") as "#Herr_ptr".
      wp_apply (wp_WaitGroup__Done with "[$Hwg_tok $His_wg]").
      {
        rewrite lookup_take_Some in Hlookup2.
        destruct Hlookup2 as [Hlookup2 _].
        iModIntro.
        unfold P.
        iExists _, _.
        iSplitL; first done.
        iFrame "#".
      }
      done.
    }
    wp_pures.
    wp_load.
    wp_store.

    (* re-establish loop invariant *)
    iModIntro.
    iLeft.
    iSplitR; first done.
    iFrame "∗".
    iExists _.
    iFrame "∗#".
    iSplitR.
    { iPureIntro. word. }
    iApply to_named.
    iExactEq "Herr_ptrs".
    f_equal.
    rewrite loc_add_assoc.
    f_equal.
    simpl.
    replace (int.Z (word.add i 1%Z)) with (int.Z i + 1)%Z by word.
    word.
  }
  (* loop completed *)
  iModIntro.
  iRight.
  iSplitR; first done.

  wp_pures.
  wp_apply (wp_WaitGroup__Wait with "[$Hwg]").
  iIntros "#Hwg_post".
  wp_pures.
  replace (int.nat i) with (length clerks); last first.
  {
    rewrite app_nil_r in Hlen.
    word.
  }

  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (err_ptr) "Herr".
  wp_pures.
  wp_store.
  wp_pures.

  (* FIXME: *)
  (* This was copy/pasted and modified from apply_proof *)
  iAssert (∃ (i err:u64),
              "Hj" ∷ i_ptr ↦[uint64T] #i ∗
              "%Hj_ub" ∷ ⌜int.nat i ≤ length clerks⌝ ∗
              "Herr" ∷ err_ptr ↦[uint64T] #err ∗
              "#Hrest" ∷ □ if (decide (err = (U64 0)%Z)) then
                (∀ (k:u64) γsrv, ⌜int.nat k < int.nat i⌝ -∗ ⌜server_γs !! (int.nat k) = Some γsrv⌝ -∗ pb_ghost.is_epoch_lb γsrv epoch)
              else
                True
          )%I with "[Hi Herr]" as "Hloop".
  {
    iExists _, _.
    iFrame "∗".
    iSplitL.
    { iPureIntro. word. }
    iModIntro.
    destruct (decide (_)); last first.
    { done. }
    iIntros.
    exfalso. replace (int.nat 0%Z) with 0 in H by word.
    word.
  }

  iClear "Herrs".
  wp_forBreak_cond.
  iNamed "Hloop".
  wp_pures.
  wp_load.
  wp_apply (wp_slice_len).

  rewrite replicate_length in Herrs_sz.
  rewrite -Hclerks_sz in Herrs_sz.
  rewrite app_nil_r in Hlen.

  clear i Hi_ineq Heqb0.
  wp_if_destruct.
  { (* one loop iteration *)
    wp_pures.
    wp_load.
    unfold SliceGet.
    wp_call.
    iDestruct (big_sepS_elem_of_acc _ _ i0 with "Hwg_post") as "[HH _]".
    { set_solver. }

    assert (int.nat i0 < int.nat errs_sl.(Slice.sz)) by word.

    iDestruct "HH" as "[%Hbad|HH]".
    { exfalso.
      rewrite -Herrs_sz in H.
      word.
    }
    iDestruct "HH" as (??) "(%HbackupLookup & Herr2 & Hpost)".
    wp_apply (wp_slice_ptr).
    wp_pure1.
    iEval (simpl) in "Herr2".
    iMod (readonly_load with "Herr2") as (?) "Herr3".
    wp_load.
    wp_pures.
    destruct (bool_decide (_)) as [] eqn:Herr; wp_pures.
    {
      rewrite bool_decide_eq_true in Herr.
      replace (err0) with (U64 0%Z) by naive_solver.
      wp_pures.
      wp_load; wp_store.
      iLeft.
      iModIntro.
      iSplitL ""; first done.
      iFrame "∗".
      iExists _, _.
      iFrame "Hj Herr".
      iSplitL "".
      { iPureIntro. word. }
      iModIntro.
      destruct (decide (err = 0%Z)).
      {
        iIntros.
        assert (int.nat k < int.nat i0 ∨ int.nat k = int.nat i0) as [|].
        {
          replace (int.nat (word.add i0 1%Z)) with (int.nat i0 + 1) in * by word.
          word.
        }
        {
          by iApply "Hrest".
        }
        {
          destruct (decide (_)); last by exfalso.
          replace (γsrv') with (γsrv); last first.
          {
            replace (int.nat i0) with (int.nat k) in * by word.
            naive_solver.
          }
          iDestruct "Hpost" as "#$".
        }
      }
      {
        done.
      }
    }
    {
      wp_store.
      wp_pures.
      wp_load; wp_store.
      iLeft.
      iModIntro.
      iSplitL ""; first done.
      iFrame "∗".
      iExists _, _.
      iFrame "Hj Herr".
      destruct (decide (err0 = _)).
      { exfalso. naive_solver. }
      iPureIntro.
      split; last done.
      word.
    }
  }
  iRight.
  iModIntro.
  iSplitL ""; first done.
  wp_pures.
  wp_load.
  wp_pures.
  (* FIXME: *)
  (* End copy/paste from apply_proof *)

  wp_if_destruct.
  { (* got some error *)
    wp_load.
    iApply "HΦ".
    done.
  }

  (* no errors *)
  replace (int.nat i0) with (length clerks); last first.
  { word. }

  destruct (decide (_)); last first.
  { exfalso. done. }

  iMod (own_update with "Hconf_unset") as "Hconf_prop".
  {
    apply singleton_update.
    apply cmra_update_exclusive.
    instantiate (1:=(to_dfrac_agree (DfracOwn 1) ((Some server_γs) : (leibnizO _)))).
    done.
  }
  iMod (own_update with "Hconf_prop") as "Hconf_prop".
  {
    apply singleton_update.
    apply dfrac_agree_persist.
  }
  iDestruct "Hconf_prop" as "#Hconf_prop".

  wp_bind (Clerk__WriteConfig _ _ _).
  iApply (wp_frame_wand with "[HΦ Hconf_sl Hprop Hclerks_sl]").
  { iNamedAccu. }
  iDestruct (big_sepL2_length with "Hhost") as %Hserver_len_eq.

  assert (length servers > 0) as Hserver_nz.
  {
    assert (length servers ≠ 0 ∨ length servers = 0) as [|Hbad] by word.
    { word. }
    {
      exfalso.
      rewrite Hbad in Hservers_sz.
      apply u64_nat_0 in Hservers_sz.
      rewrite Hservers_sz in Heqb.
      done.
    }
  }

  wp_apply (wp_Clerk__WriteConfig2 with "Hck Hservers_sl [$Hconf_prop] Hhost").
  {
    iPureIntro.
    word.
  }
  {
    iIntros (?) "%Hlookup".
    apply elem_of_list_lookup_1 in Hlookup as [i Hlookup].
    iDestruct (big_sepS_elem_of_acc _ _ (U64 i) with "Hwg_post") as "[HH _]".
    { set_solver. }

    assert (i < length server_γs).
    {
      apply lookup_lt_is_Some_1.
      eexists. done.
    }
    replace (length clerks) with (length server_γs) in * by word.
    assert (int.nat i = i) as Hi.
    { word. }

    iDestruct "HH" as "[%Hbad|HP]".
    {
      exfalso.
      word.
    }
    unfold P.
    iDestruct "HP" as (??) "(%Hlookup2 & _ & Hpost)".
    replace (γsrv') with (γsrv); last first.
    {
      rewrite Hi in Hlookup2.
      rewrite Hlookup in Hlookup2.
      by inversion Hlookup2.
    }
    iSpecialize ("Hrest" $! i γsrv with "[%] [%]").
    { word. }
    { rewrite Hi. done. }
    iFrame "Hrest".
  }
  iModIntro.
  iIntros (err) "Hpost Hservers_sl".
  iNamed 1.

  wp_pures.
  wp_if_destruct.
  { (* WriteConfig failed *)
    iApply "HΦ". done.
  }
  (* WriteConfig succeeded *)
  destruct (decide (_)); last first.
  { exfalso. done. }
  iDestruct "Hpost" as "#Hconf".
  wp_apply (wp_allocStruct).
  { eauto. }
  clear args.
  iIntros (args) "Hargs".
  assert (0 < length clerks) as Hclerk_lookup.
  {
    word.
  }
  apply list_lookup_lt in Hclerk_lookup as [primaryCk Hclerk_lookup].

  wp_apply (wp_SliceGet with "[$Hclerks_sl]").
  { done. }
  iIntros "Hclerks_sl".
  wp_pures.

  iDestruct (big_sepL2_lookup_1_some with "Hclerks_is") as %[γsrv Hlookup2].
  { done. }
  iDestruct (big_sepL2_lookup_acc with "Hclerks_is") as "[HprimaryCk _]".
  { done. }
  { done. }

  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".

  (* Get a list of γs just for backups *)
  destruct (server_γs).
  {
    exfalso.
    rewrite lookup_take /= in Hlookup2; last first.
    { word. }
    done.
  }
  replace (p) with (γsrv) in *; last first.
  {
    rewrite lookup_take /= in Hlookup2; last first.
    { word. }
    naive_solver.
  }
  iAssert (|={⊤}=> become_primary_escrow γ γsrv epoch σ)%I with "[Hprop]" as ">#Hprimary_escrow".
  {
    iMod (inv_alloc with "[Hprop]") as "$".
    {
      iNext.
      iLeft.
      iFrame "Hprop Hprop_facts2 Hinit".
    }
    done.
  }

  wp_apply (wp_Clerk__BecomePrimary with "[$HprimaryCk Hconf Hhost Epoch Replicas Hservers_sl]").
  {

    iFrame.
    instantiate (1:=(pb_marshal_proof.BecomePrimaryArgs.mkC _ _)).
    simpl.
    iFrame "#".
    iSplitR.
    {
      iDestruct ("Hrest" with "[%] [%]") as "H".
      { instantiate (1:=0). word. }
      { rewrite lookup_take in Hlookup2.
        { done. }
        word.
      }
      iFrame "H".
    }
    iSplitR.
    {
      iApply big_sepL2_forall.
      instantiate (1:=servers).
      iSplitL; first done.
      iIntros.
      iDestruct (big_sepL2_lookup_acc with "Hhost") as "[$ HH]".
      { done. }
      { done. }
      iApply "Hrest"; last first.
      {
        iPureIntro.
        instantiate (1:=k).
        replace (int.nat k) with (k).
        { done. }
        assert (k < length servers).
        { apply lookup_lt_Some in H. done. }
        word.
      }
      { iPureIntro.
        apply lookup_lt_Some in H.
        replace (int.nat k) with (k).
        { rewrite Hlen. done. }
        assert (k < length servers). (* FIXME: why do I have to assert this when it's already in context? *)
        { done. }
        word.
      }
    }
    {
      iExists _.
      iFrame.
    }
  }
  iIntros.
  wp_pures.
  iApply "HΦ".
  done.
Qed.

End admin_proof.
