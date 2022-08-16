From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export admin.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions config_proof.

Section admin_proof.

Context {pb_record:PBRecord}.
Notation pbG := (pbG (pb_record:=pb_record)).
Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).

Notation wp_Clerk__GetState := (wp_Clerk__GetState (pb_record:=pb_record)).
Notation wp_Clerk__SetState := (wp_Clerk__SetState (pb_record:=pb_record)).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.
Context `{!configG Σ}.

Definition adminN := nroot .@ "admin".

Definition is_conf_inv γpb γconf : iProp Σ :=
  inv adminN (∃ epoch conf (confγs:list pb_server_names) epoch_lb,
      "Hepoch" ∷ own_epoch γconf epoch ∗
      "Hconf" ∷ own_config γconf conf ∗
      "#His_conf" ∷ is_epoch_config γpb epoch_lb confγs ∗
      "#His_hosts" ∷ ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host γpb γsrv host) ∗
      "#His_lbs" ∷ (∀ γsrv, ⌜γsrv ∈ confγs⌝ → pb_ghost.is_epoch_lb γsrv epoch_lb) ∗
      "Hunused" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch < int.nat epoch'⌝ → config_unset γpb epoch' ∗ config_unset γpb epoch' ∗ own_proposal γpb epoch' []) ∗
      "Hunset" ∷ config_unset γpb epoch ∗
      "#His_skip" ∷ (∀ epoch_skip, ⌜int.nat epoch_skip < int.nat epoch⌝ → ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → is_epoch_skipped γpb epoch_skip)
      )
.

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
  wp_apply (wp_MakeClerk with "[$Hhost]").
  iIntros.
  iApply "HΦ".
  iExists  _; iFrame "#".
Qed.

Lemma wp_Clerk__GetEpochAndConfig2 ck γpb Φ :
  is_Clerk2 ck γpb -∗
  □(∀ (epoch epoch_lb:u64) confγs (conf:list u64) config_sl,
  (is_slice config_sl uint64T 1 conf ∗
  config_unset γpb epoch ∗
  own_proposal γpb epoch [] ∗
  is_epoch_config γpb epoch_lb confγs ∗
  (∀ epoch_skip, ⌜int.nat epoch_skip < int.nat epoch⌝ → ⌜int.nat epoch_lb < int.nat epoch_skip⌝ → is_epoch_skipped γpb epoch_skip) ∗
  ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host γpb γsrv host) ∗
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
  iMod (own_update with "Hunset") as "Hskip1".
  {
    apply singleton_update.
    apply dfrac_agree_persist.
  }
  iDestruct "Hskip1" as "#Hskip1".
  iSpecialize ("Hunset_new" with "[]").
  { done. }
  iDestruct "Hunset_new" as "(Hunset_new & Hunset_new2 & Hprop)".

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
Qed.


Lemma wp_Reconfig γ (configHost:u64) (servers:list u64) (servers_sl:Slice.t) server_γs :
  {{{
        "Hservers_sl" ∷ is_slice servers_sl uint64T 1 servers ∗
        "#Hhost" ∷ ([∗ list] host ; γsrv ∈ servers ; server_γs, is_pb_host γ γsrv host) ∗
        "#Hconf_host" ∷ is_conf_host configHost γ
  }}}
    EnterNewConfig #configHost (slice_val servers_sl)
  {{{
        (err:u64), RET #err; True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
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

  assert (length conf ≠ 0) by admit. (* FIXME: *)
  iDestruct "Hpost1" as "(Hconf_sl & Hconf_unset & Hprop & #His_conf & #Hskip & #His_hosts & #Hlb)".
  iDestruct (is_slice_to_small with "Hconf_sl") as "Hconf_sl".
  iDestruct (is_slice_small_sz with "Hconf_sl") as %Hconf_len.
  set (oldNodeId:=word.modu randId config_sl.(Slice.sz)).
  assert (int.nat oldNodeId < length conf) as Hlookup_conf.
  { rewrite Hconf_len.
    unfold oldNodeId.
    admit. (* FIXME: word *)
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
  wp_apply (pb_definitions.wp_MakeClerk with "[]").
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
  iDestruct "Hpost" as (???) "(%Hepoch_ineq & #Hacc_ro & #Hprop_facts & Hreply & %Henc)".
  iNamed "Hreply".
  wp_loadField.
  simpl.
  wp_pures.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (clerks_sl) "Hclerks_sl".
  wp_pures.

  iDestruct (is_slice_to_small with "Hservers_sl") as "Hservers_sl".
  iDestruct (is_slice_small_sz with "Hservers_sl") as %Hservers_sz.
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

    iDestruct (big_sepL2_lookup_1_some with "Hhost") as %HH.
    { done. }
    destruct HH as [γsrv Hserver_γs_lookup].
    wp_apply (pb_definitions.wp_MakeClerk with "[]").
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
    assert (length server_γs = length servers) by admit. (* FIXME: pure fact *)
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
        exfalso. simpl in H1. word.
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
    admit. (* TODO: list_solver. pure fact *)
  }
  wp_apply (wp_NewWaitGroup_free).
  iIntros (wg) "Hwg".
  wp_pures.
  wp_apply (wp_slice_len).

  wp_apply (wp_new_slice). (* XXX: untyped *)
  { done. }
  clear err e.
  iIntros (errs_sl) "Herrs_sl".
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
            is_accepted_lb γsrv' epoch0 σ
          else
            True
  )%I : u64 → iProp Σ).
  iMod (free_WaitGroup_alloc adminN _ P with "Hwg") as (γwg) "Hwg".
  iMod "Hmask" as "_".
  iModIntro.

  iMod (readonly_alloc_1 with "Hreply_epoch") as "#Hreply_epoch".
  iMod (readonly_alloc_1 with "Hreply_state") as "#Hreply_state".
  iMod (readonly_alloc_1 with "Hreply_next_index") as "#Hreply_next_index".
  iMod (readonly_alloc_1 with "Hreply_state_sl") as "#Hreply_state_sl".

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
    iExactEq "Hwg". done.
  } (* FIXME: copy/pasted from pb_apply_proof *)
  wp_forBreak_cond.

  clear i HcompleteLen Heqb Hi_done.
  iNamed "HH".
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.

  (* FIXME: need to know that epoch_lb is the epoch number for which we get a
     response from the old server *)
  (* iMod (ghost_become_leader with "[] Hprop_facts His_conf Hacc_ro [Hskip] Hprop") as "[Hprop #Hprop_facts]". *)

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
      wp_apply (wp_Clerk__SetState with "[Epoch NextIndex State]").
      {
        iFrame "∗#".
      }
    }
  }



End admin_proof.
