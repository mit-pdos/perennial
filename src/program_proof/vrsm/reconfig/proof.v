From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export reconfig.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.vrsm.replica Require Import
     config_protocol_proof getstate_proof
     setstate_proof makeclerk_proof becomeprimary_proof.

Section admin_proof.

Context {params:pbParams.t}.
Import pbParams.
Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!heapGS Σ}.
Context `{!pbG Σ}.
Context `{!waitgroupG Σ}.

Definition adminN := nroot .@ "admin".

Lemma wp_Reconfig γ configHosts_sl (configHosts:list u64) (servers:list u64) (servers_sl:Slice.t) server_γs :
  {{{
        "Hservers_sl" ∷ own_slice servers_sl uint64T (DfracOwn 1) servers ∗
        "#HconfHost_sl" ∷ readonly (own_slice_small configHosts_sl uint64T (DfracOwn 1) configHosts) ∗
        "#Hhost" ∷ ([∗ list] γsrv ; host ∈ server_γs ; servers, is_pb_host host γ γsrv) ∗
        "#Hconf_host" ∷ is_pb_config_hosts configHosts γ
  }}}
    EnterNewConfig (slice_val configHosts_sl) (slice_val servers_sl)
  {{{
        (err:u64), RET #err; True
  }}}.
Proof using waitgroupG0.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.

  wp_apply (wp_slice_len).
  wp_pures.
  iDestruct (own_slice_sz with "Hservers_sl") as %Hservers_sz.
  wp_if_destruct.
  {
    by iApply "HΦ".
  }

  wp_apply (wp_MakeClerk2 with "[Hconf_host]").
  { iFrame "#". }
  iIntros (ck γconf) "#Hck".
  wp_pures.
  wp_bind (Clerk__ReserveEpochAndGetConfig _).
  iApply (wp_frame_wand with "[HΦ Hservers_sl]").
  { iNamedAccu. }
  wp_apply (wp_Clerk_ReserveEpochAndGetConfig2 with "[$Hck]").
  iModIntro.
  iIntros (?????) "Hpost1".
  iNamed 1.
  wp_pures.
  wp_apply wp_RandomUint64.
  iIntros (rnd) "_".
  wp_pures.
  set (s:=(word.add rnd (W64 1))).
  generalize s as randId.
  clear s.
  intros randId.
  wp_apply (wp_slice_len).
  wp_pures.

  iDestruct "Hpost1" as "(Hconf_sl & #Hres & Hconf_unset & Hprop & Hinit & #His_conf & #Hskip & #His_hosts & #Hlb)".

  iAssert (⌜length conf ≠ 0⌝)%I as %Hold_conf_ne.
  {
    iDestruct "His_conf" as "(_ & _ & %Hconfγ_nz)".
    iDestruct (big_sepL2_length with "His_hosts") as %Heq.
    iPureIntro.
    rewrite fmap_length in Hconfγ_nz.
    word.
  }
  iMod (readonly_load with "Hconf_sl") as (?) "Hconf_sl2".
  iDestruct (own_slice_small_sz with "Hconf_sl2") as %Hconf_len.
  set (oldNodeId:=word.modu randId config_sl.(Slice.sz)).
  assert (uint.nat oldNodeId < length conf) as Hlookup_conf.
  { rewrite Hconf_len.
    unfold oldNodeId.
    enough (uint.Z randId `mod` uint.Z config_sl.(Slice.sz) < uint.Z config_sl.(Slice.sz))%Z.
    { word. }
    apply Z.mod_pos_bound.
    word.
  }
  apply lookup_lt_is_Some_2 in Hlookup_conf as [host Hlookup_conf].
  wp_apply (wp_SliceGet with "[$Hconf_sl2]").
  { done. }
  iIntros "Hconf_sl".
  simpl.
  (* FIXME: how does wp_MakeClerk work here? *)
  iDestruct (big_sepL2_lookup_2_some with "His_hosts") as %HH.
  { done. }
  destruct HH as [γsrv_old Hconfγ_lookup].
  iRename "His_hosts" into "His_hosts_full".
  iAssert ([∗ list] γsrv;host0 ∈ confγs;conf, is_pb_rpcs host0 γ γsrv)%I with "[]" as "#His_hosts".
  {
    iApply (big_sepL2_impl with "[$]").
    iIntros "!# * % % H".
    iClear "Hhost".
    iNamed "H". iFrame "#".
  }
  wp_apply (makeclerk_proof.wp_MakeClerk with "[]").
  {
    iDestruct (big_sepL2_lookup_acc with "His_hosts") as "[HisHost _]".
    { done. }
    { done. }
    iDestruct "HisHost" as "HisHost".
    iFrame "#".
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
    rewrite list_lookup_fmap.
    by setoid_rewrite Hconfγ_lookup.
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
  iDestruct "Hpost" as (????) "(%Hepoch_lb_ineq & %Hepoch_ub_ineq & #Hacc_ro & #Hprop_facts & #Hprim_facts & #Hprop_lb & #HcommitFacts & Hreply & %Henc & %Hlen_no_overflow)".
  destruct (decide (uint.nat epochacc = uint.nat epoch)) as [Heq|Hepochacc_ne_epoch].
  {
    replace (epochacc) with (epoch) by word.
    iExFalso.
    iApply (own_unused_facts_false with "[$] [$]").
  }
  iMod (ghost_init_primary with "Hprop_lb Hprop_facts His_conf Hacc_ro Hskip Hprop") as "Hprim".
  {
    apply elem_of_list_fmap_1.
    by eapply elem_of_list_lookup_2. }
  { word. }
  { word. }
  iClear "Hprim_facts".
  iMod (primary_ghost_init_primary with "Hinit") as "[#Hinit #Hprim_facts]".
  (*
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iClear "Hprim_facts".
  iDestruct (ghost_get_propose_lb with "Hprop") as "#Hprop_lb2".
  iMod (primary_ghost_init_primary (own_primary_ghost γ.(s_pb) epoch opsfull)
         with "Hinit [Hprop]") as "#[Hescrow Hprim_facts]".
  { iFrame "∗#". }
  iMod "Hmask". iModIntro. *)

  iNamed "Hreply".
  wp_loadField.
  simpl.
  wp_pures.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (clerks_sl) "Hclerks_sl".
  wp_pures.

  iDestruct (own_slice_to_small with "Hservers_sl") as "Hservers_sl".
  rewrite -Hservers_sz.
  iDestruct (own_slice_to_small with "Hclerks_sl") as "Hclerks_sl".
  iDestruct (own_slice_small_sz with "Hclerks_sl") as %Hclerks_sz.
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
          "%HcompleteLen" ∷ ⌜length clerksComplete = uint.nat i⌝ ∗
          "%Hlen" ∷ ⌜length (clerksComplete ++ clerksLeft) = length servers⌝ ∗
          "Hclerks_sl" ∷ own_slice_small clerks_sl ptrT (DfracOwn 1) (clerksComplete ++ clerksLeft) ∗
          "Hservers_sl" ∷ own_slice_small servers_sl uint64T (DfracOwn 1) servers ∗
          "#Hclerks_is" ∷ ([∗ list] ck ; γsrv ∈ clerksComplete ; (take (length clerksComplete) server_γs),
                              is_Clerk ck γ γsrv
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
    assert (uint.nat i < length servers) as Hlookup.
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
      iDestruct (big_sepL2_lookup_acc with "Hhost") as "[H _]".
      3:{ iClear "Hhost". iNamed "H". iFrame "#". }
      all: done.
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
    iFrame "∗".
    iExists (clerksComplete ++ [pbCk]), (tail clerksLeft).
    iSplitR.
    {
      iPureIntro.
      rewrite app_length.
      simpl.
      word.
    }
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
  assert (uint.nat i = length servers) as Hi_done.
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
  iDestruct (slice.own_slice_sz with "Herrs_sl") as "%Herrs_sz".
  wp_pures.
  wp_store.
  wp_pures.

  rewrite app_nil_r.
  rename clerksComplete into clerks.
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑adminN)) as "Hmask".
  { set_solver. }
  set (P:= (λ i, ∃ (err:u64) γsrv',
      ⌜server_γs !! uint.nat i = Some γsrv'⌝ ∗
        readonly ((errs_sl.(Slice.ptr) +ₗ[uint64T] uint.Z i)↦[uint64T] #err) ∗
        □ if (decide (err = W64 0)) then
            protocol.is_epoch_lb γsrv'.(r_pb) epoch
          else
            True
  )%I : u64 → iProp Σ).
  iMod (free_WaitGroup_alloc adminN _ P with "Hwg") as (γwg) "Hwg".
  iMod "Hmask" as "_".
  iModIntro.

  (* iMod (readonly_alloc_1 with "Hreply_epoch") as "#Hreply_epoch". *)
  iMod (readonly_alloc_1 with "Hreply_state") as "#Hreply_state".
  iMod (readonly_alloc_1 with "Hreply_next_index") as "#Hreply_next_index".
  iMod (readonly_alloc_1 with "Hreply_committed_next_index") as "#Hreply_committed_next_index".
  iDestruct "Hreply_state_sl" as "#Hreply_state_sl".

  (* weaken to loop invariant *)
  iAssert (
        ∃ (i:u64),
          "Hi" ∷ i_ptr ↦[uint64T] #i ∗
          "%Hi_ineq" ∷ ⌜uint.nat i ≤ length clerks⌝ ∗
          "Herrs" ∷ (errs_sl.(Slice.ptr) +ₗ[uint64T] uint.Z i)↦∗[uint64T] (replicate (uint.nat clerks_sl.(Slice.sz)- uint.nat i) #0) ∗
          "Hwg" ∷ own_WaitGroup adminN wg γwg i P
          )%I with "[Herrs_sl Hi Hwg]" as "HH".
  {
    unfold own_slice.
    unfold slice.own_slice. unfold slice.own_slice_small.
    clear Hlen.
    iDestruct "Herrs_sl" as "[[Herrs_sl %Hlen] _]".
    destruct Hlen as [Hlen _].
    iExists _; iFrame.
    iSplitR; first iPureIntro.
    { word. }
    simpl.
    replace (1 * uint.Z _)%Z with (0%Z) by word.
    rewrite loc_add_0.
    replace (uint.nat _ - uint.nat 0) with (uint.nat clerks_sl.(Slice.sz)) by word.
    iFrame "Herrs_sl".
  } (* FIXME: copy/pasted from pb_apply_proof *)

  iMod (own_update with "Hconf_unset") as "Hconf_prop".
  {
    apply singleton_update.
    apply cmra_update_exclusive.
    instantiate (1:=(to_dfrac_agree (DfracOwn 1) ((Some (r_pb <$> server_γs)) : (leibnizO _)))).
    done.
  }
  iMod (own_update with "Hconf_prop") as "Hconf_prop".
  {
    apply singleton_update.
    apply dfrac_agree_persist.
  }
  iDestruct "Hconf_prop" as "#Hconf_prop".

  (* FIXME: have a lemma for this kind of loop that makes use of big_sepL's and big_sepL2's. *)
  wp_forBreak_cond.

  clear i HcompleteLen Heqb0 Hi_done.
  iNamed "HH".
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.

  wp_if_destruct.
  { (* loop continues *)
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    wp_load.

    assert (uint.nat i < uint.nat clerks_sl.(Slice.sz)) as Hlookup by word.
    rewrite -Hclerks_sz in Hlookup.
    rewrite app_nil_r in Hlen.
    rewrite -Hlen in Hlookup.
    apply list_lookup_lt in Hlookup as [pbCk Hlookup].
    wp_apply (wp_SliceGet with "[$Hclerks_sl]").
    { done. }
    iIntros "Hclerks_sl".

    wp_pures.

    replace (uint.nat clerks_sl.(Slice.sz) - uint.nat i) with (S (uint.nat clerks_sl.(Slice.sz) - (uint.nat (word.add i 1)))) by word.
    rewrite replicate_S.
    iDestruct (array_cons with "Herrs") as "[Herr_ptr Herr_ptrs]".
    wp_load.
    wp_pures.

    iDestruct (own_WaitGroup_to_is_WaitGroup with "[Hwg]") as "#His_wg".
    { by iExactEq "Hwg". }
    iDestruct (ghost_get_propose_lb_facts with "Hprim") as "#[? ?]".
    wp_apply (wp_fork with "[Hwg_tok Herr_ptr]").
    {
      iNext.
      wp_pures.
      wp_loadField.
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
      wp_apply (wp_Clerk__SetState with "[Epoch NextIndex CommittedNextIndex State]").
      {
        iFrame "HcommitFacts HH # ∗".
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
        iSplitR.
        {
          iPureIntro; split.
          { rewrite fmap_length //. destruct server_γs.
            { exfalso. rewrite take_nil /= // in Hlookup2. }
            simpl. lia.
          }
          {
            eapply elem_of_list_lookup_2.
            rewrite list_lookup_fmap.
            rewrite lookup_take_Some in Hlookup2.
            destruct Hlookup2 as [-> _].
            done.
          }
        }
        iPureIntro. word.
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
    iSplitR.
    { iPureIntro. word. }
    iApply to_named.
    iExactEq "Herr_ptrs".
    f_equal.
    rewrite loc_add_assoc.
    f_equal.
    simpl.
    replace (uint.Z (word.add i 1%Z)) with (uint.Z i + 1)%Z by word.
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
  replace (uint.nat i) with (length clerks); last first.
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
              "%Hj_ub" ∷ ⌜uint.nat i ≤ length clerks⌝ ∗
              "Herr" ∷ err_ptr ↦[uint64T] #err ∗
              "#Hrest" ∷ □ if (decide (err = (W64 0)%Z)) then
                (∀ (k:u64) γsrv, ⌜uint.nat k < uint.nat i⌝ -∗ ⌜server_γs !! (uint.nat k) = Some γsrv⌝ -∗ protocol.is_epoch_lb γsrv.(r_pb) epoch)
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
    exfalso. replace (uint.nat 0%Z) with 0 in H by word.
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

    assert (uint.nat i0 < uint.nat errs_sl.(Slice.sz)) by word.

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
      replace (err0) with (W64 0%Z) by naive_solver.
      wp_pures.
      wp_load; wp_store.
      iLeft.
      iModIntro.
      iSplitL ""; first done.
      iFrame "∗".
      iSplitL "".
      { iPureIntro. word. }
      iModIntro.
      destruct (decide (err = 0%Z)).
      {
        iIntros.
        assert (uint.nat k < uint.nat i0 ∨ uint.nat k = uint.nat i0) as [|].
        {
          replace (uint.nat (word.add i0 1%Z)) with (uint.nat i0 + 1) in * by word.
          word.
        }
        {
          by iApply "Hrest".
        }
        {
          destruct (decide (_)); last by exfalso.
          replace (γsrv') with (γsrv); last first.
          {
            replace (uint.nat i0) with (uint.nat k) in * by word.
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
  replace (uint.nat i0) with (length clerks); last first.
  { word. }

  destruct (decide (_)); last first.
  { exfalso. done. }

  wp_bind (Clerk__TryWriteConfig _ _ _).
  iApply (wp_frame_wand with "[HΦ Hconf_sl Hclerks_sl Hprim]").
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

  iMod (readonly_alloc_1 with "Hservers_sl") as "#Hservers_sl".
  wp_apply (wp_Clerk__WriteConfig2 with "Hck Hservers_sl [$Hconf_prop] Hres Hhost").
  {
    iPureIntro.
    rewrite fmap_length.
    (* FIXME: why manually rewrite instead of `word`? *)
    rewrite Hserver_len_eq.
    word.
  }
  {
    iIntros (?) "%Hlookup".
    apply elem_of_list_lookup_1 in Hlookup as [i Hlookup].
    iDestruct (big_sepS_elem_of_acc _ _ (W64 i) with "Hwg_post") as "[HH _]".
    { set_solver. }

    assert (i < length server_γs).
    {
      erewrite <- fmap_length.
      apply lookup_lt_is_Some_1.
      eexists. done.
    }
    replace (length clerks) with (length server_γs) in * by word.
    assert (uint.nat i = i) as Hi.
    { word. }

    iDestruct "HH" as "[%Hbad|HP]".
    {
      exfalso.
      word.
    }
    unfold P.
    iDestruct "HP" as (??) "(%Hlookup2 & _ & Hpost)".
    assert (γsrv = γsrv'.(r_pb)).
    {
      rewrite Hi in Hlookup2.
      rewrite list_lookup_fmap in Hlookup.
      rewrite Hlookup2 in Hlookup.
      by inversion Hlookup.
    }
    subst.
    iSpecialize ("Hrest" $! i γsrv' with "[%] [%]").
    { rewrite Hi. done. }
    { done. }
    iFrame "Hrest".
  }
  iModIntro.
  iIntros (err) "Hpost".
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
  replace (r) with (γsrv) in *; last first.
  {
    rewrite lookup_take /= in Hlookup2; last first.
    { word. }
    naive_solver.
  }

  (* set up escrow for primary *)

  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iMod (primary_ghost_init_primary_escrow (own_primary_ghost γ.(s_pb) epoch opsfull)
         with "Hinit Hprim") as "#Hescrow".
  iMod "Hmask". iModIntro.

  wp_apply (wp_Clerk__BecomePrimary with "[$HprimaryCk Hconf Hhost Epoch Replicas Hservers_sl]").
  {

    iFrame.
    instantiate (1:=(marshal_proof.BecomePrimaryArgs.mkC _ _)).
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
      iSplitL; first done.
      iIntros.
      iDestruct (big_sepL2_lookup_acc with "Hhost") as "[H _]".
      1-2: done.
      iClear "Hhost".
      iNamed "H". iFrame "#".
      iApply "Hrest"; last first.
      {
        iPureIntro.
        instantiate (1:=k).
        replace (uint.nat k) with (k).
        { done. }
        assert (k < length servers).
        { apply lookup_lt_Some in H. done. }
        word.
      }
      { iPureIntro.
        apply lookup_lt_Some in H.
        replace (uint.nat k) with (k).
        { rewrite Hlen. done. }
        assert (k < length servers). (* FIXME: why do I have to assert this when it's already in context? *)
        { done. }
        word.
      }
    }
    {
      iFrame.
    }
  }
  iIntros.
  wp_pures.
  iApply "HΦ".
  done.
Qed.

End admin_proof.
