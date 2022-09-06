From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof.simplepb Require Import pb_definitions.

Section pb_apply_proof.

Context `{!heapGS Σ, !stagedG Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Opaque crash_borrow.
(* FIXME: this should be in a separate file *)
Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv (epoch index:u64) σ op_bytes ghost_op (op:list u8) op_sl :
  is_Server s γ γsrv -∗
  {{{
        "%Hhas_encoding" ∷ ⌜has_op_encoding op_bytes ghost_op.1⌝ ∗
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some ghost_op⌝ ∗
        "%Hσ_index" ∷ ⌜length σ = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op_bytes)
  }}}
    pb.Server__ApplyAsBackup #s #args_ptr
  {{{
        (err:u64), RET #err;
        if (decide (err = 0)) then
          is_accepted_lb γsrv epoch σ
        else
          True
  }}}
.
Proof.
  iIntros "#HisSrv" (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_bind (Server__isEpochStale _ _).
  wp_apply (wp_Server__isEpochStale with "[$Hepoch HisSm $HepochLb Hstate]").
  {
    iNamed "HisSm". iFrame "HaccP Hstate".
  }
  iIntros "(%Hineq & [Hepoch Hstate])".
  wp_if_destruct.
  { (* return error: stale *)
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hstate Hepoch HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }
  replace (epoch0) with (epoch) by word.
  wp_loadField.
  wp_if_destruct.
  { (* return error: stale *)
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "Hepoch HnextIndex ∗ # %".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }

  (* FIXME: use uniqueness of γsrv to show that we are not primary, or else have
     the code set isPrimary := false *)
  (* assert (isPrimary = false) as HnotPrimary by admit. *)
  wp_loadField.
  wp_loadField.
  wp_pures.
  destruct (bool_decide (_)) as [] eqn:Hindex; last first.
  { (* return errror: out-of-order *)
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }

  wp_pures.
  apply bool_decide_eq_true in Hindex.

  wp_loadField.
  wp_loadField.
  iNamed "HisSm".
  wp_loadField.

  wp_apply ("HapplySpec" with "[$Hstate $HopSl]").
  { (* prove protocol step *)
    iSplitL ""; first done.
    assert (index = nextIndex) by naive_solver.
    iIntros "Hghost".
    iDestruct "Hghost" as (?) "(%Hre & Hghost & Hprim)".
    iDestruct (ghost_helper1 with "Hs_prop_lb Hghost") as %->.
    { rewrite -(fmap_length fst). rewrite -(fmap_length fst).
      by f_equal. }
    iDestruct (ghost_accept_helper with "Hprop_lb Hghost") as "[Hghost %Happend]".
    { rewrite H in Hσ_index.
      apply (f_equal length) in Hre.
      word.
    }
    { done. }
    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
    { done. }
    { rewrite H in Hσ_index.
      word. }
    iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
    {
      rewrite Hσ_nextIndex. rewrite Hσ_index.
      replace (index) with (nextIndex) by word.
      word.
    }
    rewrite Happend.
    iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb".
    instantiate (1:=(⌜σ = σg ++ [ghost_op]⌝ ∗ is_epoch_lb γsrv epoch ∗ is_accepted_lb γsrv epoch σ)%I).
    iModIntro.

    iSplitL.
    { iExists _; iFrame "Hghost".
      iFrame "Hprim".
      by rewrite fmap_snoc. }
    iFrame "#".
    done.
  }
  iIntros (reply) "(Hreply & Hstate & #Hlb)".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate HprimaryOnly]").
  {
    iNext.
    iExists _, _, _, _, _, _, _.
    rewrite -fmap_snoc.
    iFrame "Hstate ∗#".
    iSplitR.
    { iExists _, _, _; iFrame "#". }
    iSplitR; last iFrame "#".
    2:{
      iDestruct "Hlb" as "(%Hre & Hlb1 & Hlb2)".
      rewrite Hre.
      iFrame "#".
    }
    iPureIntro.
    rewrite app_length.
    rewrite Hσ_nextIndex.
    simpl.
    replace (nextIndex) with (index) by naive_solver.
    word.
  }
  wp_pures.
  iApply "HΦ".
  iDestruct "Hlb" as "(_ & _ & $)".
  done.
Qed.

Lemma wp_Server__Apply_internal (s:loc) γ γsrv op_sl op ghost_op :
  {{{
        is_Server s γ γsrv ∗
        readonly (is_slice_small op_sl byteT 1 op) ∗
        ⌜has_op_encoding op ghost_op.1⌝ ∗
        (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [ghost_op]) ={∅,⊤∖↑ghostN}=∗ True))
  }}}
    pb.Server__Apply #s (slice_val op_sl)
  {{{
        (err:u64) reply_sl, RET (#err, slice_val reply_sl);
        if (decide (err = 0%Z)) then
          ∃ σ,
            let σphys := (λ x, x.1) <$> σ in
            is_slice reply_sl byteT 1 (compute_reply σphys ghost_op.1) ∗
            is_ghost_lb γ (σ ++ [ghost_op])
        else
          True
  }}}
  .
Proof using waitgroupG0.
  iIntros (Φ) "[#His Hpre] HΦ".
  iDestruct "Hpre" as "(#Hsl & %Hghostop_op & Hupd)".
  iNamed "His".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pure1_credit "Hcred".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "Hstate ∗#".
      done.
    }
    wp_pures.
    iApply ("HΦ" $! 1  Slice.nil).
    done.
  }
  wp_loadField.

  wp_if_destruct.
  {
    wp_loadField.
    wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate HprimaryOnly]").
    {
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "Hstate HisSm ∗#".
      iSplitL ""; first done.
      iNamed "HprimaryOnly".
      iExists _, _; iFrame "∗#%".
    }
    wp_pures.
    iApply ("HΦ" $! 1  Slice.nil).
    done.
  }

  clear Heqb.
  (* make proposal *)
  iNamed "HprimaryOnly".
  iAssert (_) with "HisSm" as "HisSm2".
  iNamed "HisSm2".
  wp_loadField.
  wp_loadField.

  wp_apply ("HapplySpec" with "[HisSm $Hstate $Hsl Hcred Hupd]").
  {
    iSplitL ""; first done.
    iIntros "Hghost".
    iDestruct "Hghost" as (?) "(%Hre & Hghost & Hprim)".
    iDestruct (ghost_helper1 with "Hs_prop_lb Hghost") as %->.
    { do 2 (rewrite -(fmap_length fst)).
      rewrite Hre. done. }

    iMod (ghost_propose with "Htok_used_witness Hprim Hcred [Hupd]") as "(Hprim & #Hprop_lb & #Hprop_facts)".
    {
      iMod "Hupd".
      iModIntro.
      iDestruct "Hupd" as (?) "[Hghost Hupd]".
      iExists _; iFrame "Hghost".
      iIntros (->) "Hghost".
      iSpecialize ("Hupd" with "Hghost").
      iMod "Hupd".
      by iModIntro.
    }

    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "HH".
    { done. }
    { rewrite app_length.
      apply (f_equal length) in Hre.
      word.
    }
    iDestruct (ghost_get_accepted_lb with "HH") as "#Hlb".
    instantiate (1:=(is_accepted_lb γsrv epoch (σg ++ [ghost_op]) ∗
                                   is_proposal_lb γ epoch (σg ++ [ghost_op]) ∗
                                   is_proposal_facts γ epoch (σg ++ [ghost_op]))%I).
    iModIntro.
    iSplitL.
    {
      iExists _; iFrame. rewrite fmap_snoc. done.
    }
    iFrame "Hlb #".
  }
  iIntros (reply) "(Hreply & Hstate & #Hprimary_acc_lb)".
  iDestruct "Hprimary_acc_lb" as "(Hprimary_acc_lb & Hprop_lb & Hprop_facts)".
  rewrite -fmap_snoc.

  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_storeField.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsealed Hsm Hclerks Hepoch Hstate Hclerks_sl]").
  {
    iNext.
    iExists _, _, _, _, _, _, _.
    iFrame "Hstate ∗#".
    iSplitL "".
    { iExists _, _, _; iFrame "#". }
    iSplitL "".
    {
      iPureIntro.
      rewrite app_length.
      simpl.
      word.
    }
    iExists _, _.
    iFrame "#%".
  }

  wp_pures.
  wp_apply (wp_NewWaitGroup_free).
  iIntros (wg) "Hwg".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_new_slice).
  { done. }
  iIntros (errs_sl) "Herrs_sl".
  wp_pures.
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iMod (free_WaitGroup_alloc pbN _
                             (λ i,
                               ∃ (err:u64) γsrv',
                               ⌜backups !! int.nat i = Some γsrv'⌝ ∗
                               readonly ((errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z i)↦[uint64T] #err) ∗
                               □ if (decide (err = U64 0)) then
                                 is_accepted_lb γsrv' epoch (σg ++ [ghost_op])
                               else
                                 True
                             )%I
         with "Hwg") as (γwg) "Hwg".
  iMod "Hmask".
  iModIntro.

  wp_apply (wp_allocStruct).
  { econstructor; eauto. }
  iIntros (Hargs) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "epoch") as "#Hargs_epoch".
  iMod (readonly_alloc_1 with "index") as "#Hargs_index".
  iMod (readonly_alloc_1 with "op") as "#Hargs_op".
  wp_pures.
  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  wp_apply (wp_forSlice (λ j, (own_WaitGroup pbN wg γwg j _) ∗
                              (errs_sl.(Slice.ptr) +ₗ[uint64T] int.Z j)↦∗[uint64T] (replicate (int.nat clerks_sl.(Slice.sz) - int.nat j) #0)
                        )%I with "[] [Hwg Herrs_sl $Hclerks_sl2]").
  2: {
    iSplitR "Herrs_sl".
    { iExactEq "Hwg". econstructor. }
    {
      unfold slice.is_slice. unfold slice.is_slice_small.
      iDestruct "Herrs_sl" as "[[Herrs_sl %Hlen] _]".
      destruct Hlen as [Hlen _].
      rewrite replicate_length in Hlen.
      rewrite Hlen.
      iExactEq "Herrs_sl".
      simpl.
      replace (1 * int.Z _)%Z with (0%Z) by word.
      rewrite loc_add_0.
      replace (int.nat _ - int.nat 0) with (int.nat errs_sl.(Slice.sz)) by word.
      done.
    }
  }
  {
    iIntros (i ck).
    clear Φ.
    iIntros (Φ) "!# ([Hwg Herr_ptrs]& %Hi_ineq & %Hlookup) HΦ".
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    replace (int.nat clerks_sl.(Slice.sz) - int.nat i) with (S (int.nat clerks_sl.(Slice.sz) - (int.nat (word.add i 1)))) by word.
    rewrite replicate_S.
    iDestruct (array_cons with "Herr_ptrs") as "[Herr_ptr Herr_ptrs]".
    (* use wgTok to set errs_sl *)
    iDestruct (own_WaitGroup_to_is_WaitGroup with "[Hwg]") as "#His_wg".
    {
      iExactEq "Hwg". econstructor. (* FIXME: why doesn't framing work? *)
    }
    wp_apply (wp_fork with "[Hwg_tok Herr_ptr]").
    {
      iNext.
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as %[γsrv' Hlookupγ].
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc") as "Hclerk_rpc".
      { done. }
      { done. }
      iDestruct "Hclerk_rpc" as "[[Hclerk_rpc Hepoch_lb] _]".
      wp_apply (wp_Clerk__Apply with "[$Hclerk_rpc $Hepoch_lb]").
      {
        iFrame "Hprop_lb Hprop_facts #".
        iPureIntro.
        rewrite last_app.
        rewrite app_length.
        rewrite Hσ_nextIndex.
        simpl.
        split; eauto.
        split; eauto.
        split; first done.
        word.
      }
      iIntros (err) "#Hpost".
      unfold SliceSet.
      wp_pures.
      unfold slice.ptr.
      wp_pures.
      wp_store.

      iMod (readonly_alloc_1 with "Herr_ptr") as "#Herr_ptr".
      wp_apply (wp_WaitGroup__Done with "[$Hwg_tok $His_wg Herr_ptr Hpost]").
      {
        iModIntro.
        iExists _, _.
        iSplitL ""; first done.
        iFrame "#".
      }
      done.
    }
    iApply "HΦ".
    iSplitL "Hwg".
    {
      iExactEq "Hwg". econstructor. (* FIXME: more framing not working *)
    }
    iExactEq "Herr_ptrs".
    f_equal.
    rewrite /ty_size //=.
    rewrite loc_add_assoc.
    f_equal.
    word.
  }
  iIntros "[[Hwg _] _]".
  wp_pures.

  wp_apply (wp_WaitGroup__Wait with "[$Hwg]").
  iIntros "#Hwg_post".
  wp_pures.
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (err_ptr) "Herr".
  wp_pures.

  wp_apply (wp_ref_to).
  { do 2 econstructor. }
  iIntros (j_ptr) "Hi".
  wp_pures.

  set (conf:=(γsrv::backups)).
  iAssert (∃ (j err:u64),
              "Hj" ∷ j_ptr ↦[uint64T] #j ∗
              "%Hj_ub" ∷ ⌜int.nat j ≤ length clerks⌝ ∗
              "Herr" ∷ err_ptr ↦[uint64T] #err ∗
              "#Hrest" ∷ □ if (decide (err = (U64 0)%Z)) then
                (∀ (k:u64) γsrv', ⌜int.nat k ≤ int.nat j⌝ -∗ ⌜conf !! (int.nat k) = Some γsrv'⌝ -∗ is_accepted_lb γsrv' epoch (σg++[ghost_op]))
              else
                True
          )%I with "[Hi Herr]" as "Hloop".
  {
    iExists _, _.
    iFrame.
    destruct (decide (_)).
    {
      iIntros.
      iSplitL "".
      { iPureIntro. word. }
      iModIntro.
      iIntros.
      replace (int.nat 0%Z) with (0) in H by word.
      replace (int.nat k) with (0) in H0 by word.
      unfold conf in H0.
      simpl in H0.
      injection H0 as <-.
      iFrame "Hprimary_acc_lb".
    }
    {
      done.
    }
  }
  wp_forBreak_cond.
  wp_pures.
  iNamed "Hloop".
  wp_load.
  wp_apply wp_slice_len.

  iMod (readonly_load with "Hclerks_sl") as (?) "Htemp".
  iDestruct (is_slice_small_sz with "Htemp") as %Hclerk_sz.
  iClear "Htemp".

  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    wp_load.
    unfold SliceGet.
    wp_call.
    iDestruct (big_sepS_elem_of_acc _ _ j with "Hwg_post") as "[HH _]".
    { set_solver. }
    iDestruct "HH" as "[%Hbad|HH]".
    { exfalso. word. }
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
        assert (int.nat k ≤ int.nat j ∨ int.nat k = int.nat (word.add j 1%Z)) as [|].
        {
          replace (int.nat (word.add j 1%Z)) with (int.nat j + 1) in * by word.
          word.
        }
        {
          by iApply "Hrest".
        }
        {
          destruct (decide (_)); last by exfalso.
          replace (γsrv'0) with (γsrv'); last first.
          {
            rewrite H1 in H0.
            replace (int.nat (word.add j 1%Z)) with (S (int.nat j)) in H0 by word.
            unfold conf in H0.
            rewrite lookup_cons in H0.
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
      word.
    }
  }
  iRight.
  iModIntro.
  iSplitL ""; first done.
  wp_pures.
  wp_load.
  wp_pures.


  iApply "HΦ".
  destruct (decide (err = 0%Z)); last first.
  {
    done.
  }
  {
    iExists _.
    iMod (ghost_commit with "Hsys_inv [Hrest] Hprop_lb Hprop_facts") as "$".
    {
      iExists _; iFrame "#".
      iIntros.
      apply elem_of_list_lookup_1 in H as [k Hlookup_conf].
      replace (int.nat j) with (length clerks); last first.
      { word. }
      epose proof (lookup_lt_Some _ _ _ Hlookup_conf) as HH.
      replace (k) with (int.nat k) in *; last first.
      {
        rewrite -Hconf_clerk_len in HH.
        rewrite Hclerk_sz in HH.
        word.
      }
      iApply ("Hrest" $! k).
      { iPureIntro. rewrite Hconf_clerk_len. unfold conf in HH.
        lia. }
      { done. }
    }
    iFrame "Hreply".
    by iModIntro.
  }
Qed.

Definition appN := pbN .@ "app".
Definition escrowN := pbN .@ "escrow".
Definition is_inv γlog γsys :=
  inv appN (∃ σ,
        own_log γlog (fst <$> σ) ∗
        own_ghost γsys σ ∗
        □(
          ∀ σ' σ'prefix lastEnt, ⌜prefix σ' σ⌝ -∗ ⌜σ' = σ'prefix ++ [lastEnt]⌝ -∗ (lastEnt.2 (fst <$> σ'prefix))
        )
      ).

Lemma prefix_app_cases {A} (σ σ':list A) e:
  σ' `prefix_of` σ ++ [e] →
  σ' `prefix_of` σ ∨ σ' = (σ++[e]).
Proof.
Admitted.

Lemma wp_Server__Apply (s:loc) γlog γ γsrv op_sl op (op_bytes:list u8) (Φ: val → iProp Σ) :
  has_op_encoding op_bytes op →
  £ 1 -∗ (* FIXME: can generate this inside of Server__Apply, but need to put it postcond *)
  £ 1 -∗
  is_inv γlog γ -∗
  is_Server s γ γsrv -∗
  readonly (is_slice_small op_sl byteT 1 op_bytes) -∗
  (* the fupd needs to be fired while some internal pb invariants are open
     (those invariants contain (fupd ∨ Q) currently, so it will be annoying to
     close them while we fire it), so we need to exclude pbN from the outer
     mask. *)
  (|={⊤∖↑pbN,∅}=> ∃ σ, own_log γlog σ ∗ (own_log γlog (σ ++ [op]) ={∅,⊤∖↑pbN}=∗
        ∀ (reply_sl:Slice.t),
            is_slice reply_sl byteT 1 (compute_reply σ op) -∗
            Φ (#(U64 0), (slice_val reply_sl))%V
  )) -∗
  (∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ Φ (#err, (slice_val unused_sl))%V ) -∗
  WP (pb.Server__Apply #s (slice_val op_sl)) {{ Φ }}
.
Proof using Type*.
  iIntros "%Hop_enc Hcred Hcred2 #Hinv #Hsrv #Hop_sl Hupd Hfail_Φ".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  iApply wp_fupd.
  wp_apply (wp_Server__Apply_internal _ _ _ _ _
      (op, (λ σ, inv escrowN (
          (∀ reply_sl : Slice.t, is_slice reply_sl byteT 1 (compute_reply σ op) -∗
                Φ (#(U64 0), slice_val reply_sl)%V) ∨
          ghost_var γtok 1 ()
        ))%I)
             with "[$Hsrv $Hop_sl Hupd]").
  {
    iSplitL ""; first done.
    iInv "Hinv" as "HH" "Hclose".
    iDestruct "HH" as (?) "(>Hlog & >Hghost & #HQs)".
    iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
    {
      assert ((↑ghostN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      assert ((↑appN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      set_solver.
    }
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (σ0) "[Hlog2 Hupd]".
    iDestruct (own_valid_2 with "Hlog Hlog2") as %Hvalid.
    apply mono_list_auth_dfrac_op_valid_L in Hvalid.
    destruct Hvalid as [_ <-].
    iExists _; iFrame.
    iIntros "Hghost".
    iMod (own_update_2 with "Hlog Hlog2") as "Hlog".
    {
      rewrite -mono_list_auth_dfrac_op.
      rewrite dfrac_op_own.
      rewrite Qp.half_half.
      apply mono_list_update.
      instantiate (1:=σ.*1 ++ [op]).
      by apply prefix_app_r.
    }
    iEval (rewrite -Qp.half_half -dfrac_op_own mono_list_auth_dfrac_op) in "Hlog".
    iDestruct "Hlog" as "[Hlog Hlog2]".
    iMod ("Hupd" with "Hlog2") as "Hupd".

    iAssert (|={↑escrowN}=> inv escrowN ((∀ reply_sl : Slice.t, is_slice reply_sl byteT 1 (compute_reply σ.*1 op) -∗ Φ (#0, slice_val reply_sl)%V) ∨ ghost_var γtok 1 ()))%I
            with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iLeft.
      iApply "Hupd".
    }
    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    {
      assert ((↑escrowN:coPset) ## (↑ghostN:coPset)).
      { by apply ndot_ne_disjoint. }
      assert ((↑escrowN:coPset) ## (↑appN:coPset)).
      { by apply ndot_ne_disjoint. }
      set_solver.
    }
    iMod "Hinv2" as "#HΦ_inv".
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hlog]").
    {
      iNext.
      iExists _; iFrame.
      rewrite fmap_app.
      simpl.
      iFrame.
      iModIntro.
      iIntros.

      apply prefix_app_cases in H as [Hprefix_of_old|Hnew].
      {
        iApply "HQs".
        { done. }
        { done. }
      }
      {
        rewrite Hnew in H0.
        assert (σ = σ'prefix) as ->.
        { (* TODO: list_solver. *)
          apply (f_equal reverse) in H0.
          rewrite reverse_snoc in H0.
          rewrite reverse_snoc in H0.
          inversion H0.
          apply (f_equal reverse) in H2.
          rewrite reverse_involutive in H2.
          rewrite reverse_involutive in H2.
          done.
        }
        eassert (_ = lastEnt) as <-.
        { eapply (suffix_snoc_inv_1 _ _ _ σ'prefix). rewrite -H0.
          done. }
        simpl.
        iFrame "#".
      }
    }
    done.
  }
  iIntros (err reply_sl).
  destruct (decide (err = U64 0)).
  { (* no error *)
    rewrite e.
    iIntros "Hpost".
    iDestruct "Hpost" as (?) "(Hreply_sl & #Hghost_lb)".
    iInv "Hinv" as "HH" "Hclose".
    {
      iDestruct "HH" as (?) "(>Hlog & >Hghost & #HQs)".
      iMod (lc_fupd_elim_later with "Hcred HQs") as "#HQ".
      iDestruct (own_valid_2 with "Hghost Hghost_lb") as %Hvalid.
      rewrite mono_list_both_dfrac_valid_L in Hvalid.
      destruct Hvalid as [_ Hvalid].
      iSpecialize ("HQ" $! _ σ _ with "[] []").
      { done. }
      { done. }
      simpl.
      iMod ("Hclose" with "[Hghost Hlog]") as "_".
      {
        iNext.
        iExists _; iFrame "∗#".
      }

      iInv "HQ" as "Hescrow" "Hclose".
      iDestruct "Hescrow" as "[HΦ|>Hbad]"; last first.
      {
        iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
        exfalso. naive_solver.
      }
      iMod ("Hclose" with "[$Htok]").
      iMod (lc_fupd_elim_later with "Hcred2 HΦ") as "HΦ".
      iModIntro.
      iApply "HΦ".
      iFrame.
    }
  }
  {
    iIntros.
    iApply "Hfail_Φ".
    done.
  }
Qed.

End pb_apply_proof.
