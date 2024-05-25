From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial Require Export paxos.definitions paxos.applyasfollower_proof.
From Perennial.base_logic Require Import lib.saved_prop.

Section tryacquire_proof.

Context `{!heapGS Σ}.
Context `{Hparams:!paxosParams.t Σ}.
Import paxosParams.
Context `{!paxosG Σ}.

Notation ghostN := (ghostN (N:=N)).

Definition own_releaseFn_internal (f:val) γ sl_ptr oldstate : iProp Σ :=
  ∀ sl Φ newstate Q,
  ( (* precondition: *)
  "Hsl_ptr" ∷ sl_ptr ↦[slice.T byteT] (slice_val sl) ∗
  "#Hsl" ∷ readonly (own_slice_small sl byteT (DfracOwn 1) newstate) ∗
  "#HP" ∷ (□ Pwf newstate) ∗
  "Hupd" ∷ (|={⊤∖↑ghostN,∅}=> ∃ σ, own_log γ.(s_mp) σ ∗
              (⌜ get_state σ = oldstate ⌝ -∗ own_log γ.(s_mp) (σ ++ [(newstate, Q)]) ={∅,⊤∖↑ghostN}=∗ True))
  ) -∗
  ( ∀ (err:u64), ((* postcondition*)
             £ 1 ∗ £ 1 ∗
             if (decide (err = 0)) then
               ∃ σ,
               is_log_lb γ.(s_mp) (σ ++ [(newstate, Q)])
             else
               True
      ) -∗ Φ #err
  ) -∗
  WP f #() {{ Φ }}
.

Definition own_releaseFn (f:val) γ sl_ptr oldstate : iProp Σ :=
  ∀ sl Φ newstate,
  ( (* precondition: *)
  "Hsl_ptr" ∷ sl_ptr ↦[slice.T byteT] (slice_val sl) ∗
  "Hsl" ∷ readonly (own_slice_small sl byteT (DfracOwn 1) newstate) ∗
  "Hwf" ∷ (□ Pwf newstate) ∗
  "Hupd" ∷ (|={⊤∖↑N,∅}=> ∃ oldstate', own_state γ oldstate' ∗
              (⌜ oldstate' = oldstate ⌝ -∗ own_state γ newstate ={∅,⊤∖↑N}=∗ Φ #0))
  ) -∗
  (∀ (err:u64), ⌜ err ≠ W64 0 ⌝ → Φ #err) -∗
  WP f #() {{ Φ }}
.

Lemma wp_Server__TryAcquire_internal s γ γsrv  :
  {{{
        is_Server s γ γsrv
  }}}
    Server__TryAcquire #s
  {{{
        (err:u64) (sl_ptr:loc) (rel:val), RET (#err, #sl_ptr, rel);
        £ 1 ∗ £ 1 ∗
        if (decide (err = 0%Z)) then
          ∃ sl oldstate,
            sl_ptr ↦[slice.T byteT] (slice_val sl) ∗
            readonly (own_slice_small sl byteT (DfracOwn 1) oldstate) ∗
            Pwf oldstate ∗
            own_releaseFn_internal rel γ sl_ptr oldstate
        else
          True
  }}}.
Proof.
  iIntros (Φ) "#Hsrv HΦ".
  wp_call.
  wp_apply wp_ref_of_zero; first done.
  iIntros (err_ptr) "Herr".
  wp_pure1_credit "Hlc1".
  wp_pure1_credit "Hlc2".
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  iNamed "Hvol".
  wp_pure1_credit "Hlc3".
  wp_loadField.
  wp_loadField.
  wp_pure1_credit "Hlc4".
  wp_if_destruct.
  { (* case: not leader *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hlc1 Hlc2]").
    {
      do 2 iFrame "∗#%".
    }
    wp_pures.
    wp_apply wp_ref_of_zero.
    { done. }
    iIntros (n) "Hn".
    wp_pures. wp_load.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
  }
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_apply wp_struct_fieldRef.
  { done. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Hlc1 Hlc2".
  setoid_rewrite decide_True; last word.
  repeat iExists _.
  iFrame "∗#".
  iSplitL "Hstate".
  {
    iExactEq "Hstate".
    rewrite struct_field_pointsto_eq.
    done. (* FIXME: maybe add a lemma to avoid unfolding this definition? *)
  }
  clear Φ.
  iClear "Hstate_sl".
  iClear "HP".
  rewrite /own_releaseFn_internal.
  iIntros "*". iNamed 1.
  iIntros "HΦ".
  wp_apply (wp_frame_wand with "[Hlc3 Hlc4]"); first iNamedAccu.
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iAssert (ps ↦[paxosState :: "state"] (slice_val sl))%I with "[Hsl_ptr]" as "Hsl_ptr".
  { iExactEq "Hsl_ptr". rewrite struct_field_pointsto_eq. done. }
  wp_loadField.
  wp_apply (wp_allocStruct).
  { repeat econstructor. done. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "Hargs".
  wp_pure1_credit "Hlc".
  wp_loadField.
  wp_apply (paxosState.wp_encode with "[Hepoch HaccEpoch HnextIndex HisLeader Hsl_ptr]").
  {
    instantiate (1:=paxosState.mk _ _ _ _ _).
    repeat iExists _. simpl. iFrame "∗#".
  }
  iIntros (?) "[Hvol Henc]".
  wp_loadField.
  iDestruct (own_slice_to_small with "Henc") as "Henc".
  wp_apply (wp_AsyncFile__Write with "[-Hvol Hlocked Hstorage Hps]").
  2:{ (* this just deals with unlocking and sends the WP for the rest of the code to the fupd *)
    iIntros (?) "[Hfile Hwp]".
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-Hwp]").
    { iFrame "HmuInv Hlocked". iNext. repeat iExists _.
      iFrame "∗#%". iPureIntro. by left.
    }
    wp_pures.
    wp_bind (w #()).
    wp_apply (wp_wand with "Hwp").
    {
      iIntros (?) "Hwp".
      wp_pures.
      iAccu.
    }
  }
  (* start ghost reasoning *)
  iFrame.
  iNamed 1.
  eapply encodes_paxosState_inj in Henc; last exact HencPaxos.
  subst.
  rewrite /own_file_inv.
  rewrite sep_exist_r.
  setoid_rewrite <- (assoc bi_sep).
  iExists _.
  iSplitR; first (iPureIntro; by left).
  iNamed "Hghost".
  rewrite Heqb.
  iMod (fupd_mask_subseteq _) as "Hmask".
  2: iMod (ghost_leader_propose with "HleaderOnly Hlc [Hupd]") as "(HleaderOnly & #Hprop)".
  { solve_ndisj. }
  {
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (?) "[H1 Hupd]".
    iExists _. iFrame "H1".
    iIntros "%Heq Hghost".
    rewrite Heq /=.
    iMod ("Hupd" with "[% //] Hghost").
    iModIntro.
    done.
  }

  rewrite Heqb in HaccEpochEq.
  repeat rewrite HaccEpochEq.
  iMod (ghost_replica_accept_same_epoch with "Hghost Hprop") as "[_ Hghost]".
  { word. }
  { simpl. done. }
  { rewrite app_length. word. }
  iMod "Hmask" as "_".

  iModIntro.
  simpl.
  iSplitR "HΦ Herr Hargs".
  {
    repeat iExists _.
    simpl.
    iFrame "∗#".
    iPureIntro.
    rewrite app_length /=.
    split_and!; try done; try word.
    { rewrite fmap_app last_app /= //. }
  }
    (* end ghost reasoning *)

  wp_loadField.
  wp_pures.

  (* set (newstate:=(next_state (default [] (last st.(mp_log).*1)) op)). *)
  rename pst0 into pst.
  iAssert (|={⊤}=> applyAsFollowerArgs.own args_ptr (applyAsFollowerArgs.mkC
                                               pst.(paxosState.epoch)
                                               (W64 (length log + 1))
                                               newstate
          ))%I with "[Hargs]" as "Hargs".
  {
    iNamed "Hargs".
    iExists _.
    iMod (readonly_alloc_1 with "epoch") as "$".
    simpl.
    rewrite HlogLen.

    rewrite Z2Nat.id; last word.
    rewrite -Hno_overflow.
    unfold W64.
    rewrite word.of_Z_unsigned.

    iMod (readonly_alloc_1 with "nextIndex") as "$".
    iMod (readonly_alloc_1 with "state") as "$".
    iModIntro. iFrame "#".
  }
  iMod "Hargs" as "#Hargs".

  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (numReplies_ptr) "HnumReplies".
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (own_slice_small_sz with "Hclerks_sl2") as "%Hclerks_sz".
  iClear "Hclerks_sl2".
  clear q.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  rewrite -Hclerks_sz.
  iIntros (replies_sl) "Hreplies_sl".
  simpl.

  wp_pures.
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ own_slice_small replies_sl ptrT (DfracOwn 1) reply_ptrs ∗
                    "#Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; γ.(s_hosts),
                    ⌜reply_ptr = null⌝ ∨ □(∃ reply, readonly (applyAsFollowerReply.own reply_ptr reply (DfracOwn 1)) ∗
                                                   if decide (reply.(applyAsFollowerReply.err) = (W64 0)) then
                                                     is_accepted_lb γsrv' pst.(paxosState.epoch) (log ++ [(newstate, Q)])
                                                   else
                                                     True
                                         ))
                )%I).
  wp_apply (newlock_spec N _ replyInv with "[HnumReplies Hreplies_sl]").
  {
    iNext.
    iExists _, _.
    iDestruct (own_slice_to_small with "Hreplies_sl") as "$".
    iFrame "∗".
    iDestruct (big_sepL2_length with "Hclerks_rpc") as "%Hlen".
    iApply big_sepL2_forall.
    rewrite Hlen.
    iSplit.
    { rewrite replicate_length. done. }
    iIntros.
    iLeft.
    iPureIntro.
    rewrite lookup_replicate in H.
    naive_solver.
  }
  iIntros (replyMu) "#HreplyMuInv".
  wp_pures.
  wp_apply (wp_newCond with "HreplyMuInv").
  iIntros (numReplies_cond) "#HnumReplies_cond".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  wp_apply (wp_forSlice (λ _, True%I) (V:=loc) with "[] [$Hclerks_sl2]").
  { (* loop iteration *)
    clear Φ.
    iIntros (?? Φ) "!# (_ & %Hi_le & %Hi_lookup) HΦ".
    wp_call.
    wp_apply (wp_fork with "[]").
    { (* make applyAsFollower RPC and put reply in the replies list *)
      iNext.
      wp_pures.

      (* establish is_singleClerk *)
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as (?) "%Hi_conf_lookup".
      { done. }
      iAssert (_) with "Hclerks_rpc" as "Hclerks_rpc2".
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc2") as "[#His_ck _]".
      { done. }
      { done. }
      wp_apply (wp_singleClerk__applyAsFollower with "[$His_ck]").
      {
        iFrame.
        iFrame "Hargs Hprop HP".
        iPureIntro.
        split.
        { rewrite app_length. simpl. word. }
        { simpl. rewrite fmap_app last_app /= //. }
      }
      iIntros (reply_ptr reply) "Hreply".
      wp_pures.

      wp_apply (acquire_spec with "HreplyMuInv").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_load.
      wp_store.
      iDestruct (big_sepL2_lookup_2_some with "Hreplies") as (?) "%Hi_replies_lookup".
      { done. }
      wp_apply (wp_SliceSet with "[$Hreplies_sl]").
      {
        done.
      }
      iIntros "Hreplies_sl".
      wp_pures.
      wp_load.
      iDestruct "Hreply" as "[Hreply #Hpost]".
      iMod (readonly_alloc_1 with "Hreply") as "#Hreply".
      wp_apply (wp_If_optional _ _ (True%I)).
      {
        iIntros (?) "_ HΦ'".
        wp_apply (wp_condSignal with "HnumReplies_cond").
        wp_pures.
        by iApply "HΦ'".
      }
      wp_apply (release_spec with "[-]").
      {
        iFrame "# Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗%".
        iApply to_named.
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies2]".
        { done. }
        { done. }
        iDestruct ("Hreplies2" $! reply_ptr x2 with "[]") as "Hreplies3".
        {
          iRight.
          iModIntro.
          iExists _.
          iFrame "#".
        }

        replace (<[uint.nat i:=x2]> γ.(s_hosts)) with (γ.(s_hosts)) ; last first.
        {
          symmetry.
          by apply list_insert_id.
        }
        iFrame "Hreplies3".
      }
      done.
    }
    iApply "HΦ".
    done.
  }
  iIntros "_".
  wp_pures.

  wp_apply (acquire_spec with "[$HreplyMuInv]").
  iIntros "[Hlocked Hown]".
  wp_pures.

  wp_forBreak_cond.
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* not enough replies, wait for cond *)
    wp_pures.
    wp_apply (wp_condWait with "[-HΦ Herr]").
    {
      iFrame "∗#".
      iExists _, _.
      iFrame "∗#".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame.
  }
  (* got enough replies to stop waiting; now we need to count how many successes *)
  iRight.
  iModIntro.
  iSplitR; first done.

  wp_pures.
  wp_apply (wp_ref_to).
  { auto. }
  iIntros (numSuccesses_ptr) "HnumSuccesses".
  wp_pures.

  iDestruct (big_sepL2_length with "Hclerks_rpc") as %Hconf_clerk_len.
  set (I:=λ (i:u64), (
                 ∃ (W: gset nat),
                 "%HW_in_range" ∷ ⌜∀ s, s ∈ W → s < uint.nat i⌝ ∗
                 "%HW_size_nooverflow" ∷ ⌜(size W) ≤ uint.nat i⌝ ∗
                 "HnumSuccesses" ∷ numSuccesses_ptr ↦[uint64T] #(W64 (size W)) ∗
                 "#Hacc_lbs" ∷ ([∗ list] s ↦ γsrv' ∈ γ.(s_hosts), ⌜s ∈ W⌝ → is_accepted_lb γsrv' pst.(paxosState.epoch) (log ++ [(newstate, Q)]))
      )%I).

  wp_apply (wp_forSlice (V:=loc) I _ _ _ _ _ reply_ptrs with "[] [HnumSuccesses Hreplies_sl]").
  2: {
    iFrame "Hreplies_sl".

    iExists ∅.
    rewrite size_empty.
    iFrame.
    iSplitL.
    { iPureIntro. done. }
    iSplitL.
    { iPureIntro. done. }
    iApply (big_sepL_forall).
    iIntros.
    exfalso.
    done.
  }
  {
    clear Φ.
    iIntros (?? Φ) "!# (Hi & %Hi_lt & %Hi_lookup) HΦ".
    iNamed "Hi".
    wp_pures.
    wp_if_destruct.
    {
      iDestruct (big_sepL2_lookup_1_some with "Hreplies") as (?) "%Hi_conf_lookup".
      { done. }
      iDestruct (big_sepL2_lookup_acc with "Hreplies") as "[#Hreply_post _]".
      { done. }
      { done. }
      iDestruct "Hreply_post" as "[%Hbad|#Hreply_post]".
      {
        exfalso. subst. done.
      }
      iDestruct "Hreply_post" as (?) "[#Hreply Hpost]".
      iMod (readonly_load with "Hreply") as (?) "Hreplyq".
      wp_loadField.
      wp_if_destruct.
      { (* increase size of W *)
        wp_load.
        wp_store.
        rewrite -Heqb2.
        iEval (rewrite decide_True) in "Hpost".
        iApply "HΦ".
        iModIntro.
        iExists (W ∪ {[ uint.nat i ]}).
        iSplitR.
        { (* prove that the new set W is still in range *)
          replace (uint.nat (word.add i (W64 1))) with (uint.nat i + 1) by word.
          iPureIntro.
          intros ? Hin.
          rewrite elem_of_union in Hin.
          destruct Hin as [Hold|Hnew].
          {
            specialize (HW_in_range s0 Hold). word.
          }
          {
            rewrite elem_of_singleton in Hnew.
            rewrite Hnew.
            word.
          }
        }

        rewrite size_union; last first.
        {
          apply disjoint_singleton_r.
          destruct (decide (uint.nat i ∈ W)).
          {
            exfalso.
            specialize (HW_in_range (uint.nat i) e).
            word.
          }
          done.
        }
        rewrite size_singleton.

        iSplitL "".
        {
          iPureIntro.
          word.
        }

        iSplitL "HnumSuccesses".
        {
          iApply to_named.
          iExactEq "HnumSuccesses".
          f_equal.
          f_equal.

          apply lookup_lt_Some in Hi_conf_lookup.
          rewrite -Hconf_clerk_len Hclerks_sz in Hi_conf_lookup.
          assert (Z.of_nat (size W) < uint.Z clerks_sl.(Slice.sz))%Z by word.
          repeat f_equal. word.
        }

        iApply (big_sepL_impl with "Hacc_lbs").
        iModIntro.
        iIntros (?? ?) "Hacc_wand".
        iIntros (Hin).
        rewrite elem_of_union in Hin.
        destruct Hin as [Hold|Hnew].
        {
          iApply "Hacc_wand".
          done.
        }
        {
          rewrite elem_of_singleton in Hnew.
          rewrite Hnew.
          replace (x0) with (x2).
          { done. }
          rewrite Hnew in H.
          rewrite Hi_conf_lookup in H.
          by injection H.
        }
      }
      { (* node i didn't accept, don't change W *)
        iModIntro.
        iApply "HΦ".
        iExists W.
        iFrame "HnumSuccesses".
        iFrame "Hacc_lbs".
        iPureIntro.
        replace (uint.nat (word.add i (W64 1))) with (uint.nat i + 1) by word.
        split.
        {
          intros.
          specialize (HW_in_range s0 H).
          word.
        }
        {
          word.
        }
      }
    }
    { (* node i didn't reply, don't change W *)
      iModIntro.
      iApply "HΦ".
      iExists W.
      iFrame "HnumSuccesses".
      iFrame "Hacc_lbs".
      iPureIntro.
      replace (uint.nat (word.add i (W64 1))) with (uint.nat i + 1) by word.
      split.
      {
        intros.
        specialize (HW_in_range s0 H).
        word.
      }
      {
        word.
      }
    }
  }

  iIntros "[Hi Hreplies_sl]".
  iDestruct (own_slice_small_sz with "Hreplies_sl") as "%Hreplies_sz".
  iNamed "Hi".
  wp_pure1_credit "Hcred1".
  wp_pure1_credit "Hcred2".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* enough acceptances to commit *)
    wp_store.
    wp_pures.
    wp_load.
    wp_pures.

    iDestruct (big_sepL2_length with "Hreplies") as "%Hreplies_len_eq_conf".
    replace (uint.nat replies_sl.(Slice.sz)) with (length γ.(s_hosts)) in HW_in_range; last first.
    { word. }

    iDestruct (establish_committed_by with "[$Hacc_lbs]") as "Hcom".
    { done. }
    {
      assert (2 * size W >= uint.Z (word.mul 2 (size W)))%Z.
      {
        rewrite word.unsigned_mul.
        rewrite /word.wrap /=.
        apply Z.le_ge.
        etrans.
        { apply Z.mod_le; word. }
        word.
      }
      simpl.
      word.
    }
    iMod (ghost_commit with "Hinv Hcom Hprop") as "Hlb".
    iModIntro. iNamed 1.
    iApply "HΦ".
    iFrame.
  }
  { (* error, too few successful applyAsFollower() RPCs *)
    wp_store. wp_pures.
    wp_load. wp_pures. iModIntro. iNamed 1.
    iApply "HΦ". iFrame.
  }
Qed.

Lemma prefix_app_cases {A} (σ σ':list A) e:
  σ' `prefix_of` σ ++ [e] →
  σ' `prefix_of` σ ∨ σ' = (σ++[e]).
Proof.
  intros [σ0 Heq].
  induction σ0 using rev_ind.
  { rewrite app_nil_r in Heq. right; congruence. }
  { rewrite app_assoc in Heq.
    apply app_inj_2 in Heq as [-> ?]; last auto.
    left. eexists; eauto.
  }
Qed.

(* This is where "helping" happens. *)
Lemma releaseFn_fact γ rel sl_ptr oldstate :
  £ 1 -∗ £ 1 -∗
  is_helping_inv γ -∗
  own_releaseFn_internal rel γ sl_ptr oldstate -∗
  own_releaseFn rel γ sl_ptr oldstate
.
Proof.
  iIntros "Hlc1 Hlc2 #Hinv Hwp".
  iIntros (?) "*". iNamed 1.
  iIntros "Hfail".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  iApply wp_fupd.

  set (Q := (inv escrowN (Φ #0 ∨ ghost_var γtok 1 ())%I)).

  iMod (saved_prop_alloc Q DfracDiscarded) as (γghost_op) "#Hsaved"; first done.

  wp_apply ("Hwp" $! _ _ _ γghost_op with "[-Hfail Htok Hlc2] [-]").
  {
    iFrame "∗#".
    iInv "Hinv" as "HH" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 HH") as "HH".
    iDestruct "HH" as (?) "(Hstate & Hghost & #HQs)".
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod "Hupd" as (?) "[Hstate2 Hupd]".
    { rewrite /ghostN /appN /=. solve_ndisj. }
    iModIntro.
    iDestruct (own_valid_2 with "Hstate Hstate2") as %Hvalid.
    rewrite dfrac_agree_op_valid_L in Hvalid.
    destruct Hvalid as [_ Heq].
    rewrite Heq.
    iDestruct "Hghost" as (?) "(Hghost & %HintEq & #?)".
    iExists _; iFrame.
    iIntros "%Heq2 Hghost".
    subst.

    iMod (own_update_2 with "Hstate Hstate2") as "Hstate".
    {
      apply (dfrac_agree_update_2).
      rewrite dfrac_op_own.
      rewrite Qp.half_half.
      done.
    }
    iDestruct "Hstate" as "[Hstate Hstate2]".
    iMod ("Hupd" with "[] Hstate2") as "Hupd".
    { iPureIntro. rewrite /get_state /=. rewrite HintEq. done. }

    iAssert (|={↑escrowN}=> inv escrowN
                               (Φ #0 ∨ ghost_var γtok 1 ()))%I
      with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iFrame.
    }

    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    2: iMod "Hinv2" as "#HΦ_inv".
    { rewrite /escrowN /=. solve_ndisj. }
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hstate]").
    {
      iNext.
      iExists _. iSplitL "Hstate"; last first.
      {
        iSplitL "Hghost".
        {
          iExists _; iFrame.
          repeat rewrite -sep_assoc.
          iSplitR; first iPureIntro.
          { instantiate (1:=(log ++ [(newstate, Q)])). do 2 rewrite fmap_app /=. by rewrite HintEq. }
          rewrite ?fmap_app. iApply big_sepL2_app.
          { iFrame "#". }
          iApply big_sepL2_singleton. iFrame "Hsaved".
        }

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
          replace (log'prefix) with (log); last first.
          { (* TODO: list_solver *)
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
          { eapply (suffix_snoc_inv_1 _ _ _ log'prefix). rewrite -H0.
            done. }
          simpl.
          iFrame "HΦ_inv".
        }
      }
      rewrite /get_state fmap_app last_app /=.
      done.
    }
    done.
  }
  iIntros "* (Hlc1 & Hlc3 & Hpost)".

  destruct (decide (err = W64 0)).
  { (* no error *)
    subst.
    setoid_rewrite decide_True.
    2:{ word. }
    iDestruct "Hpost" as (?) "#Hghost_lb".
    iInv "Hinv" as "HH" "Hclose".
    iMod (lc_fupd_elim_later with "Hlc1 HH") as "HH".
    iDestruct "HH" as (?) "(Hlog & Hghost & #HQs)".
    iDestruct "Hghost" as (?) "(Hghost&%Hfst_eq&#Hsaved')".
    iDestruct (own_valid_2 with "Hghost Hghost_lb") as %Hvalid.
    rewrite mono_list_both_dfrac_valid_L in Hvalid.
    destruct Hvalid as (_&σtail&Hvalid').
    subst.
    iDestruct (big_sepL2_length with "Hsaved'") as %Hlen.
    rewrite ?fmap_length app_length in Hlen.

    iAssert (_) with "Hsaved'" as "-#Hs".
    iFreeze "Hsaved'".
    rewrite fmap_app.
    iDestruct (big_sepL2_to_sepL_2 with "Hs") as "Hs".
    iDestruct (big_sepL_app with "Hs") as "[Hs _]".
    rewrite fmap_app.
    iDestruct (big_sepL_app with "Hs") as "[_ Hs]".
    rewrite big_sepL_singleton.
    iDestruct "Hs" as (?) "[%Hlookup #Hsaved2]".

    destruct (log !! (length σ)) eqn:HlookupFull.
    2:{ exfalso.
        rewrite list_lookup_fmap fmap_length in Hlookup.
        rewrite Nat.add_0_r HlookupFull /= in Hlookup.
        done.
    }
    destruct p.
    assert (y1 = u); last subst.
    { rewrite list_lookup_fmap fmap_length in Hlookup.
      rewrite Nat.add_0_r HlookupFull /= in Hlookup. naive_solver. }
    iAssert (_) with "HQs" as "HQ".
    iSpecialize ("HQ" $! (take (S (length σ)) log) (take (length σ) log) _ with "[] []").
    { iPureIntro. apply prefix_take. }
    { iPureIntro. by apply take_S_r. }
    iMod ("Hclose" with "[Hghost Hlog]") as "_".
    {
      iNext.
      iExists _; iFrame "∗#".
      iThaw "Hsaved'". iFrame "∗#%".
    }
    iClear "Hsaved'".
    iDestruct (saved_prop_agree with "Hsaved Hsaved2") as "Hagree".
    iApply (lc_fupd_add_later with "[$]"). iNext.
    iRewrite -"Hagree" in "HQ".
    simpl.

    iInv "HQ" as "Hescrow" "Hclose".
    iDestruct "Hescrow" as "[HΦ|>Hbad]"; last first.
    {
      iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
      exfalso. naive_solver.
    }
    iMod ("Hclose" with "[$Htok]").
    iMod (lc_fupd_elim_later with "Hlc2 HΦ") as "HΦ".
    iModIntro.
    iApply "HΦ".
  }
  {
    iIntros.
    iApply "Hfail".
    done.
  }
Qed.

Lemma wp_Server__TryAcquire s γ γsrv  :
  {{{
        is_Server s γ γsrv
  }}}
    Server__TryAcquire #s
  {{{
        (err:u64) (sl_ptr:loc) (rel:val), RET (#err, #sl_ptr, rel);
        if (decide (err = 0%Z)) then
          ∃ sl oldstate,
            sl_ptr ↦[slice.T byteT] (slice_val sl) ∗
            readonly (own_slice_small sl byteT (DfracOwn 1) oldstate) ∗
            Pwf oldstate ∗
            own_releaseFn rel γ sl_ptr oldstate
        else
          True
  }}}.
Proof.
  iIntros (?) "#Hsrv HΦ".
  wp_apply (wp_Server__TryAcquire_internal with "[$]").
  iIntros "* Hpost".
  iApply "HΦ".
  destruct (decide _).
  2:{ done. }
  iDestruct "Hpost" as "(? & ? & Hpost)".
  iNamed "Hpost". repeat iExists _.
  iDestruct "Hpost" as "($ & $ & $ & H)".
  iNamed "Hsrv". iApply (releaseFn_fact with "[$] [$] [$] [$]").
Qed.

End tryacquire_proof.
