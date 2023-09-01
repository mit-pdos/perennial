From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export definitions applyasfollower_proof.

Section apply_proof.

Context `{!heapGS Σ}.
Context `{Hparams:!mpaxosParams.t Σ}.
Import mpaxosParams.
Context `{!mpG Σ}.

Definition own_applyfn (f:val) γ Q : iProp Σ :=
  ∀ Φ (oldstate:list u8) old_sl,
  (readonly (own_slice_small old_sl byteT 1 oldstate) ∗
   Pwf oldstate) -∗
  (∀ new_sl reply_sl (newstate reply:list u8),
  (readonly (own_slice_small new_sl byteT 1 newstate) ∗
   readonly (own_slice_small reply_sl byteT 1 reply) ∗
   (□ Pwf newstate) ∗
   (|={⊤∖↑ghostN,∅}=> ∃ σ, own_ghost γ σ ∗
      (⌜ get_state σ = oldstate ⌝ -∗ own_ghost γ (σ ++ [(newstate, Q reply)]) ={∅,⊤∖↑ghostN}=∗ True)))
  -∗ Φ (slice_val new_sl, slice_val reply_sl)%V
  ) -∗
  WP f (slice_val old_sl) {{ Φ }}
.

Lemma wp_Server__apply_internal Q s γ γsrv f :
  {{{
        is_Server s γ γsrv ∗
        own_applyfn f γ Q
  }}}
    mpaxos.Server__Apply #s f
  {{{
        (err:u64) reply_sl, RET (#err, slice_val reply_sl);
        £ 1 ∗ £ 1 ∗
        if (decide (err = 0%Z)) then
          ∃ someState σ reply,
          readonly (own_slice_small reply_sl byteT 1 reply) ∗
          is_ghost_lb γ (σ ++ [(someState, Q reply)])
        else
          True
  }}}.
Proof.
  iIntros (Φ) "(#Hsrv & Hwp) HΦ".
  wp_call.
  wp_apply wp_ref_of_zero; first done.
  iIntros (err_ptr) "Herr".
  wp_apply wp_ref_of_zero; first done.
  iIntros (ret_ptr) "Hret".
  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (args_ptr_ptr) "Hargs_ptr".
  wp_pure1_credit "Hlc1".
  wp_pure1_credit "Hlc2".

  wp_apply (wp_Server__withLock with "[$]").
  iIntros (??) "HH".
  iNamed "HH".
  iNamed "Hvol".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* case not leader: return error *)
    wp_store.
    iModIntro.
    iExists _.
    rewrite sep_exist_r.
    iExists _; iFrame "∗#".
    iIntros "$".
    iModIntro.
    wp_pures.
    wp_load.
    wp_pures.
    wp_load.
    change (slice.nil) with (slice_val Slice.nil).
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
  }
  wp_loadField.
  wp_apply ("Hwp" with "[$]").
  iClear "Hstate_sl".
  iClear "HP".
  iIntros (????) "(#Hstate_sl & #Hreply & #HP & Hupd)".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros "%Hno_overflow".
  wp_storeField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_allocStruct).
  { repeat econstructor. done. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "Hargs".
  wp_pure1_credit "Hlc".
  wp_store.

  iModIntro.
  iExists _.
  rewrite sep_exist_r.
  iExists _.
  instantiate (1:=paxosState.mk _ _ _ _ _). simpl; iFrame "∗Hstate_sl".

  (* start ghost reasoning *)
  iFrame "HP".
  iIntros "Hghost". iNamed "Hghost".
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
  iSplitR "Hlc1 Hlc2 HΦ Herr Hret Hreply Hargs Hargs_ptr".
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

  wp_pures.
  wp_load.
  wp_pures.
  iNamed "Hsrv".
  wp_loadField.
  wp_pures.

  (* set (newstate:=(next_state (default [] (last st.(mp_log).*1)) op)). *)
  iAssert (|={⊤}=> applyAsFollowerArgs.own args_ptr (applyAsFollowerArgs.mkC
                                               pst.(paxosState.epoch)
                                               (U64 (length log + 1))
                                               newstate
          ))%I with "[Hargs]" as "Hargs".
  {
    iNamed "Hargs".
    iExists _.
    iMod (readonly_alloc_1 with "epoch") as "$".
    simpl.
    rewrite Hlog.

    rewrite Z2Nat.id; last word.
    rewrite -Hno_overflow.
    unfold U64.
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
  rename reply into ret.
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ own_slice_small replies_sl ptrT 1 reply_ptrs ∗
                    "#Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; config,
                    ⌜reply_ptr = null⌝ ∨ □(∃ reply, readonly (applyAsFollowerReply.own reply_ptr reply 1) ∗
                                                   if decide (reply.(applyAsFollowerReply.err) = (U64 0)) then
                                                     is_accepted_lb γsrv' pst.(paxosState.epoch) (log ++ [(newstate, Q ret)])
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
  iMod (readonly_alloc_1 with "Hargs_ptr") as "#Hargs_ptr".

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
      iMod (readonly_load with "Hargs_ptr") as (?) "H".
      wp_load. iClear "H".
      wp_apply (wp_singleClerk__applyAsFollower with "[$His_ck]").
      {
        iFrame.
        iFrame "Hargs Hprop HP".
        iPureIntro.
        split.
        { rewrite app_length. simpl. word. }
        { simpl. rewrite fmap_app last_app /= //. }
      }
      iRename "Hreply" into "Hret".
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
        iFrame "∗".
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

        replace (<[int.nat i:=x2]> config) with (config) ; last first.
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
    wp_apply (wp_condWait with "[-HΦ Hlc1 Hlc2 Herr Hret]").
    {
      iFrame "#∗".
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

  set (I:=λ (i:u64), (
                 ∃ (W: gset nat),
                 "%HW_in_range" ∷ ⌜∀ s, s ∈ W → s < int.nat i⌝ ∗
                 "%HW_size_nooverflow" ∷ ⌜(size W) ≤ int.nat i⌝ ∗
                 "HnumSuccesses" ∷ numSuccesses_ptr ↦[uint64T] #(U64 (size W)) ∗
                 "#Hacc_lbs" ∷ ([∗ list] s ↦ γsrv' ∈ config, ⌜s ∈ W⌝ → is_accepted_lb γsrv' pst.(paxosState.epoch) (log ++ [(newstate, Q ret)]))
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
      iRename "Hreply" into "Hret".
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
        iExists (W ∪ {[ int.nat i ]}).
        iSplitR.
        { (* prove that the new set W is still in range *)
          replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
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
          destruct (decide (int.nat i ∈ W)).
          {
            exfalso.
            specialize (HW_in_range (int.nat i) e).
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
          assert (Z.of_nat (size W) < int.Z clerks_sl.(Slice.sz))%Z by word.
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
        replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
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
      replace (int.nat (word.add i (U64 1))) with (int.nat i + 1) by word.
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
    wp_load.
    wp_pures.

    iDestruct (big_sepL2_length with "Hreplies") as "%Hreplies_len_eq_conf".
    replace (int.nat replies_sl.(Slice.sz)) with (length config) in HW_in_range; last first.
    { word. }

    iDestruct (establish_committed_by with "[$Hacc_lbs]") as "Hcom".
    { done. }
    {
      assert (2 * size W >= int.Z (u64_instance.u64.(word.mul) 2 (size W)))%Z.
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
    iApply "HΦ".
    iModIntro.
    iFrame.
    simpl.
    destruct (decide _).
    {
      repeat iExists _.
      iFrame "∗ #".
    }
    {
      done.
    }
  }
  { (* error, too few successful applyAsFollower() RPCs *)
    wp_store. wp_pures.
    wp_load. wp_load. wp_pures.
    iApply "HΦ".
    iModIntro.
    iFrame.
  }
Qed.

(* TODO: copied from pb_apply_proof.v *)
Lemma prefix_app_cases {A} (σ σ':list A) e:
  σ' `prefix_of` σ ++ [e] →
  σ' `prefix_of` σ ∨ σ' = (σ++[e]).
Proof.
Admitted.

(* NOTE: might be more convenient to have a statemachine controlled by the user
   for which this library can call SetState and GetState. This library could
   have a parameterized state type, instead of list u8. *)
Lemma wp_Server__Apply (s:loc) (f:val) γst γ γsrv (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  is_state_inv γst γ -∗
  (∀ Ψ (oldstate:list u8) old_sl,
     (readonly (own_slice_small old_sl byteT 1 oldstate) ∗
      Pwf oldstate
      )-∗
     (∀ new_sl reply_sl (newstate reply:list u8),
        (readonly (own_slice_small new_sl byteT 1 newstate) ∗
         readonly (own_slice_small reply_sl byteT 1 reply) ∗
         □ Pwf newstate ∗
         (|={⊤∖↑N,∅}=> ∃ oldstate',
            own_state γst oldstate' ∗
            (⌜ oldstate' = oldstate ⌝ -∗ own_state γst newstate ={∅,⊤∖↑N}=∗
             (∀ ret_sl,
                readonly (own_slice_small ret_sl byteT 1 reply) -∗
                Φ (#0, slice_val ret_sl)%V)))
        ) -∗
        Ψ (slice_val new_sl, slice_val reply_sl)%V) -∗
     WP f (slice_val old_sl) {{ Ψ }}
  ) -∗
  (∀ (err:u64) reply_sl, ⌜ err ≠ U64 0 ⌝ → Φ (#err, slice_val reply_sl)%V) -∗
  WP  mpaxos.Server__Apply #s f {{ Φ }}
.
Proof using Type*.
  iIntros "#Hsrv #Hinv Hupd Hfail".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  iApply wp_fupd.
  wp_apply (wp_Server__apply_internal
      (λ reply, inv escrowN (
        (∀ ret_sl, readonly (own_slice_small ret_sl byteT 1 reply) -∗
                   Φ (#0, slice_val ret_sl)%V) ∨
          ghost_var γtok 1 ()
        )%I)
             with "[$Hsrv Hupd]").
  {
    rewrite /own_applyfn.
    iIntros (Ψ) "*".
    iIntros "Hsl HΨ".
    wp_apply ("Hupd" with "[$]").
    iIntros "* Hupd".
    iDestruct "Hupd" as "(#Hnew & #Hreply & #HP & Hupd)".
    iSpecialize ("HΨ" with "[-]").
    2: iApply "HΨ".
    iFrame "#".
    iInv "Hinv" as "HH" "Hclose".
    iDestruct "HH" as (?) "(>Hstate & >Hghost & #HQs)".
    iMod (fupd_mask_subseteq _) as "Hmask".
    2: iMod "Hupd" as (?) "[Hstate2 Hupd]".
    { rewrite /ghostN /appN /=. solve_ndisj. }
    iModIntro.
    iDestruct (own_valid_2 with "Hstate Hstate2") as %Hvalid.
    rewrite dfrac_agree_op_valid_L in Hvalid.
    destruct Hvalid as [_ Heq].
    rewrite Heq.
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
    iMod ("Hupd" with "[% //] Hstate2") as "Hupd".

    iAssert (|={↑escrowN}=> inv escrowN
                    ((∀ reply_sl0 : Slice.t, readonly (own_slice_small reply_sl0 byteT 1 reply) -∗ Φ (#0, reply_sl0)%V)
                     ∨ ghost_var γtok 1 ()))%I
            with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iLeft.
      iIntros.
      iApply "Hupd".
      iFrame "#".
    }

    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    2: iMod "Hinv2" as "#HΦ_inv".
    { rewrite /escrowN /=. solve_ndisj. }
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hstate]").
    {
      iNext.
      iExists _; iFrame.
      unfold get_state.
      rewrite fmap_app.
      rewrite last_snoc.
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
    iModIntro.
    done.
  }
  iIntros "* (Hcred & Hcred2 & Hpost)".

  destruct (decide (err = U64 0)).
  { (* no error *)
    subst.
    iDestruct "Hpost" as (???) "[#Hsl #Hghost_lb]".
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
      iFrame "#".
    }
  }
  {
    iIntros.
    iApply "Hfail".
    done.
  }
Qed.

End apply_proof.
