From Perennial.base_logic Require Import lib.saved_prop.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial Require Import replica.protocol replica.definitions
     replica.applybackup_proof replica.increasecommit_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section proof.

Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!pbG Σ}.

Lemma wp_Clerk__Apply γ γsrv ck op_sl q op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
is_Clerk ck γ γsrv -∗
own_slice_small op_sl byteT q op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_int_log γ ops ∗
  (⌜apply_postcond ops op⌝ -∗ own_int_log γ (ops ++ [op]) ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
            own_slice_small op_sl byteT q op_bytes -∗
                Φ (#(W64 0), slice_val reply_sl)%V)))
∗
(∀ (err:u64) unused_sl, ⌜err ≠ 0⌝ -∗ own_slice_small op_sl byteT q op_bytes -∗
                                     Φ (#err, (slice_val unused_sl))%V )) -∗
WP Clerk__Apply #ck (slice_val op_sl) {{ Φ }}.
Proof.
  intros Henc.
  iIntros "#Hck Hop_sl".
  iIntros "#HΦ".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_loadField.
  rewrite is_pb_rpcs_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hop_sl Hrep").
  {
    iDestruct "Hsrv" as "[_ [_ [_ [_ [$ _]]]]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold Apply_spec.
    iExists _.
    iSplitR; first done.
    simpl.
    iSplit.
    {
      iModIntro.
      iLeft in "HΦ".
      iMod "HΦ".
      iModIntro.
      iDestruct "HΦ" as (?) "[Hlog HΦ]".
      iExists _.
      iFrame.
      iIntros "% Hlog".
      iMod ("HΦ" with "[//] Hlog") as "HΦ".
      iModIntro.
      iIntros (? Hreply_enc) "Hop".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Hreply_enc.
      wp_apply (ApplyReply.wp_Decode with "[Hrep_sl]").
      { iFrame. iPureIntro. done. }
      iIntros (reply_ptr) "Hreply".
      wp_pures.
      iNamed "Hreply".
      wp_loadField.
      wp_loadField.
      wp_pures.
      iModIntro.
      iApply ("HΦ" with "Hrepy_ret_sl Hop").
    }
    { (* Apply failed for some reason, e.g. node is not primary *)
      iIntros (??).
      iModIntro.
      iIntros (Herr_nz ? Hreply_enc) "Hop".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      iIntros.
      wp_pures.
      wp_load.
      wp_apply (ApplyReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iNamed "Hreply".
      wp_pures.
      wp_loadField.
      wp_loadField.
      iRight in "HΦ".
      wp_pures.
      iApply ("HΦ" with "[] Hop").
      done.
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      wp_load.
      exfalso. done.
    }
    iRight in "HΦ".
    replace (slice.nil) with (slice_val Slice.nil) by done.
    wp_pures.
    iApply ("HΦ" with "[] [$]").
    done.
  }
Qed.

(*
Definition entry_pred_conv (σ : list (OpType * (list OpType → iProp Σ)))
  (σgnames : list (OpType * gname)) : iProp Σ :=
    ⌜ σ.*1 = σgnames.*1 ⌝ ∗
    [∗ list] k↦Φ;γ ∈ snd <$> σ; snd <$> σgnames, saved_pred_own γ DfracDiscarded Φ.

Definition is_ghost_lb' γ σ : iProp Σ :=
  ∃ σgnames, is_ghost_lb γ σgnames ∗ entry_pred_conv σ σgnames. *)

Lemma apply_eph_primary_step γ γsrv ops canBecomePrimary epoch committedNextIndex op Q :
  apply_postcond (get_rwops ops) op →
  (|={⊤∖↑ghostN,∅}=> ∃ σ, own_pb_log γ.(s_pb) σ ∗
    (⌜apply_postcond (get_rwops σ) op⌝ -∗  own_pb_log γ.(s_pb) (σ ++ [(op, Q)]) ={∅,⊤∖↑ghostN}=∗ True)) -∗
  £ 1 -∗
  own_Primary_ghost_f γ γsrv canBecomePrimary true epoch committedNextIndex ops
  ={⊤∖↑pbAofN}=∗
  own_Primary_ghost_f γ γsrv canBecomePrimary true epoch committedNextIndex (ops ++ [(op, Q)]) ∗
  is_proposal_lb γ.(s_pb) epoch (ops ++ [(op, Q)]) ∗
  is_proposal_facts γ.(s_pb) epoch (ops ++ [(op, Q)]) ∗
  is_proposal_facts_prim γ.(s_prim) epoch (ops ++ [(op, Q)])
.
Proof.
  iIntros (?) "Hupd Hlc Hprim".
  rewrite /own_Primary_ghost_f /tc_opaque.
  iNamed "Hprim".
  iMod (fupd_mask_subseteq _);
  last iMod (ghost_propose with "Hlc Hprim [Hupd]") as "(Hprim & #? & #?)".
  { solve_ndisj. }
  {
    iMod "Hupd" as (?) "[? Hupd]".
    iModIntro.
    iExists _; iFrame.
    iIntros (?); subst. (* XXX: This is the point of having σ = ops? *)
    iApply "Hupd".
    done.
  }
  iDestruct (is_proposal_facts_prim_mono with "Hprim_facts") as "#$".
  { by apply prefix_app_r. }
  by iFrame "∗#".
Qed.

Lemma apply_eph_step γ γsrv st op Q :
  apply_postcond (get_rwops st.(server.ops_full_eph)) op →
  st.(server.isPrimary) = true →
  st.(server.sealed) = false →
  £ 1 -∗
  (|={⊤∖↑ghostN,∅}=> ∃ σ, own_pb_log γ.(s_pb) σ ∗
        (⌜apply_postcond (get_rwops σ) op⌝ -∗ own_pb_log γ.(s_pb) (σ ++ [(op, Q)]) ={∅,⊤∖↑ghostN}=∗ True)) -∗
  own_Server_ghost_eph_f st γ γsrv
  ={⊤∖↑pbAofN}=∗
  own_Server_ghost_eph_f (st <| server.ops_full_eph := st.(server.ops_full_eph) ++ [(op, Q)] |>)
                              γ γsrv ∗
  is_proposal_lb γ.(s_pb) st.(server.epoch) (st.(server.ops_full_eph) ++ [(op, Q)]) ∗
  is_proposal_facts γ.(s_pb) st.(server.epoch) (st.(server.ops_full_eph) ++ [(op, Q)]) ∗
  is_proposal_facts_prim γ.(s_prim) st.(server.epoch) (st.(server.ops_full_eph) ++ [(op, Q)]) ∗
  is_epoch_lb γsrv.(r_pb) st.(server.epoch)
.
Proof.
  intros ? Hprim Hunsealed.
  iIntros "Hlc Hupd Hghost".
  iNamed "Hghost".
  rewrite /own_Server_ghost_eph_f /tc_opaque /=.
  iNamed "Hghost".
  rewrite Hprim.
  iMod (apply_eph_primary_step with "Hupd Hlc Hprimary") as "(Hprimary & #? & #? & #?)".
  { done. }
  by iFrame "∗%#".
Qed.

Definition own_slice_elt {V} {H:IntoVal V} (sl:Slice.t) (idx:u64) typ q (v:V) : iProp Σ :=
  (sl.(Slice.ptr) +ₗ[typ] (uint.Z idx)) ↦[typ]{q} (to_val v).

Lemma slice_elements_split {V} {H:IntoVal V} sl typ q (l:list V):
  own_slice_small sl typ q l -∗
  [∗ list] i ↦ v ∈ l, own_slice_elt sl i typ q v.
Proof.
  iIntros "Hsl".
  rewrite /own_slice_small /slice.own_slice_small.
  unfold own_slice_elt.
  destruct sl. simpl.
  iDestruct "Hsl" as "(Hsl & #Hsz & #Hcap)".
  iAssert (⌜uint.Z sz <= 2^64⌝%Z)%I with "[]" as "#Hsz2".
  { iPureIntro. word. }
  iClear "Hcap".
  iRevert "Hsz2".
  iInduction l as [|] "IH" forall (ptr sz).
  { iIntros. by iApply big_sepL_nil. }
  iIntros.
  unfold list.untype.
  rewrite fmap_cons.
  iDestruct (array_cons with "Hsl") as "[Helt Hsl]".

  iSplitL "Helt".
  {
    unfold own_slice_elt.
    replace (ty_size typ * uint.Z 0%nat)%Z with (0%Z) by word.
    rewrite loc_add_0.
    iFrame.
  }
  iDestruct "Hsz" as "%".
  iSpecialize ("IH" $! (ptr +ₗ[typ] 1) with "[] [Hsl] []").
  {
    iPureIntro.
    rewrite cons_length in H1.
    instantiate (1:=(word.sub sz 1)).
    word.
  }
  { iExactEq "Hsl"; repeat f_equal; word. }
  {
    iPureIntro. generalize (word.sub sz 1).
    intros. word.
  }
  iApply (big_sepL_impl with "[$]").
  iModIntro. iIntros (???) "H".
  iExactEq "H". f_equal.
  rewrite loc_add_assoc.
  repeat f_equal.
  replace (uint.Z (S k)) with (1 + uint.Z k)%Z.
  { word. }
  { rewrite cons_length fmap_length in H1.
    apply lookup_lt_Some in H2. word.
  }
Qed.

Lemma wp_SliceSet_elt {V typ} `{!IntoVal V} `{!IntoValForType V typ} (sl:Slice.t) (i:u64) (v v':V) :
  {{{
        own_slice_elt sl i typ (DfracOwn 1) v
  }}}
      SliceSet typ (slice_val sl) #i (to_val v')
  {{{
        RET #(); own_slice_elt sl i typ (DfracOwn 1) v'
  }}}.
Proof.
  iIntros (?) "Hown HΦ".
  unfold SliceSet.
  wp_pures.
  unfold own_slice_elt.
  wp_apply (wp_slice_ptr).
  wp_pures.
  wp_apply (wp_StoreAt with "[$Hown]").
  { apply to_val_ty. }
  iFrame.
Qed.

Lemma wp_forSlice' {V} {H:IntoVal V} ϕ I sl ty q (l:list V) (body:val) :
  (∀ (i:u64) (v:V),
    {{{
          ⌜uint.nat i < length l⌝ ∗ ⌜l !! (uint.nat i) = Some v⌝ ∗ ϕ (uint.nat i) v ∗ I i
    }}}
      body #i (to_val v)
    {{{
          RET #(); I (word.add i 1)
    }}}
  ) -∗
  {{{
        own_slice_small sl ty q l ∗
        ([∗ list] i ↦ v ∈ l, ϕ i v) ∗
        I 0
  }}}
    forSlice ty body (slice_val sl)
  {{{
        RET #(); I (length l)
  }}}
.
Proof.
  iIntros "#Hwp".
  iIntros (?) "!# (Hsl & Hl & HI) HΦ".
  iDestruct (own_slice_small_sz with "Hsl") as %Hsz.
  wp_apply (wp_forSlice (λ i, I i ∗ [∗ list] j ↦ v ∈ (drop (uint.nat i) l), ϕ (j + uint.nat i) v) %I
             with "[] [$Hsl Hl HI]").
  2: { rewrite drop_0.
       replace (uint.nat (W64 0)) with (0) by word.
       setoid_rewrite <- plus_n_O. iFrame. }
  {
    clear Φ.
    iIntros (???Φ) "!# ([HI Hl] & % & %) HΦ".
    assert ((drop (uint.nat i) l) !! 0 = Some x) as ?.
    {
      rewrite lookup_drop. rewrite <- H1.
      f_equal. word.
    }
    iDestruct (big_sepL_take_drop _ _ 1 with "Hl") as "[Hϕ Hl]".
    wp_apply ("Hwp" with "[HI Hϕ]").
    {
      iFrame "∗%".
      iSplit. 1: iPureIntro; word.
      iDestruct (big_sepL_lookup_acc with "Hϕ") as "[H _]".
      {
        rewrite lookup_take.
        { done. }
        lia.
      }
      iExactEq "H". repeat f_equal.
    }
    iIntros "HI".
    iApply "HΦ".
    iFrame.
    rewrite drop_drop.
    replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) by word.
    iApply (big_sepL_impl with "Hl").
    iModIntro.
    iIntros.
    replace (k + (uint.nat i + 1)) with (1 + k + uint.nat i) by word.
    done.
  }
  iIntros "[[HI _] _]".
  iApply "HΦ".
  rewrite Hsz.
  iExactEq "HI". f_equal. word.
Qed.

Lemma establish_committed_log_fact γ epoch σ :
  committed_by γ.(s_pb) epoch σ -∗
  is_proposal_lb γ.(s_pb) epoch σ -∗
  □ committed_log_fact γ epoch σ.
Proof.
  iIntros "#Hcom #Hprop_lb".
  iModIntro.
  iIntros (????) "#Hprop_lb2 #Hprop_facts2".
  destruct (decide (uint.nat epoch = uint.nat epoch')).
  { assert (epoch = epoch'); last subst.
    { apply word.unsigned_inj. word. }
    subst. destruct H0; last by lia. by iDestruct (fmlist_ptsto_lb_longer with "Hprop_lb Hprop_lb2") as %?.
  }
  iDestruct "Hprop_facts2" as "[Hmax _]".
  iApply "Hmax".
  2: iFrame "#".
  iPureIntro. word.
Qed.

Local Instance a x y : Decision (apply_postcond x y).
Proof. apply pb_record.(Sm.apply_postcond_dec). Qed.

Lemma become_backup st γ γsrv :
own_Server_ghost_eph_f st γ γsrv -∗
own_Server_ghost_eph_f (st <| server.isPrimary := false |>) γ γsrv
.
Proof.
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed 1.
  repeat iExists _; iFrame "∗#%".
  rewrite /own_Primary_ghost_f /tc_opaque /=.
  iNamed "Hprimary".
  iFrame "∗#".
Qed.

Lemma wp_Server__Apply_internal (s:loc) γ γsrv op_sl op_bytes op Q :
  {{{
        is_Server s γ γsrv ∗
        readonly (own_slice_small op_sl byteT (DfracOwn 1) op_bytes) ∗
        ⌜has_op_encoding op_bytes op⌝ ∗
        (£ 1 -∗ £ 1 -∗ |={⊤∖↑ghostN,∅}=> ∃ σ, own_pb_log γ.(s_pb) σ ∗
          (⌜apply_postcond (get_rwops σ) op⌝ -∗ own_pb_log γ.(s_pb) (σ ++ [(op, Q)]) ={∅,⊤∖↑ghostN}=∗ True))
  }}}
    Server__Apply #s (slice_val op_sl)
  {{{
        reply_ptr reply, RET #reply_ptr; £ 1 ∗ £ 1 ∗ £ 1 ∗ ApplyReply.own_q reply_ptr reply ∗
        if (decide (reply.(ApplyReply.err) = 0%Z)) then
          ∃ opsfull,
            let ops := (get_rwops opsfull) in
            ⌜reply.(ApplyReply.ret) = compute_reply ops op⌝ ∗
            is_pb_log_lb γ.(s_pb) (opsfull ++ [(op, Q)])
        else
          True
  }}}
.
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iDestruct "Hpre" as "(#Hsl & %Hghostop_op & Hupd)".
  iNamed "His".
  rewrite /Server__Apply.
  wp_pure1_credit "Hcred3".
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (reply_ptr) "Hreply".
  iDestruct (struct_fields_split with "Hreply") as "HH".
  iNamed "HH".
  wp_pure1_credit "Hlc1".
  wp_pure1_credit "Hlc2".
  simpl.
  replace (slice.nil) with (slice_val (Slice.nil)) by done.
  wp_storeField.

  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  iNamed "Hvol".
  wp_pure1_credit "Hcred1".
  wp_pure1_credit "Hcred2".
  iSpecialize ("Hupd" with "Hlc1 Hlc2").
  wp_loadField.
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* return error "not primary" *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Err Reply Hcred1 Hcred2 Hcred3]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      iFrame "Hstate ∗#"; iFrame "%".
    }
    wp_pures.
    wp_storeField.
    iApply "HΦ".
    iFrame.
    iSplitL "Err".
    {
      instantiate (1:=(ApplyReply.mkC _ _)).
      iExists _.
      iFrame.
      iApply own_slice_small_nil.
      done.
    }
    done.
  }
  wp_loadField.

  wp_if_destruct.
  { (* return ESealed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Err Reply Hcred1 Hcred2 Hcred3]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      rewrite Heqb0 Heqb.
      iFrame "∗#"; iFrame "%".
    }
    wp_pures.
    wp_storeField.
    iApply ("HΦ" $! _ (ApplyReply.mkC 1 [])).
    iFrame.
    iExists (DfracOwn 1).
    iApply own_slice_small_nil.
    done.
  }

  (* XXX: this is ultimately to support the statemachine code making
     "assumptions" by providing a non-trivial post-condition. E.g. if the state
     machine apply() function loops forever when integer overflow occurs.
   *)
  destruct (decide (apply_postcond (get_rwops st.(server.ops_full_eph)) op)).
  2: { (* case: doomed proof *)
    iDestruct (is_StateMachine_acc_apply with "HisSm") as "HH".
    iNamed "HH". wp_loadField. wp_loadField.

    wp_apply ("HapplySpec" with "[HisSm $Hstate $Hsl]").
    { iSplitL ""; first done. iIntros (?). exfalso. done. }
    iIntros (???) "(% & _)". exfalso. done.
  }

  (* make ephemeral proposal *)
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (⊤∖↑pbAofN)) as "Hmask".
  { set_solver. }
  iMod (apply_eph_step with "Hlc Hupd HghostEph") as "(HghostEph & #Hprop_lb & #Hprop_facts & #Hprim_facts & #Hepoch_lb)".
  { done. }
  { done. }
  { done. }
  iMod "Hmask" as "_".
  iModIntro.

  iDestruct (is_StateMachine_acc_apply with "HisSm") as "HH".
  iNamed "HH".
  wp_loadField.
  wp_loadField.

  wp_apply ("HapplySpec" with "[HisSm $Hstate $Hsl]").
  {
    iSplitL ""; first done.
    iIntros "_ Hghost".
    iMod (applybackup_step with "Hprop_lb Hprop_facts Hprim_facts Hghost") as "Hghost".
    { by rewrite last_snoc. }
    { unfold get_rwops. rewrite fmap_app. rewrite app_length. done. }
    iModIntro.
    rewrite /get_rwops fmap_app /=.
    iExact "Hghost".
  }
  iIntros (reply_sl q waitFn) "(%Hop_post & Hreply & Hstate & HwaitSpec)".

  wp_pures.
  wp_storeField.
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
  wp_pures.
  wp_loadField.

  wp_apply (release_spec with "[-HΦ Hreply Err Reply Hcred1 Hcred2 Hcred3 HwaitSpec]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    repeat (iExists _).
    iSplitR "HghostEph"; last iFrame.
    repeat (iExists _).
    rewrite /= Heqb Heqb0 /=.
    replace (get_rwops (st.(server.ops_full_eph) ++ [(op, Q)])) with (get_rwops st.(server.ops_full_eph) ++ [op]); last first.
    {
      unfold get_rwops. rewrite fmap_app. done.
    }
    iFrame "∗#".
    rewrite app_length /=.
    iSplitL.
    {
      iApply to_named.
      iExactEq "HnextIndex".
      repeat f_equal.
      unfold no_overflow in HnextIndexNoOverflow.
      word.
    }
    iPureIntro.
    {
      unfold no_overflow in HnextIndexNoOverflow |- *.
      word.
    }
  }

  wp_pures.

  wp_apply (wp_NewWaitGroup_free).
  iIntros (wg) "Hwg".
  wp_pures.

  wp_apply (wp_allocStruct).
  { econstructor; eauto. }
  iIntros (Hargs) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "epoch") as "#Hargs_epoch".
  iMod (readonly_alloc_1 with "index") as "#Hargs_index".
  iMod (readonly_alloc_1 with "op") as "#Hargs_op".
  wp_pures.
  rewrite Heqb.
  iDestruct "Hprimary" as "[%Hbad|Hprimary]"; first by exfalso.
  iNamed "Hprimary".
  iMod (readonly_load with "Hclerkss_sl") as (?) "Hclerkss_sl2".

  iDestruct (own_slice_small_sz with "Hclerkss_sl2") as %Hclerkss_sz.

  wp_apply (wp_RandomUint64).
  iIntros (randint) "_".
  wp_apply (wp_slice_len).
  wp_pures.
  set (clerkIdx:=(word.modu randint clerks_sl.(Slice.sz))).

  assert (uint.nat clerkIdx < length clerkss) as Hlookup_clerks.
  { (* FIXME: better lemmas about mod? *)
    rewrite Hclerkss_sz.
    unfold clerkIdx.
    rewrite Hclerkss_len in Hclerkss_sz.
    replace (clerks_sl.(Slice.sz)) with (W64 (32)); last first.
    {
      unfold numClerks in Hclerkss_sz.
      word.
    }
    enough (uint.Z randint `mod` 32 < uint.Z 32)%Z.
    { word. }
    apply Z.mod_pos_bound.
    word.
  }

  assert (∃ clerks_sl_inner, clerkss !! uint.nat clerkIdx%Z = Some clerks_sl_inner) as [clerks_sl_inner Hclerkss_lookup].
  {
    apply list_lookup_lt.
    rewrite Hclerkss_len.
    word.
  }

  wp_apply (wp_SliceGet with "[$Hclerkss_sl2]").
  { done. }
  iIntros "Hclerkss_sl2".
  wp_pures.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (errs_sl) "Herrs_sl".
  wp_pures.
  iApply fupd_wp.
  iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
  { set_solver. }
  iMod (free_WaitGroup_alloc pbN _
          (λ i,
            ∃ (err:u64) γsrv',
            ⌜backups !! uint.nat i = Some γsrv'⌝ ∗
            readonly (own_slice_elt errs_sl i uint64T (DfracOwn 1) err) ∗
            □ if (decide (err = W64 0)) then
              is_accepted_lb γsrv'.(r_pb) st.(server.epoch) (st.(server.ops_full_eph) ++ [_])
            else
              True
          )%I
         with "Hwg") as (γwg) "Hwg".
  iMod "Hmask".
  iModIntro.

  iDestruct (big_sepL_lookup_acc with "Hclerkss_rpc") as "[Hclerks_rpc _]".
  { done. }
  iNamed "Hclerks_rpc".

  iDestruct (own_slice_to_small with "Herrs_sl") as "Herrs_sl".
  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (own_slice_small_sz with "Hclerks_sl2") as %Hclerks_sz.

  wp_apply (wp_forSlice' _ (λ j, (own_WaitGroup pbN wg γwg j _))%I with "[] [$Hwg Herrs_sl $Hclerks_sl2]").
  2: {
    iDestruct (slice_elements_split with "Herrs_sl") as "Herrs".
    iDestruct (big_sepL2_const_sepL_r _ clerks with "[$Herrs]") as "Herrs".
    { iPureIntro. by rewrite replicate_length. }
    rewrite big_sepL2_replicate_r; last done.
    iDestruct (big_sepL2_to_sepL_1 with "Hclerks_rpc") as "H2".
    iDestruct (big_sepL_sep with "[$Herrs]") as "$".
    { iFrame "H2". }
  }
  {
    iIntros (i ck).
    simpl.
    clear Φ.
    iIntros (Φ) "!# (% & %Hlookup & Hϕ & Hwg) HΦ".
    iRename "Hepoch_lb" into "Hlocal_epoch_lb".
    iDestruct "Hϕ" as "(Herr & (% & (% & #Hck & #Hepoch_lb)))".
    wp_pures.
    wp_apply (wp_WaitGroup__Add with "[$Hwg]").
    { rewrite Hclerks_sz in H. word. }
    iIntros "[Hwg Hwg_tok]".
    wp_pures.
    iDestruct (own_WaitGroup_to_is_WaitGroup with "[$Hwg]") as "#His_wg".
    wp_apply (wp_fork with "[Hwg_tok Herr]").
    {
      iNext.
      wp_pures.
      wp_forBreak_cond.
      wp_pures.

      wp_apply (wp_Clerk__ApplyAsBackup with "[$Hck $Hepoch_lb]").
      {
        iFrame "Hprop_lb Hprop_facts #".
        iPureIntro.
        rewrite last_app.
        simpl.
        split; eauto.
        split; eauto.
        rewrite /no_overflow in Hno_overflow HnextIndexNoOverflow.
        split.
        { rewrite /get_rwops fmap_app app_length. simpl.
          rewrite HnextIndexNoOverflow /get_rwops.
          word.
        }
        word.
      }
      iIntros (err) "#Hpost".

      wp_pures.
      wp_bind (#(bool_decide _) || _)%E.
      wp_apply (wp_or with "[]"); first iAccu.
      { wp_pures. by iModIntro. }
      { iIntros (_) "_". wp_pures. by iModIntro. }
      iIntros "_".
      wp_if_destruct.
      {
        wp_pures.
        iLeft.
        iFrame "∗".
        by iPureIntro.
      }

      iEval (replace (#err) with (to_val err) by done).
      replace (W64 (uint.nat i)) with (i) by word.
      wp_apply (wp_SliceSet_elt with "Herr").
      iIntros "Herr".
      wp_pures.
      iRight.
      iModIntro.
      iSplitR; first by iPureIntro.

      iMod (readonly_alloc_1 with "Herr") as "#Herr_ptr".
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
    iFrame "Hwg".
  }
  iIntros "Hwg".
  wp_pures.

  wp_apply (wp_WaitGroup__Wait with "Hwg").
  iIntros "#Hwg_post".
  wp_pures.

  wp_apply "HwaitSpec".
  iIntros "Hprimary_acc_lb".
  iDestruct "Hprimary_acc_lb" as "(_ & _ & #Hprimary_acc_lb)".

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
              "%Hj_ub" ∷ ⌜uint.nat j ≤ length clerks⌝ ∗
              "Herr" ∷ err_ptr ↦[uint64T] #err ∗
              "#Hrest" ∷ □ if (decide (err = (W64 0)%Z)) then
                (∀ (k:u64) γsrv', ⌜uint.nat k ≤ uint.nat j⌝ -∗ ⌜conf !! (uint.nat k) = Some γsrv'⌝ -∗
                  is_accepted_lb γsrv'.(r_pb) st.(server.epoch) (st.(server.ops_full_eph) ++ [_]))
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
      replace (uint.nat 0%Z) with (0) in H by word.
      replace (uint.nat k) with (0) in H0 by word.
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
  iDestruct (own_slice_small_sz with "Htemp") as %Hclerk_sz.
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
    { exfalso.
      rewrite Hclerks_sz in Hbad.
      revert Hbad.
      eassert (uint.nat (uint.nat (_:u64)) = uint.nat (_:u64)) as ->.
      { instantiate (1:=clerks_sl_inner.(Slice.sz)).
        word. }
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
        assert (uint.nat k ≤ uint.nat j ∨ uint.nat k = uint.nat (word.add j 1%Z)) as [|].
        {
          replace (uint.nat (word.add j 1%Z)) with (uint.nat j + 1) in * by word.
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
            replace (uint.nat (word.add j 1%Z)) with (S (uint.nat j)) in H0 by word.
            unfold conf in H0.
            rewrite lookup_cons in H0.
            rewrite H0 in HbackupLookup.
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
      word.
    }
  }
  iRight.
  iModIntro.
  iSplitL ""; first done.
  wp_pure1_credit "Hlc3".
  wp_load.
  wp_pures.

  wp_storeField.
  wp_load.

  destruct (decide (err = 0%Z)); last first.
  {
    wp_pures.
    rewrite bool_decide_false; last naive_solver.
    wp_pures.

    wp_loadField.
    wp_apply (acquire_spec with "[$]").
    iIntros "[Hlocked Hown]".
    iNamed "Hown".
    iClear "HopAppliedConds_conds HcommittedNextIndex_is_cond HisSm HisPrimary_is_cond".
    iNamed "Hvol".
    wp_loadField.
    wp_if_destruct.
    {
      wp_storeField.
      wp_loadField.
      iDestruct (become_backup with "HghostEph") as "HghostEph".
      wp_apply (release_spec with "[-HΦ Hreply Err Reply Hcred1 Hcred2 Hcred3]").
      { iFrame "∗#".
        repeat iExists _; iSplitR "HghostEph"; last iFrame.
        repeat iExists _; iFrame "∗#".
        iFrame "%". by iLeft.
      }
      wp_pures.
      iApply ("HΦ" $! reply_ptr (ApplyReply.mkC _ _)).
      iFrame.
      simpl.
      rewrite decide_False; last naive_solver. done.
    }
    wp_loadField.
    wp_apply (release_spec with "[-HΦ Hreply Err Reply Hcred1 Hcred2 Hcred3]").
    { iFrame "∗#".
      repeat iExists _; iSplitR "HghostEph"; last iFrame.
      repeat iExists _; iFrame "∗#".
      iFrame "%".
    }
    wp_pures.
    iApply ("HΦ" $! reply_ptr (ApplyReply.mkC _ _)).
    iFrame.
    simpl.
    rewrite decide_False; last naive_solver. done.
  }
  (* otherwise, no error *)
  iAssert (committed_by γ.(s_pb) st.(server.epoch) _) with "[]" as "#HcommitBy".
  {
    iExists _; iFrame "#".
    iIntros.
    rewrite elem_of_list_fmap in H.
    destruct H as (? & ? & H).
    subst.
    apply elem_of_list_lookup_1 in H as [k Hlookup_conf].
    replace (uint.nat j) with (length clerks); last first.
    { word. }
    epose proof (lookup_lt_Some _ _ _ Hlookup_conf) as HH.
    replace (k) with (uint.nat k) in *; last first.
    {
      rewrite cons_length /= in HH.
      rewrite -Hclerks_conf in HH.
      (* FIXME: why manually rewrite? *)
      word.
    }
    iApply ("Hrest" $! k _).
    { iPureIntro.
      unfold conf in HH.
      rewrite cons_length in HH.
      rewrite Hclerks_conf.
      clear -HH.
      lia. }
    { done. }
  }
  iMod (ghost_commit with "His_repl_inv HcommitBy Hprop_lb Hprop_facts") as "#Hcommit".

  wp_pures.
  rewrite bool_decide_true; last naive_solver.
  wp_pures.
  wp_apply (wp_Server__IncreaseCommit with "[] [-] []").
  { repeat iExists _. iFrame "Hconf_inv HconfCk_is #". }
  { instantiate (1:=(λ _, True)%I).
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iSplitL.
    { instantiate (1:=ApplyReply.mkC _ _). repeat iExists _; iFrame. done. }
    simpl.
    destruct (decide _); last first.
    { exfalso. done. }
    iExists _; iFrame "Hcommit".
    done.
  }
  iExists _, _.
  iFrame "#".
  iSplitL.
  { iPureIntro. rewrite fmap_length app_length /=.
    unfold no_overflow in *.
    rewrite fmap_length in Hno_overflow HnextIndexNoOverflow.
    word.
  }
  {
    iSplitL; last done.
    iApply establish_committed_log_fact.
    1-2: iFrame "#".
  }
  Unshelve. 1: exact (DfracOwn 1). exact True%I. (* this is from the "doomed" path in the proof. *)
Qed.

Lemma wp_Server__Apply (s:loc) γ γsrv op_sl op (enc_op:list u8) Ψ (Φ: val → iProp Σ) :
  is_Server s γ γsrv -∗
  readonly (own_slice_small op_sl byteT (DfracOwn 1) enc_op) -∗
  (∀ reply, Ψ reply -∗ ∀ reply_ptr, ApplyReply.own_q reply_ptr reply -∗ Φ #reply_ptr) -∗
  Apply_core_spec γ op enc_op Ψ -∗
  WP (Server__Apply #s (slice_val op_sl)) {{ Φ }}
.
Proof using Type*.
  iIntros "#Hsrv #Hop_sl".
  iIntros "HΨ HΦ".
  iApply (wp_frame_wand with "HΨ").
  iDestruct "HΦ" as "(%Hop_enc & #Hupd & Hfail_Φ)".
  iMod (ghost_var_alloc (())) as (γtok) "Htok".
  set (OpPred := 
(λ ops, inv escrowN (
        Ψ (ApplyReply.mkC 0 (compute_reply ops op)) ∨
          ghost_var γtok 1 ()
        ))).

  iMod (saved_pred_alloc OpPred DfracDiscarded) as (γghost_op) "#Hsaved"; first done.
  iApply wp_fupd.
  wp_apply (wp_Server__Apply_internal _ _ _ _ _ op γghost_op
             with "[$Hsrv $Hop_sl Hupd]").
  {
    iSplitR; first by iPureIntro.
    iIntros "Hlc Hlc2".
    iNamed "Hsrv".
    iDestruct (propose_rw_op_valid _ _ _ _
                                   (λ σ, apply_postcond (get_rwops σ) op)
                with "Hlc [$] [Hupd]") as "$".
    iInv "HhelpingInv" as "HH" "Hclose".
    iDestruct "HH" as (?) "(Hghost & >Hlog & #HQs)".
    iDestruct "Hghost" as (σgnames) "(>Hghost&>%Hfst_eq&#Hsaved')".
    iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
    { solve_ndisj. }
    iMod "Hupd".
    iModIntro.
    iDestruct "Hupd" as (σ0) "[Hlog2 Hupd]".
    iDestruct (own_valid_2 with "Hlog Hlog2") as %Hvalid.
    apply mono_list_auth_dfrac_op_valid_L in Hvalid.
    destruct Hvalid as [_ <-].
    iExists _; iFrame.
    iIntros "%Hpost Hghost".
    iMod (own_update_2 with "Hlog Hlog2") as "Hlog".
    {
      rewrite -mono_list_auth_dfrac_op.
      rewrite dfrac_op_own.
      rewrite Qp.half_half.
      apply mono_list_update.
      instantiate (1:=_ ++ [op]).
      by apply prefix_app_r.
    }
    iEval (rewrite -Qp.half_half -dfrac_op_own mono_list_auth_dfrac_op) in "Hlog".
    iDestruct "Hlog" as "[Hlog Hlog2]".
    iMod ("Hupd" with "[%] Hlog2") as "Hupd".
    { rewrite /get_rwops Hfst_eq. done. }

    iAssert (|={↑escrowN}=> inv escrowN ((Ψ (ApplyReply.mkC 0 (compute_reply (get_rwops opsfullQ) op)))
                                  ∨ ghost_var γtok 1 ()))%I
            with "[Hupd]" as "Hinv2".
    {
      iMod (inv_alloc with "[-]") as "$"; last done.
      iNext.
      iIntros.
      iLeft.
      iIntros.
      iApply "Hupd".
    }
    iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq (↑escrowN)) as "Hmask".
    { solve_ndisj. }
    iMod "Hinv2" as "#HΦ_inv".
    iMod "Hmask".

    iMod ("Hclose" with "[HQs Hghost Hlog]").
    {
      iNext.
      iExists (opsfullQ ++ [(op, OpPred)]); iFrame.
      iSplitR.
      { iSplitL.
        { iPureIntro. rewrite ?fmap_app /=. congruence. }
        rewrite ?fmap_app. iApply big_sepL2_app.
        { iFrame "Hsaved'". }
        iApply big_sepL2_singleton. iFrame "Hsaved".
      }
      rewrite /get_rwops fmap_app.
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
        assert (opsfullQ = opsPrePre) as ->.
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
        { eapply (suffix_snoc_inv_1 _ _ _ opsPrePre). rewrite -H0.
          done. }
        simpl.
        unfold OpPred.
        iFrame "#".
      }
    }
    done.
  }
  iIntros (err reply).
  iIntros "(Hcred & Hcred2 & Hcred3 & Hreply & Hpost)".
  destruct (decide (reply.(ApplyReply.err) = W64 0)).
  { (* no error *)
    iNamed "Hreply".
    rewrite e.
    iDestruct "Hpost" as (?) "(%Hrep & #Hghost_lb)".
    rewrite Hrep.
    iNamed "Hsrv".
    iInv "HhelpingInv" as "HH" "Hclose".
    {
      iDestruct "HH" as (?) "(Hghost & >Hlog & #HQs)".
      iDestruct "Hghost" as (σgnames) "(>Hghost&>%Hfst_eq&#Hsaved')".
      iApply (lc_fupd_add_later with "Hcred").
      iNext.
      iMod (own_pre_log_get_ineq with "[$] Hghost Hghost_lb") as "[Hghost %Hvalid]".
      { solve_ndisj. }

      destruct Hvalid as (σtail&Hvalid').
      subst.
      iDestruct (big_sepL2_length with "Hsaved'") as %Hlen.
      rewrite ?fmap_length in Hlen.
      assert (∃ σ0a op' Q' σ0b,
                 opsfullQ = σ0a ++ [(op', Q')] ++ σ0b ∧
                 length σ0a = length opsfull ∧
                 length σ0b = length σtail) as (σ0a&op'&Q'&σ0b&Heq0&Hlena&Hlenb).
      {
        destruct (nth_error opsfullQ (length opsfull)) as [(op', Q')|] eqn:Hnth; last first.
        { apply nth_error_None in Hnth. rewrite ?app_length /= in Hlen. lia. }
        edestruct (nth_error_split opsfullQ (length opsfull)) as (l1&l2&Heq&Hlen'); eauto.
        eexists l1, _, _, l2. rewrite Heq /=; split_and!; eauto.
        rewrite Heq ?app_length /= in Hlen. rewrite Hlen' in Hlen. clear -Hlen.
        (* weird, lia fails directly but if you replace lengths with a nat then it works... *)
        remember (length l2) as k.
        remember (length σtail) as k'. rewrite Heqk in Hlen. lia.
      }

      iDestruct ("HQs" $! (σ0a ++ [(op', Q')]) _ (_, _) with "[] []") as "#HQ".
      { rewrite Heq0. iPureIntro; eexists; eauto. rewrite app_assoc.  done. }
      { done. } 
      simpl.
      iMod ("Hclose" with "[Hghost Hlog]") as "_".
      { by iFrame "∗#". }

      rewrite Heq0. rewrite ?fmap_app -app_assoc. iDestruct (big_sepL2_app_inv with "Hsaved'") as "(H1&H2)".
      { left. rewrite ?fmap_length //. }

      iEval (simpl) in "H2". iDestruct "H2" as "(HsavedQ'&?)".
      iDestruct (saved_pred_agree _ _ _ _  _ (get_rwops σ0a) with "Hsaved [$]") as "HQequiv".
      iApply (lc_fupd_add_later with "[$]"). iNext.
      iRewrite -"HQequiv" in "HQ".

      iInv "HQ" as "Hescrow" "Hclose".
      iDestruct "Hescrow" as "[HΦ|>Hbad]"; last first.
      {
        iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
        exfalso. naive_solver.
      }
      iMod ("Hclose" with "[$Htok]").
      iMod (lc_fupd_elim_later with "Hcred2 HΦ") as "HΦ".
      iModIntro.
      iIntros "HΨ".
      iApply ("HΨ" with "HΦ").
      iExists _, _.
      iFrame.
      simpl.
      rewrite /named.
      iExactEq "Hrepy_ret_sl".
      { repeat f_equal.
        rewrite Heq0 in Hfst_eq. rewrite ?fmap_app -app_assoc in Hfst_eq.
        apply app_inj_1 in Hfst_eq; last (rewrite ?fmap_length //).
        destruct Hfst_eq as (Hfst_eq&_).
        done.
      }
    }
  }
  {
    iIntros.
    iNamed "Hreply".
    iModIntro.
    iIntros "HΨ".
    iApply ("HΨ" with "[Hfail_Φ]").
    {
      iApply "Hfail_Φ".
      done.
    }
    iExists _, _.
    iFrame.
  }
Qed.

End proof.
