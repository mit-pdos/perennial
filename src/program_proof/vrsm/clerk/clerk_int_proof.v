From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm Require Export clerk.
From Perennial.program_proof.vrsm.replica Require Export config_protocol_proof
     definitions apply_proof makeclerk_proof roapply_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!pbG Σ}.

Definition own_int_Clerk ck γ : iProp Σ :=
  ∃ (confCk:loc) (prefReplica lastPreferenceRefresh:u64) clerks_sl clerks γsrvs γconf,
    "#HconfCk" ∷ readonly (ck ↦[clerk.Clerk :: "confCk"] #confCk) ∗
    "HreplicaClerks" ∷ ck ↦[clerk.Clerk :: "replicaClerks"] (slice_val clerks_sl) ∗
    "HprefReplica" ∷ ck ↦[clerk.Clerk :: "preferredReplica"] #prefReplica ∗
    "HlastPreferenceRefresh" ∷ ck ↦[clerk.Clerk :: "lastPreferenceRefresh"] #lastPreferenceRefresh ∗
    "#HisConfCk" ∷ is_Clerk2 confCk γ γconf ∗ (* config clerk *)
    "#Hclerks_sl" ∷ readonly (own_slice_small clerks_sl ptrT (DfracOwn 1) clerks) ∗
    "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv ∈ clerks ; γsrvs, is_Clerk ck γ γsrv) ∗
    "%Hlen" ∷ ⌜length γsrvs > 0⌝
.

Lemma wp_Clerk__maybeRefreshPreference ck γ :
  {{{
        own_int_Clerk ck γ
  }}}
    Clerk__maybeRefreshPreference #ck
  {{{
        RET #(); own_int_Clerk ck γ
  }}}
.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  wp_lam. wp_pures.
  wp_apply wp_GetTimeRange.
  iIntros "* _ _ $ !>".
  wp_pures. wp_loadField. wp_pures.
  wp_if_destruct.
  { wp_apply wp_RandomUint64. iIntros (?) "_".
    wp_loadField. wp_apply wp_slice_len. wp_storeField.
    wp_pures.
    wp_apply wp_GetTimeRange.
    iIntros "* _ _ $ !>".
    wp_pures. wp_storeField. wp_pures.
    iModIntro. iApply "HΦ".
    repeat iExists _; iFrame "∗". 
    instantiate (7:=γconf).
    iFrame "HisConfCk #%".
  }
  iModIntro. iApply "HΦ".
  repeat iExists _; iFrame "∗".
  instantiate (7:=γconf).
  iFrame "HisConfCk #%".
Qed.

Lemma wp_makeClerks γ config_sl servers γsrvs q :
  {{{
        "#Hhosts" ∷ ([∗ list] γsrv ; host ∈ γsrvs ; servers, is_pb_host host γ γsrv) ∗
        "Hservers_sl" ∷ own_slice_small config_sl uint64T q servers
  }}}
    makeClerks (slice_val config_sl)
  {{{
        clerks_sl clerks, RET (slice_val clerks_sl);
     readonly (own_slice_small clerks_sl ptrT (DfracOwn 1) clerks) ∗
    ([∗ list] ck ; γsrv ∈ clerks ; γsrvs, is_Clerk ck γ γsrv)
  }}}
.
Proof.
  iIntros (Φ).
  iNamed 1. iIntros "HΦ".
  wp_lam.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (clerks_sl) "Hclerks_sl".
  wp_pures.
  iDestruct (own_slice_to_small with "Hclerks_sl") as "Hclerks_sl".
  iDestruct (own_slice_small_sz with "Hclerks_sl") as %Hclerks_sz.
  iDestruct (own_slice_small_sz with "Hservers_sl") as %Hservers_sz.
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
          "Hservers_sl" ∷ own_slice_small config_sl uint64T q servers ∗
          "#Hclerks_is" ∷ ([∗ list] ck ; γsrv ∈ clerksComplete ; (take (length clerksComplete) γsrvs),
                              is_Clerk ck γ γsrv
                              )
          )%I with "[Hclerks_sl Hservers_sl Hi]" as "HH".
  {
    iExists _, [], _.
    simpl.
    iFrame "∗#".
    iPureIntro.
    split; first word.
    rewrite replicate_length.
    word.
  }
  wp_forBreak_cond.

  wp_pures.
  iNamed "HH".
  wp_load.
  wp_apply (wp_slice_len).
  wp_pures.
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

    iDestruct (big_sepL2_lookup_2_some with "Hhosts") as %HH.
    { done. }
    destruct HH as [γsrv Hserver_γs_lookup].
    wp_apply (makeclerk_proof.wp_MakeClerk with "[]").
    { iDestruct (big_sepL2_lookup_acc with "Hhosts") as "[H _]"; try done. iNamed "H".
      iFrame "#". }
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
    { iPureIntro. rewrite app_length /=. word. }
    destruct clerksLeft.
    { exfalso. rewrite app_nil_r in Hlen. word. }

    iSplitR.
    {
      iPureIntro.
      do 2 rewrite app_length /=.
      rewrite -Hlen app_length /=.
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
        by rewrite insert_app_r /= -app_assoc.
      }
    }
    rewrite app_length.
    simpl.
    iDestruct (big_sepL2_length with "Hhosts") as %Hserver_len_eq.
    rewrite take_more; last first.
    { lia. }

    iApply (big_sepL2_app with "Hclerks_is []").

    replace (take 1 (drop (_) γsrvs)) with ([γsrv]); last first.
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
  iModIntro.
  iRight.
  iSplitR; first done.
  wp_pures.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "Hclerks_sl") as "$".
  iFrame.
  destruct clerksLeft.
  2:{ exfalso. rewrite app_length /= in Hlen. word. }
  rewrite app_nil_r in Hlen |- *.
  iDestruct (big_sepL2_length with "Hhosts") as %?.
  rewrite Hlen -H.
  rewrite firstn_all.
  by iFrame "#".
Qed.

Lemma wp_MakeClerk_int γ configHosts configHosts_sl :
  {{{
        "#HconfSl" ∷ readonly (own_slice_small configHosts_sl uint64T (DfracOwn 1) configHosts) ∗
        "#Hconf" ∷ is_pb_config_hosts configHosts γ
  }}}
    Make (slice_val configHosts_sl)
  {{{
        (ck:loc), RET #ck; own_int_Clerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat constructor. Opaque slice.T. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeClerk2 with "[]").
  { iFrame "#". }
  iIntros (??) "#HconfCk".
  wp_storeField.
  wp_pures.

  wp_forBreak.
  wp_pures.
  wp_loadField.
  wp_bind (configservice.Clerk__GetConfig _).
  wp_apply (wp_frame_wand with "[-HconfCk]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__GetConfig2 with "HconfCk").
  iModIntro.
  iIntros (???) "[Hconf_sl_ro #Hhost]".
  iNamed 1.
  wp_pures.
  wp_apply (wp_slice_len).
  wp_if_destruct.
  {
    iLeft.
    iModIntro.
    iFrame.
    done.
  }
  iMod (readonly_load with "Hconf_sl_ro") as (?) "Hconf_sl".
  iDestruct (own_slice_small_sz with "Hconf_sl") as "%Hlen".
  iDestruct (big_sepL2_length with "Hhost") as %Hleneq.
  assert (length conf > 0).
  {
    rewrite Hlen.
    destruct (decide (config_sl.(Slice.sz) = 0)).
    { exfalso. rewrite e in Heqb. done. }

    destruct (decide (uint.nat config_sl.(Slice.sz) = 0)).
    {
      exfalso.
      replace (config_sl.(Slice.sz)) with (W64 0) in * by word.
      done.
    }
    word.
  }

  wp_apply (wp_makeClerks with "[$]").
  iIntros (??) "[#Hclerks_sl #Hclerks_rpc]".
  wp_storeField.
  iRight.
  iSplitR; first done.
  iMod (readonly_alloc_1 with "confCk") as "#?".
  iModIntro.
  iDestruct (big_sepL2_length with "[$]") as %?.
  wp_pures.
  wp_apply wp_RandomUint64. iIntros (?) "_".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_storeField.
  wp_apply wp_GetTimeRange. iIntros "* _ _ $ !>".
  wp_pures. wp_storeField. wp_pures.
  iApply "HΦ".
  repeat iExists _.
  iModIntro. iFrame "∗ Hclerks_rpc HconfCk #".
  iPureIntro. lia.
Qed.

Lemma wp_Clerk__Apply_int γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
own_int_Clerk ck γ -∗
own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_int_log γ ops ∗
  (⌜apply_postcond ops op⌝ -∗ own_int_log γ (ops ++ [op]) ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
                  own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                  own_int_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) -∗
WP clerk.Clerk__Apply #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (?) "Hck Hop_sl #Hupd".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.

  iAssert (
      ∃ some_sl,
        "Hret" ∷ ret ↦[slice.T byteT] (slice_val some_sl)
    )%I with "[Hret]" as "HH".
  { replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (err) "Herr".
  wp_pures.
  iNamed "Hck".
  wp_loadField.

  wp_bind (Clerk__Apply _ _).
  wp_apply (wp_wand with "[Hop_sl]").
  { (* apply *)
    pose proof Hlen as Hlen2.
    apply list_lookup_lt in Hlen2 as [? Hlookup].
    iDestruct (big_sepL2_lookup_2_some with "Hclerks_rpc") as %[? ?].
    { done. }
    iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks".
    wp_apply (wp_SliceGet with "[$Hclerks]").
    { iPureIntro. done. }
    iIntros "_".
    wp_apply (apply_proof.wp_Clerk__Apply with "[] Hop_sl").
    { done. }
    { iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc") as "[$ _]"; done. }
    iModIntro.
    iSplitL.
    { (* successful case *)
      iMod "Hupd" as (?) "[Hown Hupd2]".
      iModIntro.
      iExists _.
      iFrame "Hown".
      iIntros "H Hown".
      iMod ("Hupd2" with "H Hown") as "Hupd2".
      iModIntro.
      iIntros (?) "Hsl Hsl2".
      iDestruct ("Hupd2" with "Hsl") as "HΦ".
      instantiate (1:=(λ (v:goose_lang.val),
        (∃ (reply_sl:Slice.t),
        ⌜v = (#0, slice_val reply_sl)%V⌝ ∗ (own_int_Clerk ck γ -∗ Φ (slice_val reply_sl))) ∨
        (∃ (err:u64) unused_sl, own_slice_small op_sl byteT (DfracOwn 1) op_bytes ∗ ⌜err ≠ 0⌝ ∗ ⌜v = (#err, slice_val unused_sl)%V⌝))%I).
      simpl.
      iLeft.
      iExists _.
      iSpecialize ("HΦ" with "Hsl2").
      iSplitR; first done.
      iFrame.
    }
    { (* error case *)
      iIntros (?? Herr).
      iIntros "Hop_sl".
      iRight.
      iExists err0, _.
      iSplitL; first done.
      done.
    }
  }
  iIntros (v) "H1".
  iDestruct "H1" as "[Hsuccess|Herror]".
  {
    iDestruct "Hsuccess" as (?) "[-> HΦ]".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    wp_load.
    iApply "HΦ".
    iModIntro.
    repeat iExists _. iFrame "HisConfCk".
    iFrame "∗#%".
  }
  { (* retry *)
    iDestruct "Herror" as (??) "[Hop_sl Herror]".
    iDestruct "Herror" as "[%Herr ->]".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    {
      exfalso.
      done.
    }
    wp_apply (wp_Sleep).
    wp_pures.
    wp_loadField.
    wp_bind (configservice.Clerk__GetConfig _).
    wp_apply (wp_frame_wand with "[-]").
    { iNamedAccu. }
    wp_apply (wp_Clerk__GetConfig2 with "HisConfCk").
    iModIntro.
    iIntros (???) "[Hconf_sl_ro #Hhosts]".
    iNamed 1.
    wp_pures.
    iMod (readonly_load with "Hconf_sl_ro") as (?) "Hconf_sl".
    iDestruct (own_slice_small_sz with "Hconf_sl") as %Hconf_sz.
    wp_apply (wp_slice_len).
    wp_pures.
    iDestruct (big_sepL2_length with "Hhosts") as %?.
    wp_if_destruct.
    {
      wp_apply (wp_makeClerks with "[$]").
      iIntros (??) "[? ?]".
      wp_storeField.
      iLeft. iModIntro.
      iSplitR; first done.
      iFrame "Hret Hop_sl".
      repeat iExists _. iFrame "HisConfCk ∗#%".
      iPureIntro. word.
    }
    {
      wp_pures.
      iLeft.
      iFrame "Hret Hop_sl". iSplitR; first done.
      iModIntro.
      repeat iExists _; iFrame "HisConfCk ∗#%".
    }
  }
Qed.

Lemma wp_Clerk__ApplyReadonly_int γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
is_readonly_op op →
has_op_encoding op_bytes op →
own_int_Clerk ck γ -∗
own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
□(|={⊤∖↑pbN,∅}=> ∃ ops, own_int_log γ ops ∗
       (own_int_log γ ops ={∅,⊤∖↑pbN}=∗
       □(∀ reply_sl, own_slice_small reply_sl byteT (DfracOwn 1) (compute_reply ops op) -∗
                    own_slice_small op_sl byteT (DfracOwn 1) op_bytes -∗
                    own_int_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))
 -∗
WP clerk.Clerk__ApplyRo2 #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (??) "Hck Hop_sl #Hupd".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.
  wp_apply (wp_Clerk__maybeRefreshPreference with "[$]").
  iIntros "Hck".
  wp_pures.

  iAssert (
      ∃ some_sl,
        "Hret" ∷ ret ↦[slice.T byteT] (slice_val some_sl)
    )%I with "[Hret]" as "HH".
  { replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.

  iNamed "Hck".
  wp_loadField.
  wp_pures.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (err) "Herr".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (i) "Hi".

  wp_apply (wp_forBreak_cond (λ b, ∃ (ival : u64) (errval : u64) (ret_sl : Slice.t),
    "Herr" ∷ err ↦[uint64T] #errval ∗
    "Hret" ∷ ret ↦[slice.T byteT] ret_sl ∗
    "Hi" ∷ i ↦[uint64T] #ival ∗
    "Hloopcase" ∷ match b with
    | true =>
      ∃ (prefReplica' prefRefresh' : u64),
      "Hop_sl" ∷ own_slice_small op_sl byteT (DfracOwn 1) op_bytes ∗
      "HreplicaClerks" ∷ ck ↦[clerk.Clerk :: "replicaClerks"] clerks_sl ∗
      "HprefReplica" ∷ ck ↦[clerk.Clerk :: "preferredReplica"] #prefReplica' ∗
      "HlastPreferenceRefresh" ∷ ck ↦[clerk.Clerk :: "lastPreferenceRefresh"] #prefRefresh' ∗
      match decide (ival = 0) with
      | left _  => True
      | right _ => "%Herrval" ∷ ⌜errval ≠ 0⌝
      end
    | false =>
      ( "%Herrval" ∷ ⌜errval = 0⌝ ∗
        "HΦ" ∷ Φ (slice_val ret_sl)) ∨
      ( ∃ (prefReplica' prefRefresh' : u64),
        "%Herrval" ∷ ⌜errval ≠ 0⌝ ∗
        "Hop_sl" ∷ own_slice_small op_sl byteT (DfracOwn 1) op_bytes ∗
        "HreplicaClerks" ∷ ck ↦[clerk.Clerk :: "replicaClerks"] clerks_sl ∗
        "HlastPreferenceRefresh" ∷ ck ↦[clerk.Clerk :: "lastPreferenceRefresh"] #prefRefresh' ∗
        "HprefReplica" ∷ ck ↦[clerk.Clerk :: "preferredReplica"] #prefReplica')
    end)%I with "[] [HreplicaClerks HprefReplica Hop_sl Hi Herr Hret HlastPreferenceRefresh] []").
  2: {
    repeat iExists _.
    iFrame.
  }

  - iIntros (Φloop) "!> Hloop HΦloop".
    iNamed "Hloop". iNamed "Hloopcase".
    iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
    iDestruct (big_sepL2_length with "Hclerks_rpc") as %Hlen_clerks.
    iDestruct (own_slice_small_sz with "Hclerks_sl2") as %Hclerks_sz.

    wp_load.
    wp_loadField.
    wp_apply wp_slice_len.
    wp_if_destruct.

    2: {
      iApply "HΦloop".
      iModIntro.
      repeat iExists _.
      iFrame.
      destruct (decide _).
      { exfalso. subst. rewrite -Hlen_clerks in Hlen. apply Heqb. word. }
      iRight. repeat iExists _. iFrame.
    }

    wp_pures.
    wp_load.
    wp_loadField.
    wp_apply wp_slice_len.
    wp_pures.
    wp_loadField.
    wp_pures.

    set (clerkIdx:=(word.modu (word.add ival prefReplica) clerks_sl.(Slice.sz))).
    assert (uint.nat clerkIdx < length clerks) as Hlookup_clerks.
    {
      rewrite /clerkIdx. rewrite Hclerks_sz.
       rewrite word.unsigned_modu_nowrap; last lia.
       { apply Z2Nat.inj_lt; auto using encoding.unsigned_64_nonneg.
          { apply Z.mod_pos; lia. }
          { apply Z_mod_lt; lia. }
       }
    }

    wp_bind (Clerk__ApplyRo _ _).
    wp_apply (wp_wand with "[Hop_sl]").
    { (* apply *)
      apply list_lookup_lt in Hlookup_clerks as [? Hlookup].
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as %[? ?].
      { done. }
      iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks".
      wp_apply (wp_SliceGet with "[$Hclerks]").
      { iPureIntro. done. }
      iIntros "_".
      wp_apply (roapply_proof.wp_Clerk__ApplyRo with "[] Hop_sl").
      { done. }
      { done. }
      { iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc") as "[$ _]"; done. }
      iModIntro.
      iSplitL.
      { (* successful case *)
        iMod "Hupd" as (?) "[Hown Hupd2]".
        iModIntro.
        iExists _.
        iFrame "Hown".
        iIntros "Hown".
        iMod ("Hupd2" with "Hown") as "#Hupd2".
        iModIntro.
        iModIntro.
        iIntros (?) "Hsl Hsl2".
        iDestruct ("Hupd2" with "Hsl") as "HΦ".
        instantiate (1:=(λ (v:goose_lang.val),
          (∃ (reply_sl:Slice.t),
            ⌜v = (#0, slice_val reply_sl)%V⌝ ∗
            (own_int_Clerk ck γ -∗ Φ (slice_val reply_sl))) ∨
          (∃ (err:u64) unused_sl,
            own_slice_small op_sl byteT (DfracOwn 1) op_bytes ∗
            ⌜err ≠ 0⌝ ∗ ⌜v = (#err, slice_val unused_sl)%V⌝))%I).
        simpl.
        iLeft.
        iExists _.
        iSpecialize ("HΦ" with "Hsl2").
        iSplitR; first done.
        iFrame.
      }
      { (* error case *)
        iIntros (?? Herr).
        iIntros "Hop_sl".
        iRight.
        iExists err0, _.
        iSplitL; first done.
        done.
      }
    }

    iIntros (v) "H1".
    iDestruct "H1" as "[Hsuccess|Herror]".
    {
      iDestruct "Hsuccess" as (?) "[-> HΦ]".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_pures.
      wp_storeField.
      iApply "HΦloop".
      iModIntro.
      repeat iExists _.
      iFrame.
      iLeft.
      iSplitR; first done.
      iApply "HΦ".
      repeat iExists _.
      iFrame "HisConfCk ∗#%".
    }
    { (* retry *)
      iDestruct "Herror" as (??) "[Hop_sl Herror]".
      iDestruct "Herror" as "[%Herr ->]".
      wp_pures.
      wp_store.
      wp_store.
      wp_load.
      wp_pures.
      wp_if_destruct.
      { exfalso. apply Herr. word. }
      wp_load. wp_store.
      wp_apply wp_GetTimeRange. iIntros "* _ _ $ !>".
      wp_pures. wp_storeField. wp_pures.
      iModIntro.
      iApply "HΦloop".
      repeat iExists _. iFrame "Herr Hret Hi".
      repeat iExists _. iFrame.
      iClear "Hloopcase".
      destruct (decide _); done.
    }

  - iModIntro.
    iNamed 1.
    wp_load.

    iDestruct "Hloopcase" as "[Hsuccess | Hfailure]".
    + iNamed "Hsuccess".
      wp_if_destruct.
      2: { exfalso. replace (Z.of_nat 0) with (0%Z) in Herrval by word. congruence. }
      iModIntro. iRight. iSplitR; first done.
      wp_pures. wp_load. iApply "HΦ".

    + iNamed "Hfailure".
      wp_if_destruct.
      { exfalso. apply Herrval. word. }

      wp_apply wp_RandomUint64. iIntros (?) "_".
      wp_pures.
      wp_apply (wp_Sleep).
      wp_pures.
      wp_loadField.
      wp_bind (configservice.Clerk__GetConfig _).
      wp_apply (wp_frame_wand with "[-]").
      { iNamedAccu. }
      wp_apply (wp_Clerk__GetConfig2 with "HisConfCk").
      iModIntro.
      iIntros (???) "[Hconf_sl_ro #Hhosts]".
      iNamed 1.
      wp_pures.
      iMod (readonly_load with "Hconf_sl_ro") as (?) "Hconf_sl".
      iDestruct (own_slice_small_sz with "Hconf_sl") as %Hconf_sz.
      wp_apply (wp_slice_len).
      wp_pures.
      iDestruct (big_sepL2_length with "Hhosts") as %?.
      wp_apply (wp_If_join (own_int_Clerk ck γ) with "[Hconf_sl HreplicaClerks HprefReplica HlastPreferenceRefresh]").
      { iSplit; iIntros "%".
        2: { wp_pures. iModIntro. iSplitR; first done.
             repeat iExists _. iFrame "HisConfCk ∗#%". }
        wp_apply (wp_makeClerks with "[$]").
        iIntros (??) "[? ?]".
        wp_storeField.
        wp_apply wp_GetTimeRange. iIntros "* _ _ $ !>".
        wp_pures. wp_storeField. wp_pures.
        wp_apply wp_RandomUint64. iIntros (?) "_".
        wp_loadField.
        wp_apply wp_slice_len.
        wp_storeField.
        iSplitR; first done.
        repeat iExists _.
        (* FIXME: framing is_Clerk2 takes forever here.
          After unfolding [named], it is instant. Setting
          [Strategy expand [named]] influences this behavior,
          but only changes it from 12 -> 2 seconds, which is still unacceptable *)
        unfold named. iFrame "HisConfCk ∗#%".
        iPureIntro.
        match goal with
        | H: bool_decide _ = true |- _ => apply bool_decide_eq_true_1 in H
        end.
        word.
      }

      iIntros "Hck".
      wp_pures. iModIntro.
      iLeft. iFrame "Hop_sl".
      iSplitR; first done.
      iSplitR "Hret"; last by iExists _; iFrame. iFrame.
Qed.

End clerk_proof.
