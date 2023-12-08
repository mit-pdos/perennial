From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.full2 Require Import shared.
From Goose.github_com.mit_pdos.secure_chat Require Import full2.
From Perennial.program_proof.chat.full2 Require Import shared ffi.
From iris.unstable.base_logic Require Import mono_list.

Section clerk.
Context `{!heapGS Σ, !mono_listG MsgT.t Σ}.

Definition pred_transf P : (list u8 → iProp Σ) :=
  λ lb, (∃ l, ⌜MsgTSlice.encodes lb l⌝ ∗ P l)%I.

Definition is_clerk cp γ (P:list MsgT.t → iProp Σ) lmsg : iProp Σ :=
  ∃ (cli:loc) log llog (num:u64) (sk:loc) vks lvks,
  "Hcli" ∷ cp ↦[Clerk :: "cli"] #cli ∗
  "Hlog" ∷ cp ↦[Clerk :: "log"] (slice_val log) ∗
  "Hnum" ∷ cp ↦[Clerk :: "myNum"] #num ∗
  "Hsk" ∷ cp ↦[Clerk :: "signer"] #sk ∗
  "Hvks" ∷ cp ↦[Clerk :: "verifiers"] (slice_val vks) ∗

  "Hlog_own" ∷ own_slice log ptrT 1 llog ∗
  "Hsep" ∷ ([∗ list] x1;x2 ∈ llog;lmsg, MsgT.own x1 x2) ∗
  "Hl_auth" ∷ mono_list_auth_own γ 1 lmsg ∗
  "His_sk" ∷ is_sk sk (pred_transf P) ∗
  "Hvks_own" ∷ own_slice_small vks ptrT 1 lvks ∗
  "His_cli" ∷ is_uRPCClient cli ∗

  "#Hvks_sep" ∷ ([∗ list] vk ∈ lvks, is_vk vk (pred_transf P)) ∗
  "#HPold" ∷ □ P lmsg ∗
  "%Hvks_len" ∷ ⌜length lvks = max_senders⌝.

Lemma wp_clerk_make sk P vks lvks (host num:u64) :
  {{{
    "#HP" ∷ □ P [] ∗
    "His_sk" ∷ is_sk sk (pred_transf P) ∗
    "Hvks_own" ∷ own_slice_small vks ptrT 1 lvks ∗
    "#Hvks_sep" ∷ ([∗ list] vk ∈ lvks, is_vk vk (pred_transf P)) ∗
    "%Hvks_len" ∷ ⌜length lvks = max_senders⌝
  }}}
  MakeClerk #host #num #sk (slice_val vks)
  {{{
    γ cp, RET #cp;
    "#Htriv_lb" ∷ mono_list_lb_own γ [] ∗
    "Hclk" ∷ is_clerk cp γ P []
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /MakeClerk.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (?) "Hclk".
  wp_apply wp_urpc_make.
  iIntros (?) "H".
  iNamed "H".
  iDestruct (struct_fields_split with "Hclk") as "H".
  iNamed "H".
  wp_storeField.
  wp_apply wp_NewSlice.
  iIntros (?) "Hlog".
  wp_storeField.
  wp_storeField.
  wp_storeField.
  wp_storeField.
  iMod (mono_list_own_alloc []) as (γ) "(Hauth & #Hlb)".
  iApply ("HΦ" $! γ).
  iFrame "#∗".
  iExists _, s, _, _, _, vks, _.
  iFrame "%#∗".
  rewrite replicate_0.
  by iApply big_sepL2_nil.
Qed.

Lemma wp_put cp γ P p m lmsg :
  {{{
    "Hclk" ∷ is_clerk cp γ P lmsg ∗
    "Hm" ∷ MsgT.own p m ∗
    "#Hl_lb" ∷ mono_list_lb_own γ lmsg ∗
    "Hfupd" ∷ (∀ l', ⌜lmsg `prefix_of` l'⌝ -∗ P l' ={⊤}=∗ □ P (l' ++ [m]))
  }}}
  Clerk__Put #cp #p
  {{{
    RET #();
    "Hclk" ∷ is_clerk cp γ P lmsg ∗
    "Hm" ∷ MsgT.own p m
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /Clerk__Put.
  iEval (rewrite /is_clerk) in "Hclk".
  iNamed "Hclk".
  wp_apply (MsgT.wp_copy with "[$]").
  iIntros (?) "H".
  iNamed "H".
  wp_loadField.
  wp_apply wp_slice_len.
  iDestruct (own_slice_sz with "[$Hlog_own]") as %Hlen.
  wp_apply wp_NewSlice.
  iIntros (log') "Hlog_own'".
  iDestruct (own_slice_small_read with "Hlog_own") as "(Hlog_own & Hsl_conv)".
  iDestruct (own_slice_small_acc with "Hlog_own'") as "(Hlog_own' & Hsl_conv')".
  wp_loadField.
  wp_apply (wp_SliceCopy_full_typed with "[$Hlog_own $Hlog_own']").
  {
    iPureIntro.
    rewrite replicate_length.
    word.
  }
  iIntros "(Hlog_own & Hlog_own')".
  iDestruct ("Hsl_conv" with "Hlog_own") as "Hlog_own".
  iDestruct ("Hsl_conv'" with "Hlog_own'") as "Hlog_own'".
  wp_apply (wp_SliceAppend with "Hlog_own'").
  iIntros (log'') "Hlog_own'".
  iDestruct (big_sepL2_app _ _ [np] _ [m] with "Hsep") as "/= H".
  iDestruct ("H" with "[$]") as "Hsep".
  iDestruct (own_slice_small_read with "Hlog_own'") as "(Hlog_own' & Hsl_conv')".
  wp_apply (MsgTSlice.wp_encode with "[Hlog_own' Hsep]").
  {
    rewrite /MsgTSlice.own.
    iFrame.
  }
  iIntros (??) "H".
  iNamed "H".
  iEval (rewrite /MsgTSlice.own) in "Hargs".
  iNamed "Hargs".
  iDestruct ("Hsl_conv'" with "[$]") as "Hlog_own'".
  wp_loadField.
  iDestruct ("Hfupd" $! lmsg with "[%] HPold") as "> #HP"; [naive_solver|].
  wp_apply (wp_sign with "[$His_sk $Henc HP]").
  {
    rewrite /pred_transf.
    iExists _.
    iFrame "%#".
  }
  iIntros (???) "H".
  iNamed "H".
  wp_apply wp_Assume.
  iIntros "%Herr".
  apply bool_decide_eq_true in Herr.
  rewrite /fc_errno in Herr.
  destruct err; [destruct f; done|].
  iNamed "H".
  wp_loadField.
  wp_apply (PutArg.wp_new with "[$]").
  iIntros (?) "H".
  iNamed "H".
  wp_apply (PutArg.wp_encode with "[$]").
  iIntros (??) "H".
  iNamed "H".
  wp_apply wp_NewSlice.
  iIntros (r) "Hr".
  iDestruct (own_slice_to_small with "Hr") as "Hr".
  wp_loadField.
  wp_apply (wp_call with "[$His_cli $Henc $Hr]").
  iIntros (??) "H".
  iNamed "H".
  wp_apply wp_Assume.
  iIntros "_".
  wp_pures.
  iApply "HΦ".
  iSplitR "Hold"; [|by iFrame].
  iClear "Hlog_own' Hargs HP".
  iExists _, _, _, _, _, _, _.
  iDestruct (big_sepL2_app_inv with "Hsep") as "(Hsep & _)"; [naive_solver|].
  by iFrame "#∗".
Qed.

Lemma wp_get cp γ P lmsg :
  {{{
    "Hclk" ∷ is_clerk cp γ P lmsg ∗
    "#Hlold_lb" ∷ mono_list_lb_own γ lmsg
  }}}
  Clerk__Get #cp
  {{{
    lg lloc' lmsg' err, RET ((slice_val lg), #(fc_errno err));
    match err with
    | Some ErrSome =>
      "Hclk" ∷ is_clerk cp γ P lmsg
    | None =>
      "Hclk" ∷ is_clerk cp γ P lmsg' ∗
      "#Hl_lb" ∷ mono_list_lb_own γ lmsg' ∗
      "Hsl" ∷ own_slice_small lg ptrT 1 lloc' ∗
      "%Hpref" ∷ ⌜lmsg `prefix_of` lmsg'⌝ ∗
      "HP" ∷ P lmsg' ∗
      "Hsep" ∷ ([∗ list] x1;x2 ∈ lloc';lmsg', MsgT.own x1 x2)
    end
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /Clerk__Get.
  iEval (rewrite /is_clerk) in "Hclk".
  iNamed "Hclk".
  wp_apply wp_NewSlice.
  iIntros (nilRet) "HnilRet".
  iDestruct (own_slice_to_small with "HnilRet") as "HnilRet".
  wp_apply wp_NewSlice.
  iIntros (r) "Hr".
  iDestruct (own_slice_to_small with "Hr") as "Hr".
  wp_apply wp_NewSlice.
  iIntros (i) "Hi".
  iDestruct (own_slice_to_small with "Hi") as "Hi".
  wp_loadField.
  wp_apply (wp_call with "[$His_cli $Hi $Hr]").
  iIntros (??) "H".
  iNamed "H".
  wp_if_destruct.
  {
    wp_pures.
    iApply ("HΦ" $! nilRet [] [] (Some ErrSome)).
    repeat iExists _.
    by iFrame "Hlog Hvks ∗#%".
  }
  (* TODO: better way to destruct the err?
     Not for this err construction,
     but I can switch to ite (bool_decide) postconds,
     which would remove one level of wrapping here.
  *)
  destruct err; [destruct c; done|].
  iNamed "H".
  wp_apply (PutArg.wp_decode with "[$]").
  iIntros (???) "H".
  wp_if_destruct.
  {
    wp_pures.
    iApply ("HΦ" $! nilRet [] [] (Some ErrSome)).
    repeat iExists _.
    by iFrame "Hlog Hvks ∗#%".
  }
  destruct err; [destruct f; done|].
  iNamed "H".
  rewrite /PutArg.own.
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.
  rewrite -Hvks_len in Hinb.
  apply list_lookup_lt in Hinb as (lvk & Hinb).
  wp_apply (wp_SliceGet with "[$Hvks_own //]").
  iIntros "Hvks_own".
  wp_loadField.
  wp_loadField.
  iDestruct (big_sepL_lookup_acc with "Hvks_sep") as "(#Hvk & _)"; [done|].
  wp_apply (wp_verify with "[$Hvk $Hsig_sl $HlogB_sl]").
  iIntros (?) "H".
  iNamed "H".
  wp_if_destruct.
  {
    wp_pures.
    iApply ("HΦ" $! nilRet [] [] (Some ErrSome)).
    repeat iExists _.
    by iFrame "Hlog Hvks ∗#%".
  }
  destruct err; [destruct f; done|].
  iNamed "H".
  wp_loadField.
  iEval (rewrite /pred_transf) in "HP".
  iDestruct "HP" as (ldec) "(%Hdec & HPdec)".
  wp_apply (MsgTSlice.wp_decode _ _ _ [] with "[$Hdata_sl]").
  {
    iFrame "%".
    iPureIntro.
    apply app_nil_end.
  }
  iIntros (???) "H".
  iNamed "H".
  wp_loadField.
  iDestruct (own_slice_small_read with "Hlog_own") as "(Hlog_own & Hsl_conv)".
  wp_apply (MsgTSlice.wp_prefix with "[Hlog_own Hsep Hargs]").
  {
    rewrite /MsgTSlice.own.
    iFrame.
  }
  iIntros (?) "H".
  iNamed "H".
  iEval (rewrite /MsgTSlice.own) in "Hshort".
  iRename "Hsl" into "Hother".
  iNamed "Hshort".
  iDestruct ("Hsl_conv" with "Hsl") as "Hlog_own".
  wp_if_destruct.
  {
    wp_pures.
    iApply ("HΦ" $! nilRet [] [] (Some ErrSome)).
    repeat iExists _.
    by iFrame "Hlog Hvks ∗#%".
  }
  wp_apply (MsgTSlice.wp_copy with "[$]").
  iIntros (??) "H".
  iNamed "H".
  wp_apply (wp_storeField with "[$Hlog]"); [val_ty|].
  iIntros "Hlog".
  wp_pures.
  iApply ("HΦ" $! args_ptr0 lloc ldec None).
  destruct Heq; destruct H; [done|].
  iMod (mono_list_auth_own_update_app x with "[$]") as "(Hl_auth & Hl_lb)".
  rewrite -H.
  iEval (rewrite /MsgTSlice.own) in "Hold".
  iRename "Hsep" into "Hsepold".
  iNamed "Hold".
  iFrame "#∗".
  iSplitL.
  2: {
    rewrite /prefix.
    naive_solver.
  }
  repeat iExists _.
  by iFrame "#∗".
Qed.

End clerk.
