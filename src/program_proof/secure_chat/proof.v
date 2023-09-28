From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import waitgroup.
From Perennial.program_proof.secure_chat Require Import encoding ffi.
From Goose.github_com.mit_pdos.secure_chat Require Import chat4.

Section chat4.
Context `{!heapGS Σ}.
Context `{!ghost_varG Σ u64}.
Context `{!waitgroupG Σ}.

Definition PA (bytes : list u8) : iProp Σ := True%I.

Global Instance mt γ (vs : u64) :
  AsMapsTo (ghost_var γ 1 vs) (λ q, ghost_var γ q vs).
Proof. constructor; auto; apply _. Qed.

Definition PB (γ : gname) (bytes : list u8) : iProp Σ :=
  ∃ (msg : msgT.t),
  ⌜bytes = msgT.encodeF msg⌝ ∧
  readonly (ghost_var γ 1 msg.(msgT.pin)).

Lemma wp_alice γ skA vkB:
  {{{
    valid_sk skA PA ∗
    valid_vk vkB (PB γ)
  }}}
  aliceMain #skA #vkB
  {{{
    (sn : u64) (err : bool), RET (#sn, #err);
    □ (if err then True else readonly (ghost_var γ 1 sn))
  }}}.
Proof.
  iIntros (Φ) "[Hsk Hvk] HΦ".
  rewrite /aliceMain.
  rewrite /newMsgT.
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (?) "Hmsg1".
  iDestruct (struct_fields_split with "Hmsg1") as "HH".
  iNamed "HH".
  wp_apply (msgT.wp_encode with "[tag body pin]").
  {
    instantiate (1:=msgT.mk _ _ _).
    rewrite /msgT.own /=.
    iFrame.
  }
  iIntros (? ?) "(o1 & s1 & %e1)".
  wp_apply (wp_sign with "[$Hsk s1]").
  {
    iDestruct (own_slice_to_small with "s1") as "s1".
    iFrame.
  }
  iIntros (? ?) "Hsl_sig".
  rewrite /newMsgWrapT.
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (?) "Hmsgw1".
  iDestruct (struct_fields_split with "Hmsgw1") as "HH".
  iNamed "HH".
  wp_apply (msgWrapT.wp_encode with "[msg o1 sig Hsl_sig sn]").
  {
    iExists l, sig.
    instantiate (1:=msgWrapT.mk _ _ _).
    rewrite /msgWrapT.own /=.
    iFrame.
  }
  iIntros (msgWrap1B msgWrap1BB) "(a1 & b1 & %c1)".
  wp_apply wp_NewSlice.
  iIntros (ret1Empt) "Hsl_ret1empt".
  wp_apply (wp_rpcCall with "[Hsl_ret1empt]").
  { by iApply own_slice_to_small. }
  iIntros (?) "_".
  wp_apply wp_NewSlice.
  iIntros (args2Empt) "Hsl_args2empt".
  wp_apply msgWrapT.wp_new_slice.
  iIntros (msgWrap2B l_any) "[Hsl_msgwrap2b %len_l_any]".
  iDestruct (own_slice_sz with "Hsl_msgwrap2b") as "%len_before".
  wp_apply (wp_rpcCall with "[Hsl_msgwrap2b]").
  { by iApply own_slice_to_small. }
  iIntros (msgWrap2BB) "Hsl_msgwrap2b".
  iDestruct (own_slice_small_sz with "Hsl_msgwrap2b") as "%len_after".
  rewrite <- len_before in len_after.
  rewrite len_l_any in len_after.
  wp_apply (msgWrapT.wp_decode with "[Hsl_msgwrap2b]").
  { by iFrame. }
  clear len_l_any len_before len_after.
  iIntros (args2 l_args2 garb1) "Hargs2".
  wp_pures.
  wp_apply wp_NewSlice.
  iIntros (args3Empt) "Hsl_args3empt".
  wp_apply msgWrapT.wp_new_slice.
  iIntros (msgWrap3B l2_any) "[Hsl_msgwrap3b %len_l2_any]".
  iDestruct (own_slice_sz with "Hsl_msgwrap3b") as "%len_before".
  wp_apply (wp_rpcCall with "[Hsl_msgwrap3b]").
  { by iApply own_slice_to_small. }
  iIntros (msgWrap3BB) "Hsl_msgwrap3b".
  iDestruct (own_slice_small_sz with "Hsl_msgwrap3b") as "%len_after".
  rewrite <- len_before in len_after.
  rewrite len_l2_any in len_after.
  wp_apply (msgWrapT.wp_decode with "[Hsl_msgwrap3b]").
  { by iFrame. }
  iIntros (args3 l_args3 garb2) "Hargs3".
  iNamed "Hargs3".
  wp_loadField.
  wp_apply (msgT.wp_encode with "[Hmsgown]").
  {
    instantiate (1:=msgT.mk _ _ _).
    rewrite /msgT.own /=.
    iFrame.
  }
  iIntros (msg3B msg3BB) "(Hown1 & Hsl1 & %Henc1)".
  wp_loadField.
  wp_apply (wp_verify with "[Hvk Hsl1 Hsl_own]").
  {
    iDestruct (own_slice_to_small with "Hsl1") as "Hsl1".
    iDestruct (own_slice_to_small with "Hsl_own") as "Hsl_own".
    iFrame.
  }
  iIntros (err) "Herr".
  destruct err.
  {
    wp_pures.
    by iApply "HΦ".
  }
  wp_pures.
  iRename "HSig" into "HSig2".
  iRename "HSn" into "HSn2".
  iRename "HMsg" into "HMsg2".
  iNamed "Hargs2".
  wp_loadField.
  wp_loadField.
  iNamed "Hown1".
  simpl.
  wp_loadField.
  wp_if_destruct.
  {
    wp_pures.
    by iApply "HΦ".
  }
  wp_loadField.
  wp_pures.
  iApply "HΦ".
  iModIntro.
  rewrite /PB.
  iDestruct "Herr" as (l_args3tmp) "[%Heq #Hro]".
  apply msgT.encode_inj in Heq.
  rewrite <- Heq.
  rewrite Heqb /=.
  iModIntro.
  iApply "Hro".
Qed.

Lemma wp_bob γ skB vkA:
  {{{
    valid_sk skB (PB γ) ∗
    valid_vk vkA PA ∗
    ghost_var γ 1 (U64 0)
  }}}
  bobMain #skB #vkA
  {{{
    (sn : u64) (err : bool), RET (#sn, #err);
    □ (if err then True else readonly (ghost_var γ 1 sn))
  }}}.
Proof.
  iIntros (Φ) "(Hsk & Hvk & Hg) HΦ".
  rewrite /bobMain.
  wp_apply wp_NewSlice.
  iIntros (args1Empt) "Hsl_args1empt".
  wp_apply msgWrapT.wp_new_slice.
  iIntros (msgWrap1B l1_any) "[Hsl_msgwrap1b %len_l1_any]".
  iDestruct (own_slice_sz with "Hsl_msgwrap1b") as "%len_before".
  wp_apply (wp_rpcCall with "[Hsl_msgwrap1b]").
  { by iApply own_slice_to_small. }
  iIntros (msgWrap1BB) "Hsl_msgwrap1b".
  iDestruct (own_slice_small_sz with "Hsl_msgwrap1b") as "%len_after".
  rewrite <- len_before in len_after.
  rewrite len_l1_any in len_after.
  wp_apply (msgWrapT.wp_decode with "[Hsl_msgwrap1b]").
  { by iFrame. }
  iIntros (args1 l_args1 garb1) "Hargs1".
  iNamed "Hargs1".
  wp_loadField.
  rewrite /newMsgT.
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (?) "Hmsg1".
  iDestruct (struct_fields_split with "Hmsg1") as "HH".
  iNamed "HH".
  wp_apply (msgT.wp_encode with "[tag body pin]").
  {
    instantiate (1:=msgT.mk _ _ _).
    rewrite /msgT.own /=.
    iFrame.
  }
  iIntros (? ?) "(o1 & s1 & %e1)".
  iMod (ghost_var_update l_args1.(msgWrapT.sn) with "Hg") as "Hg".
  iMod (readonly_alloc_1 with "Hg") as "#Hro".
  wp_apply (wp_sign with "[Hsk s1 Hro]").
  {
    iFrame.
    iSplit.
    { by iApply own_slice_to_small. }
    rewrite /PB.
    iExists _.
    iSplit; try done.
  }
  iIntros (? ?) "Hsl_sig".
  rewrite /newMsgWrapT.
  wp_apply wp_allocStruct.
  { val_ty. }
  iIntros (?) "Hmsgw1".
  iDestruct (struct_fields_split with "Hmsgw1") as "HH".
  iNamed "HH".
  wp_apply (msgWrapT.wp_encode with "[msg o1 sig Hsl_sig sn]").
  {
    iExists l, sig.
    instantiate (1:=msgWrapT.mk _ _ _).
    rewrite /msgWrapT.own /=.
    iFrame.
  }
  iIntros (msgWrap2B msgWrap2BB) "(a2 & b2 & %c2)".
  wp_apply wp_NewSlice.
  iIntros (ret1Empt) "Hsl_ret1empt".
  wp_apply (wp_rpcCall with "[Hsl_ret1empt]").
  { by iApply own_slice_to_small. }
  iIntros (?) "_".
  wp_loadField.
  wp_pures.
  iApply "HΦ".
  iApply "Hro".
Qed.

Definition party_ret γ sn err : iProp Σ :=
  ∃ (sn_val : u64) (err_val : bool),
  readonly (sn ↦[uint64T] #sn_val) ∗
  readonly (err ↦[boolT] #err_val) ∗
  if err_val then True else readonly (ghost_var γ 1 sn_val).

Lemma wp_game:
  {{{ True }}}
  game #()
  {{{
    (pass : bool), RET (#pass);
    ⌜pass = true⌝
  }}}.
Proof using ghost_varG0 heapGS0 waitgroupG0 Σ.
  iIntros (Φ) "_ HΦ".
  rewrite /game.
  wp_apply (wp_makeKeys PA).
  iIntros (? ?) "[Hsk_a Hvk_a]".
  iMod (ghost_var_alloc (U64 0)) as (γ) "Hg".
  wp_apply (wp_makeKeys (PB γ)).
  iIntros (? ?) "[Hsk_b Hvk_b]".
  wp_pures.
  wp_apply wp_ref_of_zero.
  { auto. }
  iIntros (aliceSn) "Ha_sn".
  wp_apply wp_ref_of_zero.
  { auto. }
  iIntros (aliceErr) "Ha_err".
  wp_apply wp_ref_of_zero.
  { auto. }
  iIntros (bobSn) "Hb_sn".
  wp_apply wp_ref_of_zero.
  { auto. }
  iIntros (bobErr) "Hb_err".

  wp_apply (wp_NewWaitGroup nroot (
    λ i,
    match int.Z i with
    | 0%Z => party_ret γ aliceSn aliceErr
    | 1%Z => party_ret γ bobSn bobErr
    | _ => True%I
    end
  )).

  iIntros (? ?) "Hwg".
  iDestruct (own_WaitGroup_to_is_WaitGroup with "Hwg") as "#Hiwg".
  wp_apply (wp_WaitGroup__Add with "Hwg"); try done.
  iIntros "(Hwg & Hwt)".
  wp_apply (wp_fork with "[Hwt Hsk_a Hvk_b Ha_sn Ha_err]").
  {
    iModIntro.
    wp_apply (wp_alice with "[$Hsk_a $Hvk_b]").
    iIntros (? ?) "#Halice".
    do 2 wp_store.
    iMod (readonly_alloc_1 with "Ha_sn") as "#Ha_sn".
    iMod (readonly_alloc_1 with "Ha_err") as "#Ha_err".
    wp_apply (wp_WaitGroup__Done with "[-]"); try done.
    iFrame "#∗".
    iModIntro.
    change (int.Z 0) with 0.
    repeat iExists _.
    iFrame "#".
  }
  wp_apply (wp_WaitGroup__Add with "Hwg"); try done.
  iIntros "(Hwg & Hwt)".
  wp_apply (wp_fork with "[Hwt Hg Hsk_b Hvk_a Hb_sn Hb_err]").
  {
    iModIntro.
    wp_apply (wp_bob with "[$Hsk_b $Hvk_a $Hg]").
    iIntros (? ?) "#Hbob".
    do 2 wp_store.
    iMod (readonly_alloc_1 with "Hb_sn") as "#Hb_sn".
    iMod (readonly_alloc_1 with "Hb_err") as "#Hb_err".
    wp_apply (wp_WaitGroup__Done with "[$Hwt $Hiwg Hb_sn Hb_err Hbob]"); try done.
    iModIntro.
    change (int.Z 0) with 0.
    repeat iExists _.
    iFrame "#".
  }

  wp_apply (wp_WaitGroup__Wait with "Hwg").
  iClear "Hiwg".
  iIntros "Hwg_post".
  iDestruct (big_sepS_delete _ _ (U64 0) with "Hwg_post") as "[Halice Hwg_post]".
  { set_solver. }
  iDestruct (big_sepS_delete _ _ (U64 1) with "Hwg_post") as "[Hbob _]".
  { set_solver. }
  iDestruct "Halice" as "[%Hbad|Halice]".
  {
    revert Hbad.
    word.
  }
  iDestruct "Hbob" as "[%Hbad|Hbob]".
  {
    revert Hbad.
    word.
  }
  change (int.Z 0) with 0.
  change (int.Z 1) with 1.
  simpl.
  rewrite /party_ret.
  iDestruct "Halice" as (a_sn a_err) "(#Ha_sn & #Ha_err & Halice)".
  iDestruct "Hbob" as (b_sn b_err) "(#Hb_sn & #Hb_err & Hbob)".

  wp_apply wp_load_ro; try done.
  destruct a_err.
  {
    wp_pures.
    by iApply "HΦ".
  }
  wp_apply wp_load_ro; try done.
  destruct b_err.
  {
    wp_pures.
    by iApply "HΦ".
  }
  wp_apply wp_load_ro; try done.
  wp_apply wp_load_ro; try done.
  iDestruct "Halice" as "#Halice".
  iDestruct "Hbob" as "#Hbob".

  iDestruct (readonly_load _ ⊤ with "Halice") as "> Halice2".
  iDestruct "Halice2" as (?) "Halice2".
  iDestruct (readonly_load _ ⊤ with "Hbob") as "> Hbob2".
  iDestruct "Hbob2" as (?) "Hbob2".
  iDestruct (ghost_var_agree with "[$Halice2] [$Hbob2]") as "%Heq".

  wp_pures.
  iApply "HΦ".
  iPureIntro.
  apply bool_decide_eq_true.
  rewrite Heq.
  done.
Qed.

End chat4.
