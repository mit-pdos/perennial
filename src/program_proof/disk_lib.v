From Perennial.program_proof Require Import disk_prelude.

Section goose.
Context `{!heapGS Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_block (s:Slice.t) (q: dfrac) (b:Block) :=
  own_slice_small s byteT q (Block_to_vals b).

Definition is_block_full (s:Slice.t) (b:Block) :=
  own_slice s byteT (DfracOwn 1) (Block_to_vals b).

Global Instance is_block_timeless s q b :
  Timeless (is_block s q b) := _.

Global Instance is_block_fractional s b :
  fractional.Fractional (λ q, is_block s (DfracOwn q) b).
Proof. apply own_slice_small_fractional. Qed.

Theorem is_block_not_nil s q b :
  is_block s q b -∗
  ⌜ s ≠ Slice.nil ⌝.
Proof.
  iIntros "Hb".
  rewrite /is_block.
  iDestruct (own_slice_small_not_null with "Hb") as "%Hnull"; eauto.
  { rewrite /Block_to_vals fmap_length.
    rewrite vec_to_list_length.
    rewrite /block_bytes. lia. }
  iPureIntro.
  destruct s. rewrite /Slice.nil. simpl in *. congruence.
Qed.

Definition list_to_block (l: list u8) : Block :=
  match decide (length l = Z.to_nat 4096) with
  | left H => eq_rect _ _ (list_to_vec l) _ H
  | _ => inhabitant
  end.

Lemma vec_to_list_to_vec_eq_rect A (l: list A) n (H: length l = n) :
  vec_to_list (eq_rect _ _ (list_to_vec l) _ H) = l.
Proof.
  rewrite <- H; simpl.
  rewrite vec_to_list_to_vec.
  auto.
Qed.

Theorem list_to_block_to_list l :
  length l = Z.to_nat 4096 ->
  vec_to_list (list_to_block l) = l.
Proof.
  intros H.
  rewrite /list_to_block /Block_to_vals.
  rewrite decide_True_pi.
  rewrite vec_to_list_to_vec_eq_rect; auto.
Qed.

Theorem list_to_block_to_vals l :
  length l = Z.to_nat 4096 ->
  Block_to_vals (list_to_block l) = b2val <$> l.
Proof.
  intros H.
  rewrite /Block_to_vals list_to_block_to_list //.
Qed.

Theorem block_list_inj l (b: Block) :
  l = vec_to_list b →
  b = list_to_block l.
Proof.
  intros ->.
  apply vec_to_list_inj2.
  rewrite list_to_block_to_list //.
  rewrite vec_to_list_length //.
Qed.

Theorem block_to_list_to_block i :
  list_to_block (vec_to_list i) = i.
Proof.
  symmetry.
  apply block_list_inj.
  auto.
Qed.

Lemma array_to_block l q (bs: list byte) :
  length bs = Z.to_nat 4096 ->
  l ↦∗[byteT]{q} (b2val <$> bs) -∗ pointsto_block l q (list_to_block bs).
Proof.
  rewrite /array /pointsto_block.
  iIntros (H) "Hl".
  rewrite -> list_to_block_to_vals by auto.
  rewrite heap_array_to_list.
  rewrite !big_sepL_fmap.
  setoid_rewrite Z.mul_1_l.
  iApply (big_sepL_impl with "Hl"); simpl.
  iModIntro.
  iIntros (i x) "% Hl".
  iApply (byte_pointsto_untype with "Hl").
Qed.

Lemma array_to_block_array l q b :
  array l q byteT (Block_to_vals b) ⊣⊢ pointsto_block l q b.
Proof.
  rewrite /pointsto_block /array.
  rewrite heap_array_to_list.
  rewrite ?big_sepL_fmap.
  setoid_rewrite Z.mul_1_l.
  apply big_opL_proper.
  intros k y Heq.
  rewrite /Block_to_vals in Heq.
  rewrite /b2val.
  rewrite byte_pointsto_untype //.
Qed.

Lemma slice_to_block_array s q b :
  own_slice_small s byteT q (Block_to_vals b) -∗ pointsto_block s.(Slice.ptr) q b.
Proof.
  rewrite /own_slice_small.
  iIntros "[Ha _]".
  by iApply array_to_block_array.
Qed.

Lemma block_array_to_slice_raw l q b :
  pointsto_block l q b -∗ l ↦∗[byteT]{q} Block_to_vals b ∗ ⌜length (Block_to_vals b) = uint.nat 4096⌝.
Proof.
  iIntros "Hm".
  rewrite /own_slice_small.
  iSplitL.
  { iApply array_to_block_array. done. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl. done.
Qed.

Transparent disk.Read disk.Write.

Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Theorem wp_Write_atomic (a: u64) s q b :
  ⊢ {{{ own_slice_small s byteT q (Block_to_vals b) }}}
  <<< ∀∀ b0, uint.Z a d↦ b0 >>>
    Write #a (slice_val s) @ ∅
  <<< uint.Z a d↦ b >>>
  {{{ RET #(); own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  wp_call.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  iApply (wp_ncatomic _ _ ∅).
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto. }
  rewrite difference_empty_L.
  iMod "Hupd" as (b0) "[Hda Hupd]"; iModIntro.
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0.
    iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iMod ("Hupd" with "Hda") as "HQ".
  iModIntro.
  iApply "HQ".
  rewrite /own_slice_small.
  iFrame.
  iSplitL; auto.
  by iApply array_to_block_array.
Qed.

Theorem wp_Write_triple E' (Q: iProp Σ) (a: u64) s q b :
  {{{ own_slice_small s byteT q (Block_to_vals b) ∗
      (|NC={⊤,E'}=> ∃ b0, uint.Z a d↦ b0 ∗ (uint.Z a d↦ b -∗ |NC={E',⊤}=> Q)) }}}
    Write #a (slice_val s)
  {{{ RET #(); own_slice_small s byteT q (Block_to_vals b) ∗ Q }}}.
Proof.
  iIntros (Φ) "[Hs Hupd] HΦ". iApply (wp_Write_atomic with "Hs").
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists b0.
  iFrame. iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write (a: u64) s q b :
  {{{ ∃ b0, uint.Z a d↦ b0 ∗ own_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s)
  {{{ RET #(); uint.Z a d↦ b ∗ own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wp_apply (wp_Write_atomic with "Hs").
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "Hclose". iExists _. iFrame.
  iIntros "Hda". iMod "Hclose" as "_".
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write' (z: Z) (a: u64) s q b :
  {{{ ⌜uint.Z a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ own_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s)
  {{{ RET #(); z d↦ b ∗ own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "[<- >Hpre] HΦ".
  iApply (wp_Write with "[$Hpre]").
  eauto.
Qed.

Lemma wp_Read_atomic (a: u64) q :
  ⊢ <<< ∀∀ b, uint.Z a d↦{q} b >>>
      Read #a @ ∅
    <<< uint.Z a d↦{q} b >>>
    {{{ s, RET slice_val s; is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hupd".
  wp_call.
  wp_bind (ExternalOp _ _).
  rewrite difference_empty_L.
  iMod "Hupd" as (b) "[Hda Hupd]".
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto. }
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ"; iModIntro.
  iDestruct (block_array_to_slice_raw with "Hl") as "Hs".
  wp_pures.
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iApply "HQ"; iFrame.
Qed.

Lemma wp_ReadTo_atomic (a: u64) b0 s q :
  ⊢ {{{ is_block_full s b0 }}}
  <<< ∀∀ b, uint.Z a d↦{q} b >>>
      ReadTo #a (slice_val s) @ ∅
    <<< uint.Z a d↦{q} b >>>
    {{{ RET #(); is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_bind (ExternalOp _ _).
  iApply (wp_ncatomic _ _ ∅).
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto. }
  rewrite difference_empty_L.
  iMod "Hupd" as (db0) "[Hda Hupd]"; iModIntro.
  wp_apply (wp_ReadOp with "[$Hda]").
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ".
  iModIntro.
  wp_pures.
  wp_apply wp_slice_ptr.
  iDestruct "Hs" as "[Hs Hcap]".
  rewrite /own_slice_small.
  iDestruct "Hs" as "[Hs _]".
  wp_apply (wp_MemCpy_rec with "[Hs Hl]").
  { iFrame.
    iDestruct (array_to_block_array with "Hl") as "$".
    iPureIntro.
    rewrite !length_Block_to_vals.
    rewrite /block_bytes.
    split; [ reflexivity | ].
    cbv; congruence.
  }
  rewrite take_ge; last first.
  { rewrite length_Block_to_vals.
    rewrite /block_bytes //. }
  iIntros "[Hs Hl]".
  iApply "HQ".
  rewrite /is_block_full /own_slice /own_slice_small.
  iFrame.
  iPureIntro.
  move: Hsz; rewrite !length_Block_to_vals //.
Qed.

Lemma wp_Read_triple E' (Q: Block -> iProp Σ) (a: u64) q :
  {{{ |NC={⊤,E'}=> ∃ b, uint.Z a d↦{q} b ∗ (uint.Z a d↦{q} b -∗ |NC={E',⊤}=> Q b) }}}
    Read #a
  {{{ s b, RET slice_val s;
      Q b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hupd HΦ". iApply wp_Read_atomic.
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> * Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Read (a: u64) q b :
  {{{ uint.Z a d↦{q} b }}}
    Read #a
  {{{ s, RET slice_val s;
      uint.Z a d↦{q} b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hda HΦ".
  wp_apply wp_Read_atomic.
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_".
  iIntros "!> * Hs". iApply ("HΦ" with "[$]").
Qed.

Lemma wp_Barrier stk E  :
  {{{ True }}}
    Barrier #() @ stk; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iApply ("HΦ" with "[//]").
Qed.

Lemma wpc_Barrier stk E1 :
  {{{ True }}}
    Barrier #() @ stk; E1
  {{{ RET #(); True }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "_ HΦ".
  rewrite /Barrier.
  wpc_pures; auto.
  - by crash_case.
  - iRight in "HΦ".
    iApply ("HΦ" with "[//]").
  - by crash_case.
Qed.

Lemma wpc_Read stk E1 (a: u64) q b :
  {{{ uint.Z a d↦{q} b }}}
    Read #a @ stk; E1
  {{{ s, RET slice_val s;
      uint.Z a d↦{q} b ∗
      own_slice s byteT (DfracOwn 1) (Block_to_vals b) }}}
  {{{ uint.Z a d↦{q} b }}}.
Proof.
  iIntros (Φ Φc) "Hda HΦ".
  rewrite /Read.
  wpc_pures.
  { by crash_case. }
  wpc_bind (ExternalOp _ _).
  assert (Atomic StronglyAtomic (ExternalOp ReadOp #a)).
  {
    solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto.
  }
  wpc_atomic; iFrame.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iDestruct (block_array_to_slice_raw with "Hl") as "Hs".
  iSplit.
  { iDestruct "HΦ" as "(HΦ&_)".
    iModIntro.
    iDestruct ("HΦ" with "[$]") as "H". repeat iModIntro; auto. }
  iModIntro. wpc_pures; first by crash_case.
  wpc_frame "Hda HΦ".
  { by crash_case. }
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iIntros "(?&HΦ)". iApply "HΦ".
  iFrame.
Qed.

Theorem wpc_Write_ncfupd {stk E1} E1' (a: u64) s q b :
  ∀ Φ Φc,
    is_block s q b -∗
    (Φc ∧ |NC={E1,E1'}=> ∃ b0, uint.Z a d↦ b0 ∗ ▷ (uint.Z a d↦ b -∗ |NC={E1',E1}=>
          Φc ∧ (is_block s q b -∗ Φ #()))) -∗
    WPC Write #a (slice_val s) @ stk; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Φ Φc) "Hs Hfupd".
  rewrite /Write /slice.ptr.
  wpc_pures.
  { iLeft in "Hfupd". iFrame. }
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  assert (Atomic StronglyAtomic (ExternalOp WriteOp (#a, #s.(Slice.ptr))%V)).
  {
    solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto.
  }
  wpc_atomic.
  iRight in "Hfupd".
  iMod "Hfupd" as (b0) "[Hda HQ]".
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0; iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iMod ("HQ" with "Hda") as "HQ".
  iModIntro.
  iSplit.
  - iDestruct "HQ" as "(HQ&_)". iModIntro. by repeat iModIntro.
  - iModIntro. iRight in "HQ". iApply "HQ".
    iFrame.
    destruct s; simpl in Hsz.
    replace sz with (W64 4096).
    + iDestruct (block_array_to_slice_raw with "Hmapsto") as "[? %]".
      rewrite /is_block /own_slice_small. iFrame.
      iPureIntro. simpl. split; first done. simpl in Hwf. word.
    + rewrite length_Block_to_vals in Hsz.
      change block_bytes with (Z.to_nat 4096) in Hsz.
      word.
Qed.

(* This is a TaDA-syle logically atomic spec, so the HoCAP-style sugar does not work. *)
Theorem wpc_Write_fupd {stk E1} E1' (a: u64) s q b :
  ∀ Φ Φc,
    is_block s q b -∗
    (Φc ∧ |={E1,E1'}=> ∃ b0, uint.Z a d↦ b0 ∗ ▷ (uint.Z a d↦ b ={E1',E1}=∗
          Φc ∧ (is_block s q b -∗ Φ #()))) -∗
    WPC Write #a (slice_val s) @ stk; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "Hblock HΦc".
  wpc_apply (wpc_Write_ncfupd with "[$]").
  iSplit.
  - by iLeft in "HΦc".
  - iRight in "HΦc". iApply fupd_ncfupd. iMod "HΦc" as (?) "(?&H1)".
    iModIntro. iExists _. iFrame. iNext. iIntros "H2".
      by iMod ("H1" with "[$]").
Qed.

Theorem wpc_Write_fupd_triple {stk E1} E1' (Q Qc: iProp Σ) (a: u64) s q b :
  {{{ is_block s q b ∗
      (Qc ∧ |={E1,E1'}=> ∃ b0, uint.Z a d↦ b0 ∗ ▷ (uint.Z a d↦ b ={E1',E1}=∗ Qc ∧ Q)) }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); is_block s q b ∗ Qc ∧ Q }}}
  {{{ Qc }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hs Hfupd]".
  iApply (wpc_Write_fupd with "Hs"). iSplit.
  { iLeft in "Hfupd". iLeft in "HΦ". iApply "HΦ". iFrame. }
  iRight in "Hfupd". iMod "Hfupd" as (b0) "[Hv Hclose]". iModIntro.
  iExists b0. iFrame. iIntros "!> Hv". iMod ("Hclose" with "Hv") as "HQ".
  iModIntro. iSplit.
  { iLeft in "HΦ". iLeft in "HQ". iApply "HΦ". iFrame. }
  iRight in "HΦ". iIntros "Hblock". iApply "HΦ". iFrame.
Qed.

Theorem wpc_Write' stk E1 (a: u64) s q b0 b :
  {{{ uint.Z a d↦ b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); uint.Z a d↦ b ∗ is_block s q b }}}
  {{{ (uint.Z a d↦ b0 ∨ uint.Z a d↦ b) }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wpc_apply (wpc_Write_fupd with "[$Hs]").
  iSplit.
  { crash_case.
    eauto. }
  iModIntro.
  iExists _; iFrame.
  iIntros "!> Hda !>".
  iSplit.
  { crash_case; eauto. }
  iRight in "HΦ".
  iIntros "Hb".
  iApply "HΦ"; iFrame.
Qed.

Theorem wpc_Write stk E1 (a: u64) s q b :
  {{{ ∃ b0, uint.Z a d↦ b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); uint.Z a d↦ b ∗ is_block s q b }}}
  {{{ ∃ b', uint.Z a d↦ b' }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wpc_apply (wpc_Write' with "[$Hda $Hs]").
  iSplit.
  { iLeft in "HΦ". iIntros "[Hda|Hda]"; iApply "HΦ"; eauto. }
  iIntros "!> [Hda Hb]".
  iRight in "HΦ".
  iApply "HΦ"; iFrame.
Qed.

Theorem slice_to_block s q bs :
  s.(Slice.sz) = 4096 ->
  own_slice_small s byteT q (b2val <$> bs) -∗
  pointsto_block s.(Slice.ptr) q (list_to_block bs).
Proof.
  iIntros (Hsz) "Hs".
  rewrite /own_slice_small.
  iDestruct "Hs" as "[Hl %]".
  rewrite fmap_length in H.
  iApply (array_to_block with "Hl").
  assert (uint.Z (Slice.sz s) = 4096).
  { rewrite Hsz. reflexivity. }
  lia.
Qed.

End goose.
