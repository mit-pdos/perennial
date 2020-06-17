From Perennial.program_proof Require Import proof_prelude.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Lemma byte_ptsto_untype l q (x: u8) :
  l ↦[byteT]{q} #x ⊣⊢ l ↦{q} #x.
Proof.
  rewrite struct_mapsto_eq /struct_mapsto_def /=.
  rewrite loc_add_0 right_id.
  iSplit.
  - iDestruct 1 as "[$ _]".
  - iDestruct 1 as "$".
    auto.
Qed.

Definition is_block (s:Slice.t) (q: Qp) (b:Block) :=
  is_slice_small s byteT q (Block_to_vals b).

Definition is_block_full (s:Slice.t) (b:Block) :=
  is_slice s byteT 1 (Block_to_vals b).

Global Instance is_block_timeless s q b :
  Timeless (is_block s q b) := _.

Theorem is_block_not_nil s q b :
  is_block s q b -∗
  ⌜ s ≠ Slice.nil ⌝.
Proof.
  iIntros "Hb".
  rewrite /is_block.
  iDestruct (is_slice_small_not_null with "Hb") as "%Hnull"; eauto.
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

Definition list_to_block_to_vals l :
  length l = Z.to_nat 4096 ->
  Block_to_vals (list_to_block l) = b2val <$> l.
Proof.
  intros H.
  rewrite /list_to_block /Block_to_vals.
  rewrite decide_left.
  f_equal.
  rewrite vec_to_list_to_vec_eq_rect; auto.
Qed.

Lemma array_to_block l q (bs: list byte) :
  length bs = Z.to_nat 4096 ->
  l ↦∗[byteT]{q} (b2val <$> bs) -∗ mapsto_block l q (list_to_block bs).
Proof.
  rewrite /array /mapsto_block.
  iIntros (H) "Hl".
  rewrite -> list_to_block_to_vals by auto.
  rewrite heap_array_to_list.
  rewrite !big_sepL_fmap.
  setoid_rewrite Z.mul_1_l.
  iApply (big_sepL_impl with "Hl"); simpl.
  iModIntro.
  iIntros (i x) "% Hl".
  iApply (byte_ptsto_untype with "Hl").
Qed.

Lemma array_to_block_array l q b :
  array l q byteT (Block_to_vals b) ⊣⊢ mapsto_block l q b.
Proof.
  rewrite /mapsto_block /array.
  rewrite heap_array_to_list.
  rewrite ?big_sepL_fmap.
  setoid_rewrite Z.mul_1_l.
  apply big_opL_proper.
  intros k y Heq.
  rewrite /Block_to_vals in Heq.
  rewrite /b2val.
  rewrite byte_ptsto_untype //.
Qed.

Lemma slice_to_block_array s q b :
  is_slice_small s byteT q (Block_to_vals b) -∗ mapsto_block s.(Slice.ptr) q b.
Proof.
  iIntros "[Ha _]".
  by iApply array_to_block_array.
Qed.

Lemma block_array_to_slice l q b cap :
  mapsto_block l q b -∗ is_slice_small (Slice.mk l 4096 cap) byteT q (Block_to_vals b).
Proof.
  iIntros "Hm".
  iSplitL.
  { by iApply array_to_block_array. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl.
  reflexivity.
Qed.

Transparent disk.Read disk.Write.

Theorem wp_Write_fupd {stk E} E' (a: u64) s q b :
  ∀ Φ,
    is_slice_small s byteT q (Block_to_vals b) -∗
    (|={E,E'}=> ∃ b0, int.val a d↦ b0 ∗
       ▷ (int.val a d↦ b ={E',E}=∗ (is_slice_small s byteT q (Block_to_vals b) -∗ Φ #()))) -∗
    WP  Write #a (slice_val s) @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "Hs Hupd".
  wp_call.
  wp_call.
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  iApply (wp_atomic _ E E').
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
  iFrame.
  iSplitL; auto.
  by iApply array_to_block_array.
Qed.

Theorem wp_Write_fupd_triple {stk E} E' (Q: iProp Σ) (a: u64) s q b :
  {{{ is_slice_small s byteT q (Block_to_vals b) ∗
      (|={E,E'}=> ∃ b0, int.val a d↦ b0 ∗ ▷ (int.val a d↦ b ={E',E}=∗ Q)) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); is_slice_small s byteT q (Block_to_vals b) ∗ Q }}}.
Proof.
  iIntros (Φ) "[Hs Hupd] HΦ". iApply (wp_Write_fupd with "Hs").
  iMod "Hupd" as (b0) "[Hda Hclose]". iModIntro. iExists b0.
  iFrame. iIntros "!> Hda". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write stk E (a: u64) s q b :
  {{{ ∃ b0, int.val a d↦ b0 ∗ is_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); int.val a d↦ b ∗ is_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wp_apply (wp_Write_fupd E with "Hs").
  iModIntro. iExists _. iFrame.
  iIntros "!> Hda !> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write' stk E (z: Z) (a: u64) s q b :
  {{{ ⌜int.val a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ is_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); z d↦ b ∗ is_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "[<- >Hpre] HΦ".
  iApply (wp_Write with "[$Hpre]").
  eauto.
Qed.

Lemma wp_Read_fupd {stk E} E' (a: u64) q :
  ∀ Φ,
    (|={E,E'}=> ∃ b, int.val a d↦{q} b ∗
      ▷ (int.val a d↦{q} b -∗ |={E',E}=> (∀ s, is_block_full s b -∗ Φ (slice_val s)))) -∗
    WP  Read #a @ stk; E {{ Φ }}.
Proof.
  iIntros (Φ) "Hupd".
  wp_call.
  wp_bind (ExternalOp _ _).
  iApply (wp_atomic _ E E').
  iMod "Hupd" as (b) "[Hda Hupd]"; iModIntro.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ"; iModIntro.
  iDestruct (block_array_to_slice _ _ _ 4096 with "Hl") as "Hs".
  wp_pures.
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iApply "HQ"; iFrame.
Qed.

Lemma wp_Read_fupd_triple {stk E} E' (Q: Block -> iProp Σ) (a: u64) q :
  {{{ |={E,E'}=> ∃ b, int.val a d↦{q} b ∗ ▷ (int.val a d↦{q} b -∗ |={E',E}=> Q b) }}}
    Read #a @ stk; E
  {{{ s b, RET slice_val s;
      Q b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hupd HΦ". iApply wp_Read_fupd.
  iMod "Hupd" as (b0) "[Hda Hclose]". iModIntro. iExists b0.
  iFrame. iIntros "!> Hda". iMod ("Hclose" with "Hda").
  iIntros "!> * Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Read {stk E} (a: u64) q b :
  {{{ int.val a d↦{q} b }}}
    Read #a @ stk; E
  {{{ s, RET slice_val s;
      int.val a d↦{q} b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hda HΦ".
  wp_apply (wp_Read_fupd E).
  iModIntro.
  iExists b; iFrame.
  iIntros "!> Hda !> * Hs".
  iApply ("HΦ" with "[$]").
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

Lemma wpc_Barrier stk k E1 E2 :
  {{{ True }}}
    Barrier #() @ stk; k; E1; E2
  {{{ RET #(); True }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "_ HΦ".
  rewrite /Barrier.
  wpc_pures; auto.
  iRight in "HΦ".
  iApply ("HΦ" with "[//]").
Qed.

Lemma wpc_Read stk k E1 E2 (a: u64) q b :
  {{{ int.val a d↦{q} b }}}
    Read #a @ stk; k; E1; E2
  {{{ s, RET slice_val s;
      int.val a d↦{q} b ∗
      is_slice s byteT 1%Qp (Block_to_vals b) }}}
  {{{ int.val a d↦{q} b }}}.
Proof.
  iIntros (Φ Φc) "Hda HΦ".
  rewrite /Read.
  wpc_pures; first done.
  wpc_bind (ExternalOp _ _).
  wpc_atomic; iFrame.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iDestruct (block_array_to_slice _ _ _ 4096 with "Hl") as "Hs".
  iSplit; first (by iApply "HΦ").
  iModIntro. wpc_pures; first done.
  wpc_frame "Hda HΦ".
  { by crash_case. }
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iIntros "(?&HΦ)". iApply "HΦ".
  iFrame.
Qed.

Theorem wpc_Write_fupd {stk k E1 E2} E1' (a: u64) s q b :
  ∀ Φ Φc,
    is_block s q b -∗
    (Φc ∧ |={E1,E1'}=> ∃ b0, int.val a d↦ b0 ∗ ▷ (int.val a d↦ b ={E1',E1}=∗
          Φc ∧ (is_block s q b -∗ Φ #()))) -∗
    WPC Write #a (slice_val s) @ stk;k; E1;E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Φ Φc) "Hs Hfupd".
  rewrite /Write /slice.ptr.
  wpc_pures.
  { iLeft in "Hfupd". iFrame. }
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wpc_atomic.
  { iLeft in "Hfupd". iFrame. }
  iRight in "Hfupd".
  iMod "Hfupd" as (b0) "[Hda HQ]".
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0; iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iMod ("HQ" with "Hda") as "HQ".
  iModIntro.
  iSplit; iModIntro.
  - by iLeft in "HQ".
  - iRight in "HQ". iApply "HQ".
    iFrame.
    destruct s; simpl in Hsz.
    replace sz with (U64 4096).
    + by iApply block_array_to_slice.
    + rewrite length_Block_to_vals in Hsz.
      change block_bytes with (Z.to_nat 4096) in Hsz.
      word.
Qed.

Theorem wpc_Write_fupd_triple {stk k E1 E2} E1' (Q Qc: iProp Σ) (a: u64) s q b :
  {{{ is_block s q b ∗
      (Qc ∧ |={E1,E1'}=> ∃ b0, int.val a d↦ b0 ∗ ▷ (int.val a d↦ b ={E1',E1}=∗ Q)) }}}
    Write #a (slice_val s) @ stk;k; E1;E2
  {{{ RET #(); is_block s q b ∗ Q }}}
  {{{ Qc ∨ Q }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hs Hfupd]".
  iApply (wpc_Write_fupd with "Hs"). iSplit.
  { iLeft in "Hfupd". iLeft in "HΦ". iApply "HΦ". iFrame. }
  iRight in "Hfupd". iMod "Hfupd" as (b0) "[Hv Hclose]". iModIntro.
  iExists b0. iFrame. iIntros "!> Hv". iMod ("Hclose" with "Hv") as "HQ".
  iModIntro. iSplit.
  { iLeft in "HΦ". iApply "HΦ". iFrame. }
  iRight in "HΦ". iIntros "Hblock". iApply "HΦ". iFrame.
Qed.

Theorem wpc_Write' stk k E1 E2 (a: u64) s q b0 b :
  {{{ int.val a d↦ b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); int.val a d↦ b ∗ is_block s q b }}}
  {{{ (int.val a d↦ b0 ∨ int.val a d↦ b) }}}.
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

Theorem wpc_Write stk k E1 E2 (a: u64) s q b :
  {{{ ∃ b0, int.val a d↦ b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); int.val a d↦ b ∗ is_block s q b }}}
  {{{ ∃ b', int.val a d↦ b' }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wpc_apply (wpc_Write' with "[$Hda $Hs]").
  iSplit.
  { iIntros "[Hda|Hda]"; crash_case; eauto. }
  iIntros "!> [Hda Hb]".
  iRight in "HΦ".
  iApply "HΦ"; iFrame.
Qed.

Theorem slice_to_block s q bs :
  s.(Slice.sz) = 4096 ->
  is_slice_small s byteT q (b2val <$> bs) -∗
  mapsto_block s.(Slice.ptr) q (list_to_block bs).
Proof.
  iIntros (Hsz) "Hs".
  iDestruct "Hs" as "[Hl %]".
  rewrite fmap_length in H.
  iApply (array_to_block with "Hl").
  assert (int.val (Slice.sz s) = 4096).
  { rewrite Hsz. reflexivity. }
  lia.
Qed.

End goose.
