From Perennial.program_proof Require Import async_disk_prelude.

Section goose.
Context `{!heapGS Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

(* TODO: these are common with disk_lib, but we don't want to import disk_lib *)
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
  { by iApply array_to_block_array. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl.
  reflexivity.
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
  <<< ∀∀ aset b0, uint.Z a d↦[aset] b0 >>>
    Write #a (slice_val s) @ ∅
  <<< ∃ b',⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b >>>
  {{{ RET #(); own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  wp_call.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  iApply (wp_ncatomic _ _ ∅).
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7.
    inversion H8. subst. inversion H13. eauto. }
  rewrite difference_empty_L.
  iMod "Hupd" as (aset0 b0) "[Hda Hupd]"; iModIntro.
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iFrame.
    by iApply slice_to_block_array. }
  iDestruct 1 as (? Heq) "[Hda Hmapsto]".
  iMod ("Hupd" with "[Hda]") as "HQ".
  { iExists _. iFrame. eauto. }
  iModIntro.
  iApply "HQ".
  rewrite /own_slice_small.
  iFrame.
  iSplitL; auto.
  by iApply array_to_block_array.
Qed.

Theorem wp_Write_triple E' (Q: iProp Σ) (a: u64) s q b :
  {{{ own_slice_small s byteT q (Block_to_vals b) ∗
      (|NC={⊤,E'}=> ∃ aset b0, uint.Z a d↦[aset] b0 ∗
                    (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b -∗ |NC={E',⊤}=> Q)) }}}
    Write #a (slice_val s)
  {{{ RET #(); own_slice_small s byteT q (Block_to_vals b) ∗ Q }}}.
Proof.
  iIntros (Φ) "[Hs Hupd] HΦ". iApply (wp_Write_atomic with "Hs").
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (aset b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists aset, b0.
  iFrame. iIntros "Hda". iMod "HcloseE" as "_". iDestruct "Hda" as (?) "Hda". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write (a: u64) aset s q b0 b :
  {{{ uint.Z a d↦[aset] b0 ∗ own_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s)
  {{{ RET #();
      ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b ∗ own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wp_apply (wp_Write_atomic with "Hs").
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "Hclose". iExists _, _. iFrame.
  iIntros "Hda". iMod "Hclose" as "_".
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write' (z: Z) (a: u64) aset s q b b0 :
  {{{ ⌜uint.Z a = z⌝ ∗ ▷ (z d↦[aset] b0 ∗ own_slice_small s byteT q (Block_to_vals b)) }}}
    Write #a (slice_val s)
  {{{ RET #();
      ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗
      z d↦[b'] b ∗ own_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "[<- >Hpre] HΦ".
  iApply (wp_Write with "[$Hpre]").
  eauto.
Qed.

Lemma wp_Read_atomic (a: u64) q :
  ⊢ <<< ∀∀ aset b, uint.Z a d↦{q}[aset] b >>>
      Read #a @ ∅
    <<< uint.Z a d↦{q}[aset] b >>>
    {{{ s, RET slice_val s; is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hupd".
  wp_call.
  wp_bind (ExternalOp _ _).
  rewrite difference_empty_L.
  iMod "Hupd" as (? b) "[Hda Hupd]".
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7.
    subst. eauto. }
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
  <<< ∀∀ aset b, uint.Z a d↦{q}[aset] b >>>
      ReadTo #a (slice_val s) @ ∅
    <<< uint.Z a d↦{q}[aset] b >>>
    {{{ RET #(); is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_bind (ExternalOp _ _).
  iApply (wp_ncatomic _ _ ∅).
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7.
    subst. eauto. }
  rewrite difference_empty_L.
  iMod "Hupd" as (aset db0) "[Hda Hupd]"; iModIntro.
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
  {{{ |NC={⊤,E'}=> ∃ aset b, uint.Z a d↦{q}[aset] b ∗ (uint.Z a d↦{q}[aset] b -∗ |NC={E',⊤}=> Q b) }}}
    Read #a
  {{{ s b, RET slice_val s;
      Q b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hupd HΦ". iApply wp_Read_atomic.
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (aset b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _, _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> * Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Read (a: u64) q b aset :
  {{{ uint.Z a d↦{q}[aset] b }}}
    Read #a
  {{{ s, RET slice_val s;
      uint.Z a d↦{q}[aset] b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hda HΦ".
  wp_apply wp_Read_atomic.
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _, _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_".
  iIntros "!> * Hs". iApply ("HΦ" with "[$]").
Qed.

  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

Theorem wp_Barrier_atomic :
  ⊢ {{{ True }}}
  <<< ∀∀ m, [∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs) >>>
    Barrier #() @ ∅
  <<<(⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝ ∗
         [∗ map] a ↦ bs ∈ m, a d↦[(fst bs)] (snd bs)) >>>
  {{{ RET #(); True }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  Transparent async_disk_proph.Barrier.
  wp_rec.
  Opaque async_disk_proph.Barrier.
  iLöb as "IH".
  wp_bind (ExternalOp _ _).
  iApply ectx_lifting.wp_lift_base_step_nc; first by auto.
  iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg".
  iApply (ncfupd_mask_intro); first set_solver+. iIntros "Hclo".
  cbv [ffi_local_ctx disk_interp].
  iSplit.
  { iPureIntro.
    destruct (decide (all_synced (σ1.(world)))).
    - eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      rewrite decide_True //. repeat (monad_simpl; cbn).
    - eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      rewrite decide_False //. repeat (monad_simpl; cbn).
  }
  iNext; iIntros (v2 σ2 g2 efs Hstep).
  apply base_step_atomic_inv in Hstep; [ | by inversion 1 ].
  inv_base_step.
  monad_inv.
  iMod "Hclo". iIntros.
  destruct (decide (all_synced _)) as [Ha|Hna].
  - rewrite difference_empty_L.
    iMod ("Hupd") as (m) "(Hm&Hclo')".
    iAssert (⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝)%I with "[-]" as "%Hsynced".
    {
      iIntros (k bs Hin).
      iDestruct (big_sepM_lookup_acc with "[$]") as "(Hk&_)"; eauto.
      iDestruct (gen_heap.gen_heap_valid with "[$] [$]") as %Hlook.
      iPureIntro. eapply Ha in Hlook. eauto.
    }
    monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iFrame. rewrite big_sepL_nil right_id.
    iMod ("Hclo'" with "[$Hm //]") as "HΦ".
    iFrame. iApply wp_value. iApply ("HΦ" with "[-]").
    simpl. iFrame.
  - monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iFrame. rewrite big_sepL_nil right_id.
    iApply ("IH" with "[$] [$]").
  Qed.

Lemma wp_Barrier_triple E' (Q: iProp Σ) m :
  {{{ |NC={⊤,E'}=> ([∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs)) ∗
                   (⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝ ∗
                    ([∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs))-∗ |NC={E',⊤}=> Q)}}}
    Barrier #()
  {{{ RET #(); Q }}}.
Proof.
  iIntros (Φ) "Hupd HΦ". iApply (wp_Barrier_atomic with "[//]").
  rewrite difference_empty_L.
  iNext.
  iMod "Hupd" as "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists m.
  iFrame. iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Barrier m :
  {{{ ▷ [∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs) }}}
    Barrier #()
  {{{ RET LitV LitUnit;
      ⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝ ∗
         [∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs) }}}.
Proof.
  iIntros (Φ) ">H HΦ".
  wp_apply (wp_Barrier_atomic with "[//]").
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists m.
  iFrame. iIntros "Hda". iMod "HcloseE" as "_".
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.


Lemma wpc_Read stk E1 (a: u64) aset q b :
  {{{ uint.Z a d↦{q}[aset] b }}}
    Read #a @ stk; E1
  {{{ s, RET slice_val s;
      uint.Z a d↦{q}[aset] b ∗
      own_slice s byteT (DfracOwn 1) (Block_to_vals b) }}}
  {{{ uint.Z a d↦{q}[aset] b }}}.
Proof.
  iIntros (Φ Φc) "Hda HΦ".
  rewrite /Read.
  wpc_pures.
  { by crash_case. }
  wpc_bind (ExternalOp _ _).
  assert (Atomic (StronglyAtomic) (ExternalOp ReadOp #a)).
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7.
    subst. eauto. }
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
    (Φc ∧ |NC={E1,E1'}=> ∃ aset b0, uint.Z a d↦[aset] b0 ∗
            ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b -∗ |NC={E1',E1}=>
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
  { solve_atomic. inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7.
    inversion H8. subst. inversion H13. eauto. }
  wpc_atomic.
  iRight in "Hfupd".
  iMod "Hfupd" as (aset b0) "[Hda HQ]".
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iFrame. by iApply slice_to_block_array. }
  iIntros "H". iDestruct "H" as (b' Hdisj) "[Hda Hmapsto]".
  iMod ("HQ" with "[$Hda]") as "HQ"; eauto.
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
    (Φc ∧ |={E1,E1'}=> ∃ aset b0, uint.Z a d↦[aset] b0 ∗
           ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b ={E1',E1}=∗
          Φc ∧ (is_block s q b -∗ Φ #()))) -∗
    WPC Write #a (slice_val s) @ stk; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (??) "Hblock HΦc".
  wpc_apply (wpc_Write_ncfupd with "[$]").
  iSplit.
  - by iLeft in "HΦc".
  - iRight in "HΦc". iApply fupd_ncfupd. iMod "HΦc" as (??) "(?&H1)".
    iModIntro. iExists _, _. iFrame. iNext. iIntros (?) "H2".
      by iMod ("H1" with "[$]").
Qed.

Theorem wpc_Write_fupd_triple {stk E1} E1' (Q Qc: iProp Σ) (a: u64) s q b :
  {{{ is_block s q b ∗
      (Qc ∧ |={E1,E1'}=> ∃ aset b0, uint.Z a d↦[aset] b0 ∗ ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b ={E1',E1}=∗ Qc ∧ Q)) }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); is_block s q b ∗ Qc ∧ Q }}}
  {{{ Qc }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hs Hfupd]".
  iApply (wpc_Write_fupd with "Hs"). iSplit.
  { iLeft in "Hfupd". iLeft in "HΦ". iApply "HΦ". iFrame. }
  iRight in "Hfupd". iMod "Hfupd" as (aset b0) "[Hv Hclose]". iModIntro.
  iExists aset, b0. iFrame. iIntros "!>" (b') "Hv". iMod ("Hclose" with "Hv") as "HQ".
  iModIntro. iSplit.
  { iLeft in "HΦ". iLeft in "HQ". iApply "HΦ". iFrame. }
  iRight in "HΦ". iIntros "Hblock". iApply "HΦ". iFrame.
Qed.

Theorem wpc_Write' stk E1 (a: u64) aset s q b0 b :
  {{{ uint.Z a d↦[aset] b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b ∗ is_block s q b }}}
  {{{ (uint.Z a d↦[aset] b0) ∨ (∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ uint.Z a d↦[b'] b) }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wpc_apply (wpc_Write_fupd with "[$Hs]").
  iSplit.
  { crash_case.
    eauto. }
  iModIntro.
  iExists _, _; iFrame.
  iIntros "!>" (b') "Hda !>".
  iSplit.
  { crash_case; eauto. }
  iRight in "HΦ".
  iIntros "Hb".
  iApply "HΦ"; iFrame.
Qed.

Theorem wpc_Write stk E1 (a: u64) s q b :
  {{{ ∃ aset b0, uint.Z a d↦[aset] b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); ∃ aset, uint.Z a d↦[aset] b ∗ is_block s q b }}}
  {{{ ∃ aset' b', uint.Z a d↦[aset'] b' }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as (aset b0) "[Hda Hs]".
  wpc_apply (wpc_Write' with "[$Hda $Hs]").
  iSplit.
  { iLeft in "HΦ". iIntros "[Hda|Hda]"; iApply "HΦ"; eauto.
    iDestruct "Hda" as (??) "H". iExists _, _; by iFrame. }
  iIntros "!> H". iDestruct "H" as (??) "H".
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

Lemma wpc_Barrier E1 m  :
  {{{ ▷ [∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs) }}}
    Barrier #() @ E1
    {{{ RET #();
        ⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝ ∗
          ([∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs))
      }}}
     {{{ ([∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs)) }}}.
Proof.
  iIntros (Φ Φc) ">Hd HΦ".
  Transparent async_disk_proph.Barrier.
  wpc_call.
  { eauto. }
  iLöb as "IH".
  Opaque async_disk_proph.Barrier.
  iApply wpc_lift_base_step_fupd; first by auto.
  iSplit; last first.
  { iModIntro. iLeft in "HΦ". iApply "HΦ". eauto. }
  iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd'&Htr) Hg".
  iApply (fupd_mask_intro); first set_solver+. iIntros "Hclo".
  cbv [ffi_local_ctx disk_interp].
  iSplit.
  { iPureIntro.
    destruct (decide (all_synced (σ1.(world)))).
    - eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      rewrite decide_True //. repeat (monad_simpl; cbn).
    - eexists _, _, _, _, _; cbn.
      constructor 1; cbn.
      repeat (monad_simpl; cbn).
      rewrite decide_False //. repeat (monad_simpl; cbn).
  }
  iNext; iIntros (v2 σ2 g2 efs Hstep).
  apply base_step_atomic_inv in Hstep; [ | by inversion 1 ].
  inv_base_step.
  monad_inv.
  iMod "Hclo". iIntros.
  destruct (decide (all_synced _)) as [Ha|Hna].
  - monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iAssert (⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝)%I with "[-]" as "%Hsynced".
    {
      iIntros (k bs Hin).
      iDestruct (big_sepM_lookup_acc with "[$]") as "(Hk&_)"; eauto.
      iDestruct (gen_heap.gen_heap_valid with "[$] [$]") as %Hlook.
      iPureIntro. eapply Ha in Hlook. eauto.
    }
    iFrame. rewrite big_sepL_nil right_id.
    iApply wpc_value.
    iModIntro. iSplit.
    * iFrame. iApply ("HΦ" with "[-]"). iFrame. eauto.
    * iLeft in "HΦ". iModIntro. iApply ("HΦ" with "[-]"). iFrame.
  - monad_inv.
    iMod (global_state_interp_le with "Hg") as "$".
    { apply step_count_next_incr. }
    iFrame. rewrite big_sepL_nil right_id.
    iApply ("IH" with "[$] [$]").
  Qed.

Lemma wpc_Barrier0 :
  {{{ True }}}
    Barrier #() @ ⊤
  {{{ RET #(); True }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "_ HΦ".
  wpc_apply (wpc_Barrier _ ∅); eauto.
  iSplit.
  - iIntros. iLeft in "HΦ". by iApply "HΦ".
  - iNext. iIntros. iRight in "HΦ". by iApply "HΦ".
Qed.

Lemma wpc_Barrier1 E1 a b0 b :
  {{{ ▷ a d↦[b0] b }}}
    Barrier #() @ E1
  {{{ RET #(); ⌜ b0 = b ⌝ ∗ a d↦[b0] b }}}
  {{{ a d↦[b0] b }}}.
Proof.
  iIntros (Φ Φc) ">Hd HΦ".
  wpc_apply (wpc_Barrier _ ({[ a := (b0, b)]}) with "[Hd]").
  { iNext.  rewrite big_sepM_singleton. iFrame. }
  iSplit.
  - rewrite ?big_sepM_singleton. iLeft in "HΦ". eauto.
  - rewrite ?big_sepM_singleton. iNext. iIntros "(%Hlookup&Ha)".
    iRight in "HΦ". iApply "HΦ". iFrame. iPureIntro.
    eapply (Hlookup a (b0, b)) => //=.
    rewrite lookup_singleton //.
Qed.

End goose.
