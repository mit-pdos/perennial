From Perennial.program_proof Require Import async_disk_prelude.

Section goose.
Context `{!heapGS Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

(* TODO: these are common with disk_lib, but we don't want to import disk_lib *)
Definition is_block (s:Slice.t) (q: Qp) (b:Block) :=
  is_slice_small s byteT q (Block_to_vals b).

Definition is_block_full (s:Slice.t) (b:Block) :=
  is_slice s byteT 1 (Block_to_vals b).

Global Instance is_block_timeless s q b :
  Timeless (is_block s q b) := _.

Global Instance is_block_fractional s b :
  fractional.Fractional (λ q, is_block s q b).
Proof. apply is_slice_small_fractional. Qed.

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
  iApply (byte_mapsto_untype with "Hl").
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
  rewrite byte_mapsto_untype //.
Qed.

Lemma slice_to_block_array s q b :
  is_slice_small s byteT q (Block_to_vals b) -∗ mapsto_block s.(Slice.ptr) q b.
Proof.
  rewrite /is_slice_small.
  iIntros "[Ha _]".
  by iApply array_to_block_array.
Qed.

Lemma block_array_to_slice l q b cap :
  mapsto_block l q b -∗ is_slice_small (Slice.mk l 4096 cap) byteT q (Block_to_vals b).
Proof.
  iIntros "Hm".
  rewrite /is_slice_small.
  iSplitL.
  { by iApply array_to_block_array. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl.
  reflexivity.
Qed.

Transparent disk.Read disk.Write.

Theorem wp_Write_atomic (a: u64) s q b :
  ⊢ {{{ is_slice_small s byteT q (Block_to_vals b) }}}
  <<< ∀∀ aset b0, int.Z a d↦[aset] b0 >>>
    Write #a (slice_val s) @ ∅
  <<<▷ ∃ b',⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b >>>
  {{{ RET #(); is_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  wp_call.
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  iApply (wp_ncatomic _ _ ∅).
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
  rewrite /is_slice_small.
  iFrame.
  iSplitL; auto.
  by iApply array_to_block_array.
Qed.

Theorem wp_Write_triple E' (Q: iProp Σ) (a: u64) s q b :
  {{{ is_slice_small s byteT q (Block_to_vals b) ∗
      (|NC={⊤,E'}=> ∃ aset b0, int.Z a d↦[aset] b0 ∗
                    ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b -∗ |NC={E',⊤}=> Q)) }}}
    Write #a (slice_val s)
  {{{ RET #(); is_slice_small s byteT q (Block_to_vals b) ∗ Q }}}.
Proof.
  iIntros (Φ) "[Hs Hupd] HΦ". iApply (wp_Write_atomic with "Hs").
  rewrite difference_empty_L.
  iMod "Hupd" as (aset b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists aset, b0.
  iFrame. iIntros "!> Hda". iMod "HcloseE" as "_". iDestruct "Hda" as (?) "Hda". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write (a: u64) aset s q b0 b :
  {{{ int.Z a d↦[aset] b0 ∗ is_slice_small s byteT q (Block_to_vals b) }}}
    Write #a (slice_val s)
  {{{ RET #();
      ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b ∗ is_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "[Hda Hs]".
  wp_apply (wp_Write_atomic with "Hs").
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "Hclose". iExists _, _. iFrame.
  iIntros "!> Hda". iMod "Hclose" as "_".
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write' (z: Z) (a: u64) aset s q b b0 :
  {{{ ⌜int.Z a = z⌝ ∗ ▷ (z d↦[aset] b0 ∗ is_slice_small s byteT q (Block_to_vals b)) }}}
    Write #a (slice_val s)
  {{{ RET #();
      ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗
      z d↦[b'] b ∗ is_slice_small s byteT q (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "[<- >Hpre] HΦ".
  iApply (wp_Write with "[$Hpre]").
  eauto.
Qed.

Lemma wp_Read_atomic (a: u64) q :
  ⊢ <<< ∀∀ aset b, int.Z a d↦{q}[aset] b >>>
      Read #a @ ∅
    <<<▷ int.Z a d↦{q}[aset] b >>>
    {{{ s, RET slice_val s; is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hupd".
  wp_call.
  wp_bind (ExternalOp _ _).
  rewrite difference_empty_L.
  iMod "Hupd" as (? b) "[Hda Hupd]".
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ"; iModIntro.
  iDestruct (block_array_to_slice _ _ _ 4096 with "Hl") as "Hs".
  wp_pures.
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iApply "HQ"; iFrame.
Qed.

Lemma wp_ReadTo_atomic (a: u64) b0 s q :
  ⊢ {{{ is_block_full s b0 }}}
  <<< ∀∀ aset b, int.Z a d↦{q}[aset] b >>>
      ReadTo #a (slice_val s) @ ∅
    <<< ▷ int.Z a d↦{q}[aset] b >>>
    {{{ RET #(); is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_call.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  wp_bind (ExternalOp _ _).
  iApply (wp_ncatomic _ _ ∅).
  rewrite difference_empty_L.
  iMod "Hupd" as (aset db0) "[Hda Hupd]"; iModIntro.
  wp_apply (wp_ReadOp with "[$Hda]").
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ".
  iModIntro.
  wp_pures.
  wp_apply wp_slice_ptr.
  iDestruct "Hs" as "[Hs Hcap]".
  rewrite /is_slice_small.
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
  rewrite /is_block_full /is_slice /is_slice_small.
  iFrame.
  iPureIntro.
  move: Hsz; rewrite !length_Block_to_vals //.
Qed.

Lemma wp_Read_triple E' (Q: Block -> iProp Σ) (a: u64) q :
  {{{ |NC={⊤,E'}=> ∃ aset b, int.Z a d↦{q}[aset] b ∗ ▷ (int.Z a d↦{q}[aset] b -∗ |NC={E',⊤}=> Q b) }}}
    Read #a
  {{{ s b, RET slice_val s;
      Q b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hupd HΦ". iApply wp_Read_atomic.
  rewrite difference_empty_L.
  iMod "Hupd" as (aset b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _, _. iFrame.
  iIntros "!> Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> * Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Read (a: u64) q b aset :
  {{{ int.Z a d↦{q}[aset] b }}}
    Read #a
  {{{ s, RET slice_val s;
      int.Z a d↦{q}[aset] b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "Hda HΦ".
  wp_apply wp_Read_atomic.
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _, _. iFrame.
  iIntros "!> Hda". iMod "HcloseE" as "_".
  iIntros "!> * Hs". iApply ("HΦ" with "[$]").
Qed.

Theorem wp_Barrier_atomic :
  ⊢ {{{ True }}}
  <<< ∀∀ m, [∗ map] a ↦ bs ∈ m, a d↦[fst bs] (snd bs) >>>
    Barrier #() @ ∅
  <<<(⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝ ∗
         [∗ map] a ↦ bs ∈ m, a d↦[(fst bs)] (snd bs)) >>>
  {{{ RET #(); True }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  (* TODO: why does this have to be made transparent whereas the others don't ?? *)
  Transparent async_disk_proph.Barrier.
  iLöb as "IH".
  wp_rec.
  Opaque async_disk_proph.Barrier.
  wp_bind (ExternalOp _ _).
  (* TODO: I don't see how to directly derive this from BarrierOp because
     I only want to fire the opening fupd if the barrier in fact succeeds *)
  iApply ectx_lifting.wp_lift_atomic_head_step_no_fork_nc; first by auto.
  iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
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
  apply head_step_atomic_inv in Hstep; [ | by inversion 1 ].
  iMod (global_state_interp_le with "Hg") as "$".
  { apply step_count_next_incr. }
  inversion Hstep; subst; clear Hstep.
  simpl in H.
  monad_inv.
  destruct (decide (all_synced _)) as [Ha|Hna].
  - rewrite difference_empty_L.
    iMod "Hupd" as (m) "[Hda Hupd]".
    iAssert (⌜ (∀ k bs, m !! k = Some bs → fst bs = snd bs) ⌝)%I with "[-]" as "%Hsynced".
    {
      iIntros (k bs Hin).
      iDestruct (big_sepM_lookup_acc with "[$]") as "(Hk&_)"; eauto.
      iDestruct (gen_heap.gen_heap_valid with "[$] [$]") as %Hlook.
      iPureIntro. eapply Ha in Hlook. eauto.
    }
    monad_inv.
    iFrame.
    iMod ("Hupd" with "[-]") as "H".
    { iFrame. eauto. }
    iModIntro. iSplit; first done. simpl. wp_pures. iModIntro. iApply ("H" with "[//]").
  - iModIntro; iSplit; first done.
    monad_inv.
    iFrame. simpl. wp_pures. 
    iApply "IH"; eauto.
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
  {{{ int.Z a d↦{q}[aset] b }}}
    Read #a @ stk; E1
  {{{ s, RET slice_val s;
      int.Z a d↦{q}[aset] b ∗
      is_slice s byteT 1%Qp (Block_to_vals b) }}}
  {{{ int.Z a d↦{q}[aset] b }}}.
Proof.
  iIntros (Φ Φc) "Hda HΦ".
  rewrite /Read.
  wpc_pures.
  { by crash_case. }
  wpc_bind (ExternalOp _ _).
  wpc_atomic; iFrame.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl)".
  iDestruct (block_array_to_slice _ _ _ 4096 with "Hl") as "Hs".
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
    (Φc ∧ |NC={E1,E1'}=> ∃ aset b0, int.Z a d↦[aset] b0 ∗
            ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b -∗ |NC={E1',E1}=>
          Φc ∧ (is_block s q b -∗ Φ #()))) -∗
    WPC Write #a (slice_val s) @ stk; E1 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (Φ Φc) "Hs Hfupd".
  rewrite /Write /slice.ptr.
  wpc_pures.
  { iLeft in "Hfupd". iFrame. }
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
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
    replace sz with (U64 4096).
    + by iApply block_array_to_slice.
    + rewrite length_Block_to_vals in Hsz.
      change block_bytes with (Z.to_nat 4096) in Hsz.
      word.
Qed.

(* This is a TaDA-syle logically atomic spec, so the HoCAP-style sugar does not work. *)
Theorem wpc_Write_fupd {stk E1} E1' (a: u64) s q b :
  ∀ Φ Φc,
    is_block s q b -∗
    (Φc ∧ |={E1,E1'}=> ∃ aset b0, int.Z a d↦[aset] b0 ∗
           ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b ={E1',E1}=∗
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
      (Qc ∧ |={E1,E1'}=> ∃ aset b0, int.Z a d↦[aset] b0 ∗ ▷ (∀ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b ={E1',E1}=∗ Qc ∧ Q)) }}}
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
  {{{ int.Z a d↦[aset] b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); ∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b ∗ is_block s q b }}}
  {{{ (int.Z a d↦[aset] b0) ∨ (∃ b', ⌜ b' = aset ∨ b' = b ⌝ ∗ int.Z a d↦[b'] b) }}}.
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
  iExists _. iFrame.
Qed.

Theorem wpc_Write stk E1 (a: u64) s q b :
  {{{ ∃ aset b0, int.Z a d↦[aset] b0 ∗ is_block s q b }}}
    Write #a (slice_val s) @ stk; E1
  {{{ RET #(); ∃ aset, int.Z a d↦[aset] b ∗ is_block s q b }}}
  {{{ ∃ aset' b', int.Z a d↦[aset'] b' }}}.
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
  iExists _. iFrame.
Qed.

Theorem slice_to_block s q bs :
  s.(Slice.sz) = 4096 ->
  is_slice_small s byteT q (b2val <$> bs) -∗
  mapsto_block s.(Slice.ptr) q (list_to_block bs).
Proof.
  iIntros (Hsz) "Hs".
  rewrite /is_slice_small.
  iDestruct "Hs" as "[Hl %]".
  rewrite fmap_length in H.
  iApply (array_to_block with "Hl").
  assert (int.Z (Slice.sz s) = 4096).
  { rewrite Hsz. reflexivity. }
  lia.
Qed.

Lemma wpc_Barrier1 E1 a b0 b :
  {{{ ▷ a d↦[b0] b }}}
    Barrier #() @ E1
  {{{ RET #(); ⌜ b0 = b ⌝ ∗ a d↦[b0] b }}}
  {{{ a d↦[b0] b }}}.
Proof.
  iIntros (Φ Φc) ">Hd HΦ".
  iLöb as "IH".
  Transparent async_disk_proph.Barrier.
  wpc_call.
  { eauto. }
  Opaque async_disk_proph.Barrier.
  wpc_bind_seq.
  wpc_atomic.
  { eauto. }
  wp_apply (wp_BarrierOp _ _ ({[ a := (b0, b)]}) with "[Hd]").
  { iNext.  rewrite big_sepM_singleton. iFrame. }
  iIntros (bl). destruct bl.
  - iIntros "(%Heq&H)".
    rewrite big_sepM_singleton.
    iSplit.
    { iLeft in "HΦ". iApply "HΦ". eauto. }
    iModIntro. wpc_pures.
    { iLeft in "HΦ". iApply "HΦ". eauto. }
    iRight in "HΦ".
    iApply ("HΦ" with "[-]").
    { iFrame. iPureIntro. eapply (Heq a (b0, b)) => //=.
      rewrite lookup_singleton //. }
  - iIntros "(_&H)".
    rewrite big_sepM_singleton.
    iSplit.
    { iLeft in "HΦ". iApply "HΦ". eauto. }
    iModIntro. wpc_pures.
    { iLeft in "HΦ". iApply "HΦ". eauto. }
    iApply ("IH" with "[$]"). iSplit.
    * iLeft in "HΦ". eauto.
    * iNext. iRight in "HΦ". eauto.
Qed.

End goose.
