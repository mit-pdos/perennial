From New.proof Require Import proof_prelude.
From New Require Export atomic_fupd.
Require Import New.code.github_com.goose_lang.primitive.disk.
Require Import New.generatedproof.github_com.goose_lang.primitive.disk.
Require Import Perennial.goose_lang.ffi.disk.
Require Import Perennial.goose_lang.ffi.disk_prelude.

Section wps.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_inst : IsPkgInit (PROP:=iProp Σ) disk :=
  ltac2:(build_pkg_init ()).

Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_block (s:slice.t) (q: dfrac) (b:Block) :=
  own_slice s q (vec_to_list b).

Definition is_block_full (s:slice.t) (b:Block) :=
  own_slice s (DfracOwn 1) (vec_to_list b).

Global Instance is_block_timeless s q b :
  Timeless (is_block s q b) := _.

Global Instance is_block_dfractional s b :
  DFractional (λ dq, is_block s dq b).
Proof. apply _. Qed.

Theorem is_block_not_nil s q b :
  is_block s q b -∗
  ⌜ s ≠ slice.nil ⌝.
Proof.
  iIntros "Hb".
  rewrite /is_block.
  iDestruct (own_slice_not_null with "Hb") as "%Hnull"; eauto.
  { rewrite go_type_size_unseal //. }
  { rewrite length_vec_to_list.
    rewrite /block_bytes. lia. }
  iPureIntro.
  destruct s. rewrite /slice.nil. simpl in *. congruence.
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
  rewrite length_vec_to_list //.
Qed.

Theorem block_to_list_to_block i :
  list_to_block (vec_to_list i) = i.
Proof.
  symmetry.
  apply block_list_inj.
  auto.
Qed.

Lemma slice_to_block_array s q b :
  own_slice s q (vec_to_list b) -∗ pointsto_block s.(slice.ptr_f) q b.
Proof.
  rewrite /pointsto_block heap_array_to_list.
  rewrite own_slice_unseal /own_slice_def.
  iIntros "[Ha %]".
  rewrite big_sepL_fmap.
  iApply (big_sepL_impl with "Ha"); simpl.
  iModIntro.
  iIntros (i x) "% Hl".
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  rewrite to_val_unseal. simpl.
  rewrite go_type_size_unseal. simpl.
  rewrite loc_add_0.
  replace (Z.mul 1%nat i) with (Z.of_nat i) by word.
  iDestruct "Hl" as "[Hl _]".
  iFrame.
Qed.

Lemma block_array_to_slice_mk l q (b: Block) :
  pointsto_block l q b -∗ own_slice (slice.mk l (length b) (length b)) q (vec_to_list b).
Proof.
  intros.
  rewrite /pointsto_block heap_array_to_list.
  rewrite own_slice_unseal /own_slice_def.
  iIntros "Hb".
  rewrite big_sepL_fmap.
  iDestruct (big_sepL_impl with "Hb []") as "$"; eauto.
  2: {
    iPureIntro. simpl.
    rewrite length_vec_to_list.
    assert (block_bytes < 2^64)%Z.
    { unfold block_bytes. lia. }
    word.
  }
  iModIntro.
  iIntros (i x) "% Hl".
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  rewrite to_val_unseal. simpl.
  rewrite go_type_size_unseal. simpl.
  rewrite loc_add_0.
  replace (Z.mul 1%nat i) with (Z.of_nat i) by word.
  iFrame.
Qed.

Lemma block_array_to_slice s q (b: Block) :
  length b = uint.nat s.(slice.len_f) ->
  uint.Z s.(slice.len_f) ≤ uint.Z s.(slice.cap_f) ->
  pointsto_block s.(slice.ptr_f) q b -∗ own_slice s q (vec_to_list b).
Proof.
  intros.
  rewrite /pointsto_block heap_array_to_list.
  rewrite own_slice_unseal /own_slice_def.
  iIntros "Hb".
  rewrite big_sepL_fmap.
  iDestruct (big_sepL_impl with "Hb []") as "$"; eauto.
  iModIntro.
  iIntros (i x) "% Hl".
  rewrite typed_pointsto_unseal /typed_pointsto_def.
  rewrite to_val_unseal. simpl.
  rewrite go_type_size_unseal. simpl.
  rewrite loc_add_0.
  replace (Z.mul 1%nat i) with (Z.of_nat i) by word.
  iFrame.
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
  ⊢
  {{{ is_pkg_init disk ∗ own_slice s q (vec_to_list b) }}}
  <<< ∀∀ b0, uint.Z a d↦ b0 >>>
    disk@"Write" #a #s @@ ∅
  <<< uint.Z a d↦ b >>>
  {{{ RET #(); own_slice s q (vec_to_list b) }}}.
Proof.
  wp_start as "Hs".
  iDestruct (own_slice_len with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iApply (wp_ncatomic _ _ ∅).
  { solve_atomic. rewrite to_val_unseal in H.
    inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto. }
  rewrite difference_empty_L.
  iMod "HΦ" as (b0) "[Hda Hupd]"; iModIntro.
  rewrite to_val_unseal.
  iApply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0.
    iFrame.
    by iApply slice_to_block_array. }
  iModIntro.
  iIntros "[Hda Hmapsto]".
  iMod ("Hupd" with "Hda") as "HQ".
  iModIntro.
  iApply "HQ".
  iApply block_array_to_slice; eauto.
Qed.

Theorem wp_Write_triple E' (Q: iProp Σ) (a: u64) s q b :
  {{{ is_pkg_init disk ∗ own_slice s q (vec_to_list b) ∗
      (|NC={⊤,E'}=> ∃ b0, uint.Z a d↦ b0 ∗ (uint.Z a d↦ b -∗ |NC={E',⊤}=> Q)) }}}
    disk@"Write" #a #s
  {{{ RET #(); own_slice s q (vec_to_list b) ∗ Q }}}.
Proof.
  iIntros (Φ) "[#Hpkg [Hs Hupd]] HΦ".
  iApply (wp_Write_atomic with "[$Hpkg $Hs]").
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists b0.
  iFrame. iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write (a: u64) s q b :
  {{{ is_pkg_init disk ∗ ∃ b0, uint.Z a d↦ b0 ∗ own_slice s q (vec_to_list b) }}}
    disk@"Write" #a #s
  {{{ RET #(); uint.Z a d↦ b ∗ own_slice s q (vec_to_list b) }}}.
Proof.
  iIntros (Φ) "[#Hpkg Hpre] HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wp_apply (wp_Write_atomic with "[$Hs]").
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "Hclose". iExists _. iFrame.
  iIntros "Hda". iMod "Hclose" as "_".
  iIntros "!> Hs". iApply "HΦ". iFrame.
Qed.

Theorem wp_Write' (z: Z) (a: u64) s q b :
  {{{ is_pkg_init disk ∗ ⌜uint.Z a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ own_slice s q (vec_to_list b) }}}
    disk@"Write" #a #s
  {{{ RET #(); z d↦ b ∗ own_slice s q (vec_to_list b) }}}.
Proof.
  iIntros (Φ) "[#Hpkg [<- >Hpre]] HΦ".
  iApply (wp_Write with "[$Hpkg $Hpre]").
  eauto.
Qed.

Lemma wp_Read_atomic (a: u64) q :
  ⊢ {{{ is_pkg_init disk }}}
    <<< ∀∀ b, uint.Z a d↦{q} b >>>
      disk@"Read" #a @@ ∅
    <<< uint.Z a d↦{q} b >>>
    {{{ s, RET #s; is_block_full s b }}}.
Proof.
  wp_start as "_".
  wp_bind (ExternalOp _ _).
  rewrite difference_empty_L.
  iMod "HΦ" as (b) "[Hda Hupd]".
  { solve_atomic. rewrite to_val_unseal in H.
    inversion H. subst. monad_inv. inversion H0. subst. inversion H2. subst.
    inversion H4. subst. inversion H6. subst. inversion H7. econstructor. eauto. }
  rewrite to_val_unseal. simpl.
  iApply (wp_ReadOp with "Hda").
  iNext.
  iIntros (l) "(Hda&Hl)".
  iMod ("Hupd" with "Hda") as "HQ"; iModIntro.
  iDestruct (block_array_to_slice_mk with "Hl") as "Hs".
  iSpecialize ("HQ" with "Hs"). simpl.
  rewrite length_vec_to_list /block_bytes.
  replace (Z.of_nat (Z.to_nat 4096)) with 4096%Z by lia.
  wp_pures.
  rewrite to_val_unseal //.
Qed.

(*
Lemma wp_ReadTo_atomic (a: u64) b0 s q :
  ⊢ {{{ is_pkg_init disk ∗ is_block_full s b0 }}}
    <<< ∀∀ b, uint.Z a d↦{q} b >>>
      disk@"ReadTo" #a #s @@ ∅
    <<< uint.Z a d↦{q} b >>>
    {{{ RET #(); is_block_full s b }}}.
Proof.
  iIntros "!#" (Φ) "Hs Hupd".
  wp_rec. wp_pures.
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
*)

Lemma wp_Read_triple E' (Q: Block -> iProp Σ) (a: u64) q :
  {{{ is_pkg_init disk ∗
      |NC={⊤,E'}=> ∃ b, uint.Z a d↦{q} b ∗ (uint.Z a d↦{q} b -∗ |NC={E',⊤}=> Q b) }}}
    disk@"Read" #a
  {{{ s b, RET #s;
      Q b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "[#Hpkg Hupd] HΦ". iApply (wp_Read_atomic with "[$Hpkg]").
  rewrite difference_empty_L. iNext.
  iMod "Hupd" as (b0) "[Hda Hclose]".
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_". iMod ("Hclose" with "Hda").
  iIntros "!> * Hs". iApply "HΦ". iFrame.
Qed.

Lemma wp_Read (a: u64) q b :
  {{{ is_pkg_init disk ∗ uint.Z a d↦{q} b }}}
    disk@"Read" #a
  {{{ s, RET #s;
      uint.Z a d↦{q} b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "[#Hpkg Hda] HΦ".
  wp_apply wp_Read_atomic.
  iApply ncfupd_mask_intro; first set_solver+.
  iIntros "HcloseE". iExists _. iFrame.
  iIntros "Hda". iMod "HcloseE" as "_".
  iIntros "!> * Hs". iApply ("HΦ" with "[$]").
Qed.

Lemma wp_Read_eq (a: u64) (a': Z) q b :
  {{{ is_pkg_init disk ∗ a' d↦{q} b ∗ ⌜uint.Z a = a'⌝ }}}
    disk@"Read" #a
  {{{ s, RET #s;
      a' d↦{q} b ∗ is_block_full s b }}}.
Proof.
  iIntros (Φ) "[#Hpkg Hb] HΦ".
  iDestruct "Hb" as "[Hb %]". subst.
  wp_apply (wp_Read with "[$Hpkg $Hb]").
  iApply "HΦ".
Qed.

Lemma wp_Barrier :
  {{{ is_pkg_init disk }}}
    disk@"Barrier" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".
  iApply ("HΦ" with "[//]").
Qed.

End wps.
