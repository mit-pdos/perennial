From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import util_proof.
From Goose.github_com.mit_pdos.goose_nfsd Require Import alloc.

Section proof.
Context `{!heapG Σ}.

Let N: namespace := nroot .@ "alloc".

Definition alloc_linv (max: u64) (l: loc) : iProp Σ :=
  ∃ (next: u64) (bitmap_s: Slice.t) (bits: list u8),
  "next" ∷ l ↦[Alloc.S :: "next"] #next ∗
  "bitmap" ∷ l ↦[Alloc.S :: "bitmap"] (slice_val bitmap_s) ∗
  "%Hnext_bound" ∷ ⌜int.Z next < int.Z max⌝ ∗
  "%Hbits_len" ∷ ⌜int.Z max = (8 * (Z.of_nat $ length bits))%Z⌝ ∗
  "Hbits" ∷ is_slice_small bitmap_s byteT 1 (b2val <$> bits).

Definition is_alloc (max: u64) (l: loc) : iProp Σ :=
  ∃ (mu_l: loc),
    "%Hmax_nonzero" ∷ ⌜0 < int.Z max⌝ ∗
    "#mu" ∷ readonly (l ↦[Alloc.S :: "mu"] #mu_l) ∗
    "#His_lock" ∷ is_lock N #mu_l (alloc_linv max l).

Global Instance is_alloc_persistent max l : Persistent (is_alloc max l).
Proof. apply _. Qed.

Lemma wp_MkAlloc (bitmap_s: Slice.t) (data: list u8) :
  0 < length data →
  8 * Z.of_nat (length data) < 2^64 →
  {{{ is_slice_small bitmap_s byteT 1 (b2val <$> data) }}}
    MkAlloc (slice_val bitmap_s)
  {{{ l, RET #l; is_alloc (U64 (8 * length data)) l }}}.
Proof.
  set (max := U64 (8 * length data)).
  intros Hlen_lb Hlen_ub.
  iIntros (Φ) "Hs HΦ".
  wp_call.
  wp_apply wp_new_free_lock.
  iIntros (mu_l) "Hl".
  wp_pures.
  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Halloc".
  iApply struct_fields_split in "Halloc".
  iNamed "Halloc".
  iMod (readonly_alloc_1 with "mu") as "#mu".
  iMod (alloc_lock N _ _ (alloc_linv max l) with "Hl [Hs next bitmap]") as "#Hl".
  { iNext.
    iExists _, _, _; iFrame.
    iPureIntro.
    subst max.
    split; word. }
  wp_pures.
  iApply "HΦ".
  iExists _; iFrame "#".
  iPureIntro.
  subst max; word.
Qed.

Lemma wp_incNext (max: u64) (l: loc) :
  0 < int.Z max →
  {{{ alloc_linv max l }}}
    Alloc__incNext #l
  {{{ (next': u64), RET #next'; ⌜int.Z next' < int.Z max⌝ ∗
                                alloc_linv max l }}}.
Proof.
  iIntros (Hbound Φ) "Hl HΦ".
  iNamed "Hl".
  wp_call.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  - wp_storeField.
    wp_loadField.
    iApply "HΦ".
    iSplit.
    + iPureIntro.
      word.
    + iExists _, _, _.
      iFrame "∗%".
  - wp_loadField.
    iApply "HΦ".
    iDestruct (is_slice_small_sz with "Hbits") as %Hsz_len.
    rewrite fmap_length in Hsz_len.
    rewrite word.unsigned_mul in Heqb.
    rewrite -> wrap_small in Heqb by word.
    change (int.Z 8) with 8 in Heqb.
    iSplit.
    + iPureIntro.
      revert Heqb. word.
    + iExists _, _, _.
      iFrame "∗%".
      iPureIntro.
      revert Heqb; word.
Qed.

Lemma wp_allocBit (max: u64) (l: loc) :
  {{{ is_alloc max l }}}
    Alloc__allocBit #l
  {{{ (n: u64), RET #n; ⌜int.Z n < int.Z max⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (typed_mem.wp_AllocAt uint64T); first by auto.
  iIntros (num_l) "num".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "[Hlocked Hlinv]".
  wp_apply (wp_incNext with "Hlinv"); auto.
  iIntros (?) "[%Hnext_bound Hlinv]".
  wp_store.
  wp_load.
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak (λ _, ∃ (num: u64),
                            "%Hnum_bound" ∷ ⌜int.Z num < int.Z max⌝ ∗
                            "num" ∷ num_l ↦[uint64T] #num ∗
                            "Hlinv" ∷ alloc_linv max l)%I
                        with "[] [num Hlinv]"); swap 1 2.
  - (* initial loop invariant *)
    iExists _; iFrame "∗%".
  - clear Φ.
    iIntros "!>" (Φ) "Hinv HΦ". iNamed "Hinv".
    wp_pures. wp_load. wp_load.
    wp_pures.
    wp_apply wp_DPrintf.
    wp_pures.
    iNamed "Hlinv".
    wp_loadField.
    assert (int.Z num / 8 < length bits).
    { apply Zdiv_lt_upper_bound; lia. }
    destruct (list_lookup_lt _ bits (Z.to_nat (int.Z num / 8)%Z)) as [b Hlookup].
    { apply Nat2Z.inj_lt.
      lia. }
    (* prove this separately since we need it twice *)
    assert ((b2val <$> bits) !! int.nat (word.divu num 8) = Some (b2val b)) as Hlookup'.
    { rewrite list_lookup_fmap.
      apply fmap_Some.
      eexists; split; eauto.
      rewrite word.unsigned_divu_nowrap; auto. }
    wp_apply (wp_SliceGet _ _ _ _ _ _ _ (b2val b) with "[$Hbits]"); first done.
    iIntros "[Hbits _]".
    wp_pures.
    wp_if_destruct.
    + wp_loadField.
      wp_apply (wp_SliceGet with "[$Hbits]"); first done.
      iIntros "[Hbits _]".
      wp_loadField.
      wp_apply (wp_SliceSet with "[$Hbits]").
      { iSplit; iPureIntro; auto.
        rewrite Hlookup'.
        eauto. }
      iIntros "Hbits".
      wp_pures.
      iApply "HΦ".
      iExists _; iFrame.
      iSplit; first by (iPureIntro; word).
      rewrite -list_fmap_insert.
      iExists _, _, _; iFrame "∗%".
      rewrite insert_length.
      iFrame "%".
    + wp_apply (wp_incNext max with "[next bitmap Hbits]"); first done.
      { iExists _, _, _; iFrame "∗%". }
      iIntros (next'') "[%Hnext'' Hlinv]".
      wp_store.
      wp_load.
      wp_if_destruct.
      { wp_store.
        iApply "HΦ".
        iExists _; iFrame "∗%". }
      iApply "HΦ".
      iExists _; iFrame "∗%".
  - iNamed 1.
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$His_lock $Hlocked $Hlinv]").
    wp_load.
    iApply "HΦ".
    iPureIntro; done.
Qed.

End proof.
