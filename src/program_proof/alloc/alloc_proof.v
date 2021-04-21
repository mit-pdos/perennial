From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import util_proof.
From Goose.github_com.mit_pdos.goose_nfsd Require Import alloc.

(* TODO: this file isn't using typed_slice, should fix that *)

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

Lemma bits_lookup_byte (max: u64) (bits: list u8) (num: u64) :
  int.Z max = 8 * length bits →
  int.Z num < int.Z max →
  ∃ (b:u8), (b2val <$> bits) !! int.nat (word.divu num 8) = Some (b2val b).
Proof.
  intros Hmax Hnum.
  assert (int.Z num / 8 < length bits).
  { apply Zdiv_lt_upper_bound; lia. }
  destruct (list_lookup_lt _ bits (Z.to_nat (int.Z num / 8)%Z)) as [b Hlookup].
  { apply Nat2Z.inj_lt.
    word. }
  exists b.
  rewrite list_lookup_fmap.
  apply fmap_Some.
  eexists; split; eauto.
  rewrite word.unsigned_divu_nowrap; auto.
Qed.

(* TODO: identical to freeBit proof, would be nice to share some of this *)
Lemma wp_MarkUsed max l (bn: u64) :
  int.Z bn < int.Z max →
  {{{ is_alloc max l }}}
    Alloc__MarkUsed #l #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_apply (wp_SliceGet with "[$Hbits]"); first by eauto.
  iIntros "[Hbits _]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hbits]").
  { iSplit; iPureIntro; auto.
    rewrite Hlookup; eauto. }
  iIntros "Hbits".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$His_lock $Hlocked next bitmap Hbits]").
  { rewrite -list_fmap_insert.
    iExists _, _, _; iFrame "∗%".
    rewrite insert_length.
    iFrame "%". }
  by iApply "HΦ".
Qed.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_MkMaxAlloc (max: u64) :
  0 < int.Z max →
  int.Z max `mod` 8 = 0 →
  {{{ True }}}
    MkMaxAlloc #max
  {{{ l, RET #l; is_alloc max l }}}.
Proof.
  iIntros (Hbound Hmod Φ) "_ HΦ".
  wp_call.
  rewrite -> bool_decide_eq_true_2 by word.
  wp_pures.
  rewrite bool_decide_eq_true_2; last first.
  { repeat (f_equal; try word). }
  wp_pures.
  wp_apply wp_new_slice; first by auto.
  iIntros (bitmap_s) "Hs".
  wp_pures.
  iApply is_slice_to_small in "Hs".
  replace (replicate (int.nat (word.divu max 8)) (zero_val byteT))
          with (b2val <$> replicate (int.nat (word.divu max 8)) (U8 0));
    last first.
  { rewrite fmap_replicate //. }
  wp_apply (wp_MkAlloc with "[$Hs]").
  { rewrite replicate_length.
    word. }
  { rewrite replicate_length.
    word. }
  iIntros (a_l) "#Ha".
  rewrite replicate_length.
  wp_pures.
  wp_apply (wp_MarkUsed with "Ha").
  { word. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExactEq "Ha".
  f_equal.
  word.
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
    destruct (bits_lookup_byte max bits num) as [b Hlookup]; [ done | done | ].
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
        rewrite Hlookup.
        eauto. }
      iIntros "Hbits".
      wp_pures.
      iApply "HΦ".
      iExists _; iFrame.
      iModIntro.
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
        iExists _; iFrame "∗%". eauto. }
      iApply "HΦ".
      iExists _; iFrame "∗%"; eauto.
  - iNamed 1.
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[$His_lock $Hlocked $Hlinv]").
    wp_load.
    iApply "HΦ".
    iPureIntro; done.
Qed.

Lemma wp_freeBit max l (bn: u64) :
  int.Z bn < int.Z max →
  {{{ is_alloc max l }}}
    Alloc__freeBit #l #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_apply (wp_SliceGet with "[$Hbits]"); first by eauto.
  iIntros "[Hbits _]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hbits]").
  { iSplit; iPureIntro; auto.
    rewrite Hlookup; eauto. }
  iIntros "Hbits".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$His_lock $Hlocked next bitmap Hbits]").
  { rewrite -list_fmap_insert.
    iExists _, _, _; iFrame "∗%".
    rewrite insert_length.
    iFrame "%". }
  by iApply "HΦ".
Qed.

Lemma wp_AllocNum max l :
  {{{ is_alloc max l }}}
    Alloc__allocBit #l
  {{{ (n: u64), RET #n; ⌜int.Z n < int.Z max⌝ }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_apply (wp_allocBit with "H").
  done.
Qed.

Lemma wp_FreeNum max l (num: u64) :
  int.Z num < int.Z max →
  int.Z num ≠ 0 →
  {{{ is_alloc max l }}}
    Alloc__FreeNum #l #num
  {{{ RET #(); True }}}.
Proof.
  intros Hnum Hnonzero.
  iIntros (Φ) "H HΦ".
  wp_call.
  wp_if_destruct.
  { contradiction Hnonzero. word. }
  wp_apply (wp_freeBit with "H"); eauto.
  by iApply "HΦ".
Qed.

End proof.

Ltac Zify.zify_post_hook ::= idtac.
