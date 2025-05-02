Require Import New.generatedproof.github_com.mit_pdos.go_journal.alloc.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.
Require Import New.proof.sync.

From Perennial.Helpers Require Import bytes.

Lemma Z_u8_to_u64 (x:w8) : uint.Z (W64 (uint.Z x)) = uint.Z x.
Proof.
  rewrite /W64.
  rewrite word.unsigned_of_Z_nowrap //.
  pose proof (word.unsigned_range x).
  lia.
Qed.

Lemma and_1_u8 (x: u8) : 0 ≤ uint.Z (word.and x (W8 1)) ≤ 1.
Proof.
  assert (Lt ≠ Gt) by congruence.
  assert (Eq ≠ Gt) by congruence.
  byte_cases x; vm_compute; auto.
Qed.

Section proof.
Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

Program Instance : IsPkgInit alloc.alloc := ltac2:(build_pkg_init ()).

Definition alloc_linv (max: u64) (l: loc) : iProp Σ :=
  ∃ (next: u64) (bitmap_s: slice.t) (bits: list u8),
  "next" ∷ l ↦s[alloc.Alloc :: "next"] next ∗
  "bitmap" ∷ l ↦s[alloc.Alloc :: "bitmap"] bitmap_s ∗
  "%Hnext_bound" ∷ ⌜uint.Z next < uint.Z max⌝ ∗
  "%Hbits_len" ∷ ⌜uint.Z max = (8 * (Z.of_nat $ length bits))%Z⌝ ∗
  "Hbits" ∷ own_slice bitmap_s (DfracOwn 1) bits.

Definition is_alloc (max: u64) (l: loc) : iProp Σ :=
  ∃ (mu_l: loc),
    "%Hmax_nonzero" ∷ ⌜0 < uint.Z max⌝ ∗
    "#mu" ∷ l ↦s[alloc.Alloc :: "mu"]□ mu_l ∗
    "#His_lock" ∷ is_Mutex mu_l (alloc_linv max l).

Global Instance is_alloc_persistent max l : Persistent (is_alloc max l).
Proof. apply _. Qed.

Lemma wp_MkAlloc (bitmap_s: slice.t) (data: list u8) :
  0 < length data →
  8 * Z.of_nat (length data) < 2^64 →
  {{{ is_pkg_init alloc.alloc ∗
      own_slice bitmap_s (DfracOwn 1) data }}}
    alloc.alloc@"MkAlloc" #bitmap_s
  {{{ l, RET #l; is_alloc (W64 (8 * length data)) l }}}.
Proof.
  set (max := W64 (8 * length data)).
  intros Hlen_lb Hlen_ub.
  wp_start as "Hs".
  wp_auto.
  wp_alloc mu_l as "Hl".
  wp_auto.
  wp_alloc l as "Halloc".
  iApply struct_fields_split in "Halloc".
  iNamed "Halloc".
  iPersist "Hmu".
  iMod (init_Mutex with "Hl [Hs Hnext Hbitmap]") as "#Hl".
  2: {
    wp_auto.
    iApply "HΦ".
    iFrame "#". subst max; word.
  }
  iFrame.
  simpl; subst max; word.
Qed.

Lemma bits_lookup_byte (max: u64) (bits: list u8) (num: u64) :
  uint.Z max = 8 * length bits →
  uint.Z num < uint.Z max →
  ∃ (b:u8), bits !! uint.nat (word.divu num 8) = Some b.
Proof.
  intros Hmax Hnum.
  assert (uint.Z num / 8 < length bits).
  { apply Zdiv_lt_upper_bound; lia. }
  destruct (list_lookup_lt bits (Z.to_nat (uint.Z num / 8)%Z)) as [b Hlookup].
  { apply Nat2Z.inj_lt.
    word. }
  exists b.
  rewrite word.unsigned_divu_nowrap; auto.
Qed.

(* TODO: identical to freeBit proof, would be nice to share some of this *)
Lemma wp_MarkUsed max l (bn: u64) :
  uint.Z bn < uint.Z max →
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"MarkUsed" #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  wp_start as "H".
  iNamed "H".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$His_lock]").
  iIntros "[Hlocked Hlinv]".
  iNamed "Hlinv".
  wp_auto.
  iDestruct (own_slice_len with "Hbits") as "%Hbitslen".
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  apply mk_is_Some in Hlookup as Hlookupsome.
  apply lookup_lt_is_Some in Hlookupsome.

  (* XXX *)
  wp_pure.
  { word. }

  (* XXX why doesn't [wp_auto] work? *)
  wp_apply (wp_load_slice_elem with "[$Hbits]"); first eauto. iIntros "Hbits".

  wp_auto.

  (* XXX *)
  wp_pure; first word.

  (* XXX *)
  wp_apply (wp_store_slice_elem with "[$Hbits]"); first word. iIntros "Hbits".

  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked $next $bitmap $Hbits]").
  { rewrite length_insert. done. }

  iApply "HΦ". done.
Qed.

(*
Lemma wp_MkMaxAlloc (max: u64) :
  0 < uint.Z max →
  uint.Z max `mod` 8 = 0 →
  {{{ True }}}
    MkMaxAlloc #max
  {{{ l, RET #l; is_alloc max l }}}.
Proof.
  iIntros (Hbound Hmod Φ) "_ HΦ".
  wp_rec. wp_pures.
  rewrite -> bool_decide_eq_true_2 by word.
  wp_pures.
  rewrite bool_decide_eq_true_2; last first.
  { repeat (f_equal; try word). }
  wp_pures.
  wp_apply wp_new_slice; first by auto.
  iIntros (bitmap_s) "Hs".
  wp_pures.
  iApply own_slice_to_small in "Hs".
  replace (replicate (uint.nat (word.divu max 8)) (zero_val byteT))
          with (b2val <$> replicate (uint.nat (word.divu max 8)) (W8 0));
    last first.
  { rewrite fmap_replicate //. }
  wp_apply (wp_MkAlloc with "[$Hs]").
  { rewrite length_replicate.
    word. }
  { rewrite length_replicate.
    word. }
  iIntros (a_l) "#Ha".
  rewrite length_replicate.
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
  0 < uint.Z max →
  {{{ alloc_linv max l }}}
    Alloc__incNext #l
  {{{ (next': u64), RET #next'; ⌜uint.Z next' < uint.Z max⌝ ∗
                                alloc_linv max l }}}.
Proof.
  iIntros (Hbound Φ) "Hl HΦ".
  iNamed "Hl".
  wp_rec. wp_pures.
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
    iDestruct (own_slice_small_sz with "Hbits") as %Hsz_len.
    rewrite length_fmap in Hsz_len.
    rewrite word.unsigned_mul in Heqb.
    rewrite -> wrap_small in Heqb by word.
    change (uint.Z 8) with 8 in Heqb.
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
  {{{ (n: u64), RET #n; ⌜uint.Z n < uint.Z max⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec. wp_pures.
  wp_apply (wp_ref_of_zero); first by auto.
  iIntros (num_l) "num".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "His_lock").
  iIntros "[Hlocked Hlinv]".
  wp_apply (wp_incNext with "Hlinv"); auto.
  iIntros (?) "[%Hnext_bound Hlinv]".
  wp_store.
  wp_load.
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak (λ _, ∃ (num: u64),
                            "%Hnum_bound" ∷ ⌜uint.Z num < uint.Z max⌝ ∗
                            "num" ∷ num_l ↦[uint64T] #num ∗
                            "Hlinv" ∷ alloc_linv max l)%I
                        with "[] [num Hlinv]"); swap 1 2.
  - (* initial loop invariant *)
    iExists _; iFrame "∗%".
  - clear Φ.
    iIntros "!>" (Φ) "Hinv HΦ". iNamed "Hinv".
    wp_pures. wp_load. wp_load.
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
      { iSplit; iPureIntro; [ done | auto ]. }
      iIntros "Hbits".
      wp_pures.
      iApply "HΦ".
      rewrite -list_fmap_insert.
      iExists _; iFrame "∗%".
      by rewrite length_insert.
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
    wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked $Hlinv]").
    wp_load.
    iApply "HΦ".
    iPureIntro; done.
Qed.

Lemma wp_freeBit max l (bn: u64) :
  uint.Z bn < uint.Z max →
  {{{ is_alloc max l }}}
    Alloc__freeBit #l #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_apply (wp_SliceGet with "[$Hbits]"); first by eauto.
  iIntros "[Hbits _]".
  wp_loadField.
  wp_apply (wp_SliceSet with "[$Hbits]").
  { iSplit; iPureIntro; [ done | auto ]. }
  iIntros "Hbits".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked next bitmap Hbits]").
  { rewrite -list_fmap_insert.
    iExists _, _, _; iFrame "∗%".
    rewrite length_insert.
    iFrame "%". }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_AllocNum max l :
  {{{ is_alloc max l }}}
    Alloc__AllocNum #l
  {{{ (n: u64), RET #n; ⌜uint.Z n < uint.Z max⌝ }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_rec. wp_pures.
  wp_apply (wp_allocBit with "H").
  iIntros (n Hlt).
  wp_pures. iModIntro.
  iApply "HΦ". auto.
Qed.

Lemma wp_FreeNum max l (num: u64) :
  uint.Z num < uint.Z max →
  uint.Z num ≠ 0 →
  {{{ is_alloc max l }}}
    Alloc__FreeNum #l #num
  {{{ RET #(); True }}}.
Proof.
  intros Hnum Hnonzero.
  iIntros (Φ) "H HΦ".
  wp_rec. wp_pures.
  wp_if_destruct.
  wp_apply (wp_freeBit with "H"); eauto.
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_popCnt (b: u8) :
  {{{ True }}}
    popCnt #b
  {{{ (n: u64), RET #n; ⌜uint.Z n ≤ 8⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply (wp_ref_of_zero); auto.
  iIntros (count_l) "Hcount".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (x_l) "Hx".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (i_l) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ (x: u8) (count: u64),
                           "Hx" ∷ x_l ↦[byteT] #x ∗
                           "Hcount" ∷ count_l ↦[uint64T] #count ∗
                           "%Hcount_bound" ∷ ⌜uint.Z count ≤ uint.Z i⌝)%I
              with "[] [Hx Hcount $Hi]").
  - word.
  - clear.
    iIntros (i Φ) "!> Hpre HΦ".
    iDestruct "Hpre" as "(Hpre & Hi & %Hi)".
    iNamed "Hpre".
    wp_pures.
    wp_load. wp_load. wp_store. wp_load. wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame "Hi".
    iExists _, _; iFrame.
    iPureIntro.
    pose proof (and_1_u8 x).
    word.
  - iExists _, _; iFrame.
    iPureIntro.
    word.
  - iIntros "[Hinv _]".
    iNamed "Hinv".
    wp_pures. wp_load.
    iModIntro.
    iApply "HΦ".
    word.
Qed.

Lemma wp_NumFree max l :
  {{{ is_alloc max l }}}
    Alloc__NumFree #l
  {{{ (n:u64), RET #n; ⌜0 ≤ uint.Z n ≤ uint.Z max⌝}}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "[$]").
  iIntros "[Hlocked Hlinv]".
  wp_pures.
  iNamed "Hlinv".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (count_l) "Hcount".
  wp_pures.
  wp_loadField.

  iDestruct (own_slice_small_sz with "Hbits") as %Hsz.
  rewrite length_fmap in Hsz.

  wp_apply (wp_forSlice (λ i, ∃ (count: u64),
                            "Hcount" ∷ count_l ↦[uint64T] #count ∗
                            "%Hcount_bound" ∷ ⌜uint.Z count ≤ 8 * uint.Z i⌝)%I
           with "[] [Hcount $Hbits]").
  - clear Φ.
    iIntros (i x Φ) "!> [Hinv [%Hbound %Hlookup]] HΦ". iNamed "Hinv".
    fmap_Some in Hlookup as b.
    wp_pures.
    wp_load.
    wp_apply wp_popCnt.
    iIntros (popcnt Hpop_bound).
    wp_store.
    iModIntro.
    iApply "HΦ".
    iExists _; iFrame.
    iPureIntro.
    word.
  - iExists _; iFrame.
    word.
  - iIntros "[Hinv Hbits]". iNamed "Hinv".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked next bitmap Hbits]").
    { iExists _, _, _; iFrame "∗%". }
    wp_load.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    word.
Qed.
*)

End proof.
