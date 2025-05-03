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

  (* Q: why doesn't [wp_auto] work? *)
  (* A: [points_to_access_slice_elem_ref] requires [TCSimpl (vs !! (uint.nat i))
     (Some v)], which cannot be established here. It makes sense when the
     contents of the slice are a literal list, but not here. We should probably
     not support it at all. FIXME:(slice elem_ref)
   *)
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

Lemma wp_MkMaxAlloc (max: u64) :
  0 < uint.Z max →
  uint.Z max `mod` 8 = 0 →
  {{{ is_pkg_init alloc.alloc }}}
    alloc.alloc@"MkMaxAlloc" #max
  {{{ l, RET #l; is_alloc max l }}}.
Proof.
  intros Hbound Hmod.
  wp_start as "_".
  wp_auto.
  wp_if_destruct; last by word.
  wp_auto.
  wp_if_destruct; last by word.
  wp_auto.
  wp_apply (wp_slice_make2 (V:=u8)).
  iIntros (bitmap_s) "[Hs Hscap]". simpl.
  wp_auto.
  wp_apply (wp_MkAlloc with "[$Hs]").
  { rewrite length_replicate. word. }
  { rewrite length_replicate. word. }
  iIntros (a_l) "#Ha".
  rewrite length_replicate.
  wp_auto.
  wp_apply (wp_MarkUsed with "[$Ha]").
  { word. }
  iApply "HΦ".
  iExactEq "Ha".
  f_equal.
  word.
Qed.

Lemma wp_incNext (max: u64) (l: loc) :
  0 < uint.Z max →
  {{{ is_pkg_init alloc.alloc ∗
      alloc_linv max l }}}
    l@alloc.alloc@"Alloc'ptr"@"incNext" #()
  {{{ (next': u64), RET #next'; ⌜uint.Z next' < uint.Z max⌝ ∗
                                alloc_linv max l }}}.
Proof.
  intros Hbound.
  wp_start as "Hl".
  iNamed "Hl".
  wp_auto.
  wp_if_destruct.
  - wp_auto.
    iApply "HΦ".
    iSplit.
    + iPureIntro.
      word.
    + iExists _, _, _.
      iFrame "∗%".
  - wp_auto.
    iApply "HΦ".
    iDestruct (own_slice_len with "Hbits") as %Hsz_len.
    rewrite word.unsigned_mul in n.
    rewrite -> wrap_small in n by word.
    change (uint.Z 8) with 8 in n.
    iSplit.
    + iPureIntro. word.
    + iExists _, _, _.
      iFrame "∗%".
      iPureIntro. word.
Qed.

Lemma wp_allocBit (max: u64) (l: loc) :
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"allocBit" #()
  {{{ (n: u64), RET #n; ⌜uint.Z n < uint.Z max⌝ }}}.
Proof.
  wp_start as "Hpre".
  iNamed "Hpre".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$His_lock]").
  iIntros "[Hlocked Hlinv]".
  wp_auto.
  wp_apply (wp_incNext with "[$Hlinv]"); auto.
  iIntros (?) "[%Hnext_bound Hlinv]".
  wp_auto.
  wp_for.


(*

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
*)
Admitted.

Lemma wp_freeBit max l (bn: u64) :
  uint.Z bn < uint.Z max →
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"freeBit" #bn
  {{{ RET #(); True }}}.
Proof.
  intros Hbound.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$His_lock]").
  iIntros "[Hlocked Hlinv]".
  iNamed "Hlinv".
  iDestruct (own_slice_len with "Hbits") as "%Hbitslen".
  destruct (bits_lookup_byte max bits bn) as [b Hlookup]; [ done | done | ].
  wp_auto.
  wp_pure; first word.
  wp_apply (wp_load_slice_elem with "[$Hbits]"); first by eauto.
  iIntros "Hbits".
  wp_auto.
  wp_pure; first word.
  wp_apply (wp_store_slice_elem with "[$Hbits]"); first by word.
  iIntros "Hbits".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked $next $bitmap $Hbits]").
  { rewrite length_insert. word. }
  by iApply "HΦ".
Qed.

Lemma wp_AllocNum max l :
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"AllocNum" #()
  {{{ (n: u64), RET #n; ⌜uint.Z n < uint.Z max⌝ }}}.
Proof.
  wp_start as "H".
  wp_auto.
  wp_apply (wp_allocBit with "[$H]").
  iIntros (n Hlt).
  wp_auto.
  iApply "HΦ". auto.
Qed.

Lemma wp_FreeNum max l (num: u64) :
  uint.Z num < uint.Z max →
  uint.Z num ≠ 0 →
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"FreeNum" #num
  {{{ RET #(); True }}}.
Proof.
  intros Hnum Hnonzero.
  wp_start as "H".
  wp_auto.
  wp_if_destruct; first word.
  wp_auto.
  wp_apply (wp_freeBit with "[$H]"); eauto.
  by iApply "HΦ".
Qed.

Lemma wp_popCnt (b: u8) :
  {{{ is_pkg_init alloc.alloc }}}
    alloc.alloc@"popCnt" #b
  {{{ (n: u64), RET #n; ⌜uint.Z n ≤ 8⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iAssert (∃ (i count: w64) (x: w8),
                           "Hx" ∷ x_ptr ↦ x ∗
                           "Hi" ∷ i_ptr ↦ i ∗
                           "Hcount" ∷ count_ptr ↦ count ∗
                           "%Hcount_bound" ∷ ⌜uint.Z count ≤ uint.Z i⌝ ∗
                           "%Hi_bound" ∷ ⌜0 ≤ uint.Z i ≤ 8⌝)%I
              with "[$i $x $count]" as "Hloop".
  { simpl. word. }

  wp_for.
  iNamed "Hloop".
  wp_auto.
  wp_if_destruct.
  - wp_auto.
    wp_for_post.
    iFrame.
    pose proof (and_1_u8 x). word.
  - (* XXX why doesn't the automation work for this? *)
    replace (# true) with (into_val_bool.(to_val_def) true) by ( rewrite to_val_unseal; auto ).
    replace (# false) with (into_val_bool.(to_val_def) false) by ( rewrite to_val_unseal; auto ).
    simpl.
    wp_auto.
    iApply "HΦ". word.
Qed.

Lemma wp_NumFree max l :
  {{{ is_pkg_init alloc.alloc ∗
      is_alloc max l }}}
    l@alloc.alloc@"Alloc'ptr"@"NumFree" #()
  {{{ (n:u64), RET #n; ⌜0 ≤ uint.Z n ≤ uint.Z max⌝}}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$His_lock]").
  iIntros "[Hlocked Hlinv]".
  iNamed "Hlinv".
  wp_auto.
  (* FIXME: This spec was written to be really convenient with a list literal,
     but I never did it with general loops. *)
  wp_apply (wp_slice_for_range with "[$Hbits]").
  (* XXX annoying that [bits] appears twice: once as the 3rd argument to [foldr],
   * and once in [bitmap_s ↦* bits] on the left of the wand in the 2nd argument
   * to [foldr].
   *)
  (* I think induction on [bits] isn't the right proof argument. Correctness of
     this code with [b::bits] does not reduce to correctness of code with [bits]. *)
  iInduction bits as [|b bits].
  2:{
    simpl. wp_auto. wp_apply wp_popCnt. iIntros "* %Hn". wp_auto.
    iSplitR; first done.
    (* FIXME: this will not work. The spec is pretty tough to use as-is. *)
    (* iApply "IHbits". *)
    admit.
  }
  simpl. iIntros "Hbits".
  wp_auto.
  iDestruct (own_slice_len with "Hbits") as %Hsz.
    wp_apply (wp_Mutex__Unlock with "[$His_lock $Hlocked $next $bitmap $Hbits]").
  { iNext. simpl in *. word. }
  iApply "HΦ". word.
Admitted.

(*
  Search slice.for_range.
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
