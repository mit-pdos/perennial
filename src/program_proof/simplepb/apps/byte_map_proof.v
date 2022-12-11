From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import typed_map map.impl.

Section proof.

Context `{!heapGS Σ}.
Definition own_byte_map (mptr:loc) (m:gmap u64 (list u8)): iProp Σ :=
  ∃ (kvs_sl:gmap u64 Slice.t),
    "Hkvs_map" ∷ is_map mptr 1 kvs_sl ∗
    "#Hkvs_slices" ∷ (∀ (k:u64), readonly (is_slice_small (default Slice.nil (kvs_sl !! k))
                                                          byteT
                                                          1
                                                          (default [] (m !! k))
                                                          )
                     )
.

Lemma wp_byteMapNew :
  {{{
        True
  }}}
    NewMap (slice.T byteT) #()
  {{{
        mptr, RET #mptr; own_byte_map mptr ∅
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".

  iDestruct (is_slice_small_nil byteT 1 Slice.nil) as "HH".
  { done. }
  iMod (readonly_alloc_1 with "HH") as "Hsl".
  wp_apply (wp_NewMap).
  iIntros (?) "Hmap".
  iApply "HΦ".
  iExists _; iFrame.
  iIntros (?).
  rewrite lookup_empty.
  rewrite lookup_empty.
  simpl.
  iFrame "Hsl".
Qed.

Lemma wp_byteMapGet mptr m (k:u64) :
  {{{ own_byte_map mptr m }}}
    Fst (MapGet #mptr #k)
  {{{
        sl, RET (slice_val sl);
        readonly (is_slice_small sl byteT 1 (default [] (m !! k))) ∗
        own_byte_map mptr m
  }}}
.
Proof.
  iIntros (Φ) "Hmap HΦ".
  iNamed "Hmap".
  wp_apply (wp_MapGet with "Hkvs_map").
  iIntros (sl ok) "[%Hlookup Hkvs_map]".
  wp_pures.
  iApply "HΦ".
  iSplitR "Hkvs_map"; last first.
  { iExists _. eauto with iFrame. }
  iModIntro.
  iSpecialize ("Hkvs_slices" $! k).
  rewrite /map_get in Hlookup.
  apply (f_equal fst) in Hlookup.
  simpl in Hlookup.
  rewrite Hlookup.
  iFrame "#".
Qed.

Lemma wp_byteMapPut mptr m (k:u64) sl (v:list u8) q :
{{{
      own_byte_map mptr m ∗ is_slice_small sl byteT q v
}}}
    MapInsert #mptr #k (slice_val sl)
{{{
      RET #(); own_byte_map mptr (<[k := v]> m)
}}}
.
Proof.
  iIntros (Φ) "[Hmap Hsl] HΦ".
  iNamed "Hmap".
  iMod (readonly_alloc (is_slice_small sl byteT 1 v) with "[Hsl]") as "#Hsl".
  { done. }
  wp_apply (wp_MapInsert with "Hkvs_map").
  { done. }
  iIntros "Hkvs_map".
  iApply "HΦ".
  iExists _.
  iFrame "Hkvs_map".
  rewrite /typed_map.map_insert.
  iIntros (?).
  destruct (decide (k0 = k)).
  {
    rewrite e.
    repeat rewrite lookup_insert.
    simpl.
    done.
  }
  {
    rewrite lookup_insert_ne; last done.
    rewrite lookup_insert_ne; last done.
    iApply "Hkvs_slices".
  }
Qed.

Definition has_byte_map_encoding (enc:list u8) (m:gmap u64 (list u8)) : Prop.
Admitted.

End proof.
