From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_proof Require Export wal.abstraction.
From Perennial.program_proof Require Import proof_prelude disk_lib.

Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) b ∗
                                     ⌜fst b_upd = a⌝.

Lemma updates_slice_len bk_s bs :
  updates_slice bk_s bs -∗ ⌜int.val bk_s.(Slice.sz) = length bs⌝.
Proof.
  iIntros "Hupds".
  iDestruct "Hupds" as (bks) "[Hbs Hbks]".
  iDestruct (is_slice_sz with "Hbs") as %Hbs_sz.
  iDestruct (big_sepL2_length with "Hbks") as %Hbks_len.
  rewrite fmap_length in Hbs_sz.
  iPureIntro.
  rewrite -Hbks_len.
  rewrite Hbs_sz.
  destruct bk_s; simpl.
  word.
Qed.

Theorem wp_SliceGet_updates stk E bk_s bs (i: u64) (u: update.t) :
  {{{ updates_slice bk_s bs ∗ ⌜bs !! int.nat i = Some u⌝ }}}
    SliceGet (struct.t Update.S) (slice_val bk_s) #i @ stk; E
  {{{ uv, RET (update_val uv);
      ⌜uv.1 = u.(update.addr)⌝ ∗
      is_block uv.2 u.(update.b) ∗
      (is_block uv.2 u.(update.b) -∗ updates_slice bk_s bs)
  }}}.
Proof.
  iIntros (Φ) "[Hupds %Hlookup] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_lookup_2_some _ _ _ _ _ Hlookup with "Hbks")
    as %[b_upd Hlookup_bs].
  iDestruct (is_slice_small_acc with "Hbk_s") as "[Hbk_s Hbk_s_rest]".
  wp_apply (wp_SliceGet with "[$Hbk_s]").
  { iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hlookup_bs //. }
  iIntros "[Hbk_s _]".
  iDestruct ("Hbk_s_rest" with "Hbk_s") as "Hbk_s".
  iApply "HΦ".
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hbi Hbks]"; eauto.
  destruct u as [a b]; simpl.
  iDestruct "Hbi" as "[Hbi <-]".
  iSplit; first by auto.
  iFrame.
  iIntros "Hbi".
  iSpecialize ("Hbks" with "[$Hbi //]").
  rewrite /updates_slice.
  iExists _; iFrame.
Qed.

Theorem wp_copyUpdateBlock stk E (u: u64 * Slice.t) b :
  {{{ is_block (snd u) b }}}
    copyUpdateBlock (update_val u) @ stk; E
  {{{ (s':Slice.t), RET (slice_val s'); is_block (snd u) b ∗ is_block s' b }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  destruct u as [a s]; simpl.
  wp_call.
  wp_apply wp_new_slice; first by auto.
  iIntros (s') "Hs'".
  iDestruct (is_slice_to_small with "Hs'") as "Hs'".
  wp_pures.
  wp_apply (wp_SliceCopy_full with "[$Hb $Hs']").
  { iPureIntro.
    autorewrite with len.
    rewrite length_Block_to_vals.
    reflexivity. }
  iIntros "(Hs&Hs')".
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

End heap.

Hint Resolve update_val_t : val_ty.
