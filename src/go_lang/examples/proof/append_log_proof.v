From iris.proofmode Require Import coq_tactics reduction.
From Perennial.go_lang.examples Require Import append_log.
From Perennial.go_lang Require Import basic_triples.
From Perennial.go_lang Require Import slice encoding.
From Perennial.go_lang Require Import ffi.disk.
From Perennial.go_lang Require Import ffi.disk_prelude.
Import uPred.

Section heap.
Context `{!heapG Σ}.
Existing Instance diskG0.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types stk : stuckness.

Lemma slice_to_block_array s b :
  is_slice s (Block_to_vals b) ⊣⊢ mapsto_block s.(Slice.ptr) 1 b.
Proof.
  rewrite /mapsto_block /is_slice /array.
  (* TODO: how to relate two different big_ops? *)
Admitted.

Transparent disk.Read disk.Write.

Theorem wp_Write stk E (a: u64) s b :
  {{{ ▷ ∃ b0, int.val a d↦ b0 ∗ is_slice s (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); int.val a d↦ b ∗ is_slice s (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) ">Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wp_call.
  wp_call.
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0.
    iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iApply "HΦ".
  iFrame.
  by iApply slice_to_block_array.
Qed.

Definition val_to_byte (v: val): u8 :=
  match v with
  | LitV (LitByte x) => x
  | _ => 0
  end.

Definition list_to_block (l: list val) (H: length l = Z.to_nat 4096) : Block :=
  eq_rect _ _ (vmap val_to_byte (Vector.of_list l)) _ H.

Lemma array_to_block l vs :
  (* TODO: only true if vs are all actually bytes (otherwise roundtripping
  produces #(U8 0) and not the original value) *)
  l ↦∗ vs ∗ ⌜length vs = Z.to_nat 4096⌝ -∗ ∃ H, mapsto_block l 1 (list_to_block vs H).
Proof.
  rewrite /array /mapsto_block /Block_to_vals /list_to_block.
  iIntros "[Hl %]".
  iExists H.
Admitted.

Definition is_hdr (sz disk_sz: u64): iProp Σ :=
  ∃ b, 0 d↦ b ∗
       ⌜take 8 (Block_to_vals b) = u64_le_bytes sz⌝ ∗
       ⌜take 8 (drop 8 (Block_to_vals b)) = u64_le_bytes disk_sz⌝.

Definition is_log (v:val) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    ⌜v = (#sz, #disk_sz)%V⌝ ∗
    is_hdr sz disk_sz ∗
    1 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ ∗
    (∃ (free: list Block), (1 + length vs) d↦∗ free ∗
    ⌜ (1 + length vs + length free)%Z = int.val disk_sz ⌝)
.

Ltac mia :=
  change (int.val 1) with 1;
  change (int.val 4) with 4;
  change (int.val 8) with 8;
  change (int.val 4096) with 4096;
  lia.

Theorem wp_write_hdr stk E (sz0 disk_sz0 sz disk_sz:u64) :
  {{{ is_hdr sz0 disk_sz0 }}}
    Log__writeHdr (#sz, #disk_sz)%V @ stk; E
  {{{ RET #(); is_hdr sz disk_sz }}}.
Proof.
  iIntros (Φ) "Hhdr HΦ".
  iDestruct "Hhdr" as (b) "(Hd0&%&%)".
  wp_call.
  wp_call.
  wp_alloc l as "Hs"; first mia.
  wp_steps.
  wp_call.
  wp_call.
  wp_bind (UInt64Put _ _).
  rewrite slice_val_fold.
  wp_apply (wp_UInt64Put with "[Hs]").
  { iFrame.
    rewrite replicate_length /=.
    iPureIntro; mia. }
  iIntros "Hs".
  wp_steps.
  wp_call.
  wp_bind (SliceSkip _ _).
  wp_apply (wp_SliceSkip with "[$Hs]").
  { iPureIntro.
    rewrite app_length drop_length replicate_length u64_le_bytes_length.
    mia. }
  cbv [Slice.ptr Slice.sz slice_skip].
  iIntros "[Hrest Htake]".
  rewrite take_app_le ?drop_app_ge.
  { wp_bind (UInt64Put _ _).
    wp_apply (wp_UInt64Put with "[Hrest]").
    { iSplitL.
      { rewrite drop_drop drop_replicate.
        rewrite u64_le_bytes_length.
        match goal with
        | |- context[replicate ?n _] => change n with (Z.to_nat 4088)
        end.
        change (word.sub 4096 8) with (U64 4088).
        iExact "Hrest". }
      iPureIntro.
      rewrite replicate_length; mia.
    }
    rewrite drop_replicate.
    change (Z.to_nat 4088 - 8)%nat with (Z.to_nat 4080).
    iIntros "Hrest".
    wp_steps.
    iDestruct "Hrest" as "[Hskip _]".
    cbv [Slice.ptr].
    rewrite firstn_all2; rewrite ?u64_le_bytes_length; last mia.
    iDestruct (array_app with "[$Htake $Hskip]") as "Hl".
    iDestruct (array_to_block with "[$Hl]") as (Hlength) "Hb".
    { iPureIntro.
      rewrite ?app_length ?u64_le_bytes_length replicate_length.
      reflexivity. }
    wp_apply (wp_Write with "[Hd0 Hb]").
    { iExists b.
      iModIntro.
      iSplitL "Hd0"; [ iFrame | ].
      iDestruct (slice_to_block_array (Slice.mk l 4096) with "[$Hb]") as "Hs".
      iExact "Hs". }
    iIntros "[Hd0 Hs]".
    iApply "HΦ".
    rewrite /is_hdr.
    iExists _; iFrame "Hd0".
    iPureIntro.
    admit. }
  { rewrite u64_le_bytes_length; mia. }
  { rewrite u64_le_bytes_length; mia. }
Admitted.

Lemma le_to_u64_le bs :
  length bs = 8%nat ->
  u64_le (le_to_u64 bs) = bs.
Proof.
  intros.
  do 8 (destruct bs; [ simpl in H; lia | ]).
  destruct bs; [ clear H | simpl in H; lia ].
  rewrite /u64_le /le_to_u64.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small.
  { rewrite LittleEndian.split_combine.
    simpl; auto. }
  cbv [length].
  match goal with
  | |- context[LittleEndian.combine ?n ?t] =>
    pose proof (combine_bound n t)
  end.
  lia.
Qed.

Lemma block_to_is_hdr b :
  0 d↦ b -∗ ∃ sz disk_sz, is_hdr sz disk_sz.
Proof.
  iIntros "Hd0".
  rewrite /is_hdr.
  iExists (le_to_u64 (take 8 $ vec_to_list b)).
  iExists (le_to_u64 (take 8 $ drop 8 $ vec_to_list b)).
  iExists _; iFrame.
  iPureIntro; split.
  - rewrite /u64_le_bytes.
    rewrite le_to_u64_le; last first.
    { rewrite take_length.
      rewrite Nat.min_l; auto.
      rewrite vec_to_list_length.
      change block_bytes with 4096%nat; lia. }
    unfold Block_to_vals.
    rewrite fmap_take.
    auto.
  - rewrite /u64_le_bytes.
    rewrite le_to_u64_le; last first.
    { rewrite take_length drop_length.
      rewrite Nat.min_l; auto.
      rewrite vec_to_list_length.
      change block_bytes with 4096%nat; lia. }
    unfold Block_to_vals.
    rewrite fmap_take fmap_drop.
    auto.
Qed.

Theorem wp_init stk E (sz: u64) vs :
  {{{ 0 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ }}}
    Init #sz @ stk; E
  {{{ v (ok: bool), RET (v, #ok); ⌜ok⌝ -∗ is_log v [] }}}.
Proof.
  iIntros (Φ) "[Hdisk %] HΦ".
  wp_lam.
  wp_pures.
  wp_if_destruct; wp_pures.
  - iApply "HΦ".
    iIntros ([]).
  - rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_ge in Heqb.
    wp_lam.
    destruct vs.
    { simpl in *.
      change (int.val 1) with 1 in Heqb.
      lia. }
    iDestruct (disk_array_cons with "Hdisk") as "[Hd0 Hdrest]".
    iDestruct (block_to_is_hdr with "Hd0") as (sz0 disk_sz0) "Hhdr".
    wp_apply (wp_write_hdr with "Hhdr").
    iIntros "Hhdr".
    wp_steps.
    iApply "HΦ".
    iIntros "_".
    rewrite /is_log.
    change (0 + 1) with 1.
    simpl.
    iExists _, _; iFrame.
    rewrite disk_array_emp.
    iSplitR; first by auto.
    iSplitR; first by auto.
    iSplitR; first by auto.
    iExists vs; iFrame.
    iPureIntro.
    simpl in H.
    lia.
Qed.

End heap.
