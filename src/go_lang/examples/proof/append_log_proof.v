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

Lemma wp_Read stk E (a: u64) q b :
  {{{ ▷ int.val a d↦{q} b }}}
    Read #a @ stk; E
  {{{ s, RET slice_val s;
      int.val a d↦{q} b ∗
      is_slice s (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) ">Hda HΦ".
  wp_call.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl&_)".
  iDestruct (slice_to_block_array (Slice.mk l 4096) with "Hl") as "Hs".
  wp_pures.
  wp_call.
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iApply "HΦ".
  iFrame.
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

Definition is_log' (v:val) (sz disk_sz: u64) (vs:list Block): iProp Σ :=
  is_hdr sz disk_sz ∗
  1 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ ∗
  (∃ (free: list Block), (1 + length vs) d↦∗ free ∗
  ⌜ (1 + length vs + length free)%Z = int.val disk_sz ⌝)
.

Definition is_log (v:val) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    ⌜v = (#sz, #disk_sz)%V⌝ ∗
    is_log' v sz disk_sz vs.

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
    rewrite /is_log /is_log'.
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

Lemma is_log_elim v bs :
  is_log v bs -∗ ∃ (sz disk_sz: u64),
      ⌜v = (#sz, #disk_sz)%V⌝ ∗
      is_log (#sz, #disk_sz) bs.
Proof.
  iIntros "Hlog".
  iDestruct "Hlog" as (sz disk_sz) "[-> Hlog']".
  rewrite /is_log.
  iExists _, _.
  iSplitR; eauto.
Qed.

Theorem is_log'_sz v sz disk_sz bs :
  is_log' v sz disk_sz bs -∗ ⌜length bs = int.nat sz⌝.
Proof.
  iIntros "(_&_&%&_)"; auto.
Qed.

Theorem is_log_sz (sz disk_sz: u64) bs :
  is_log (#sz, #disk_sz)%V bs -∗ ⌜length bs = int.nat sz⌝.
Proof.
  iIntros "Hlog".
  iDestruct "Hlog" as (sz' disk_sz') "[% Hlog']".
  iDestruct (is_log'_sz with "Hlog'") as "%".
  iPureIntro.
  congruence.
Qed.

Instance word_inhabited width (word: Interface.word width) : Inhabited word.
Proof.
  constructor.
  exact (word.of_Z 0).
Qed.

Theorem is_log_read (i: u64) (sz disk_sz: u64) bs :
  int.val i < int.val sz ->
  is_log (#sz, #disk_sz) bs -∗
    ∃ b, ⌜bs !! int.nat i = Some b⌝ ∗
         (1 + int.val i) d↦ b ∗
         ((1 + int.val i) d↦ b -∗ is_log (#sz, #disk_sz) bs).
Proof.
  iIntros (Hi) "Hlog".
  iDestruct "Hlog" as (sz' disk_sz') "[% Hlog]".
  symmetry in H; inversion H; subst; clear H.
  destruct_with_eqn (bs !! int.nat i).
  - iExists b.
    iSplitR; eauto.
    iDestruct "Hlog" as "(Hhdr & Hlog & % & free)".
    iDestruct (update_disk_array 1 bs (int.val i) with "Hlog") as "(Hdi&Hupd)"; eauto.
    { pose proof (word.unsigned_range i); lia. }
    iFrame.
    iIntros "Hdi"; iDestruct ("Hupd" with "Hdi") as "Hlog".
    rewrite /is_log.
    iExists _, _; iSplitR; eauto.
    rewrite /is_log'.
    iFrame.
    rewrite list_insert_id; eauto.
  - apply lookup_ge_None in Heqo.
    apply Nat2Z.inj_le in Heqo.
    pose proof (word.unsigned_range i).
    rewrite Z2Nat.id in Heqo; try lia.
    iDestruct (is_log'_sz with "Hlog") as "%".
    lia.
Qed.

Theorem wp_Log__Get stk E v bs (i: u64) :
  {{{ is_log v bs }}}
    Log__Get v #i @ stk; E
  {{{ b s (ok: bool), RET (slice_val s, #ok);
      (⌜ok⌝ -∗ ⌜bs !! int.nat i = Some b⌝ ∗ is_slice s (Block_to_vals b)) ∗
      (⌜negb ok⌝ -∗ ⌜bs !! int.nat i = None⌝) ∗
      is_log v bs }}}.
Proof.
  iIntros (Φ) "Hlog HΦ".
  iDestruct (is_log_elim with "Hlog") as (sz disk_sz) "[-> Hlog]".
  wp_call.
  wp_call.
  wp_call.
  wp_if_destruct.
  - rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_lt in Heqb.
    iDestruct (is_log_read i with "Hlog") as (b) "(%& Hdi&Hupd)"; auto.
    wp_apply (wp_Read with "[Hdi]").
    { rewrite word.unsigned_add.
      (* TODO: does something imply this doesn't overflow? *)
      rewrite wrap_small; [ | admit ].
      iFrame. }
    iIntros (s) "[Hdi Hs]".
    wp_steps.
    iApply "HΦ".
    iSplitL "Hs"; eauto.
    iSplitR; eauto.
    iApply "Hupd".
    rewrite word.unsigned_add.
    rewrite wrap_small; [ | admit ].
    iFrame.
  - wp_steps.
    rewrite /slice.nil.
    rewrite slice_val_fold.
    iApply "HΦ".
    iDestruct (is_log_sz with "Hlog") as "%".
    rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_ge in Heqb.
    iFrame.
    iSplit.
    + iIntros ([]).
    + iIntros "_".
      iPureIntro.
      apply lookup_ge_None.
      lia.

      Grab Existential Variables.
      { refine inhabitant. }
Admitted.

End heap.
