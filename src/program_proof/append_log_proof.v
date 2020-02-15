From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang Require Import encoding_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import marshal_proof.

(* TODO: use this throughout (including replacing slice_val) *)
Class GoData T := to_val: forall {ext:ext_op}, T -> val.
Hint Mode GoData !.

Instance u64_data: GoData u64 := λ {_} x, #x.
Instance byte_data: GoData u8 := λ {_} x, #x.
Instance bool_data: GoData bool := λ {_} x, #x.
Instance slice_data: GoData Slice.t := λ {_} s, slice_val s.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Lemma points_to_byte l (x: u8) :
  l ↦[byteT] #x ⊣⊢ l ↦ Free #x.
Proof.
  rewrite /struct_mapsto /=.
  rewrite loc_add_0 right_id.
  iSplit.
  - iDestruct 1 as "[$ _]".
  - iDestruct 1 as "$".
    auto.
Qed.

Lemma array_to_block_array l b :
  array l byteT (Block_to_vals b) ⊣⊢ mapsto_block l 1 b.
Proof.
  rewrite /mapsto_block /array.
  rewrite heap_array_to_list.
  rewrite big_sepL_fmap.
  setoid_rewrite Z.mul_1_l.
  apply big_opL_proper.
  intros k y Heq.
  rewrite /Block_to_vals in Heq.
  rewrite list_lookup_fmap in Heq.
  destruct (fmap_Some_1 _ _ _ Heq) as [x [Hx ->]].
  rewrite /b2val.
  rewrite points_to_byte //.
Qed.

Lemma slice_to_block_array s b :
  is_slice_small s byteT (Block_to_vals b) -∗ mapsto_block s.(Slice.ptr) 1 b.
Proof.
  iIntros "(Ha&_)".
  by iApply array_to_block_array.
Qed.

Lemma block_array_to_slice l b cap :
  mapsto_block l 1 b -∗ is_slice_small (Slice.mk l 4096 cap) byteT (Block_to_vals b).
Proof.
  iIntros "Hm".
  iSplitL.
  { by iApply array_to_block_array. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl.
  reflexivity.
Qed.

Notation length := strings.length.

Transparent disk.Read disk.Write.

Theorem wp_Write stk E (a: u64) s b :
  {{{ ▷ ∃ b0, int.val a d↦ b0 ∗ is_slice_small s byteT (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); int.val a d↦ b ∗ is_slice_small s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) ">Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  wp_call.
  wp_call.
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0.
    iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iApply "HΦ".
  iFrame.
  iSplitL; auto.
  by iApply array_to_block_array.
Qed.

Theorem wp_Write' stk E (z: Z) (a: u64) s b :
  {{{ ⌜int.val a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ is_slice_small s byteT (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); z d↦ b ∗ is_slice_small s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) "[<- >Hpre] HΦ".
  iApply (wp_Write with "[$Hpre]").
  eauto.
Qed.

Lemma wp_Read stk E (a: u64) q b :
  {{{ ▷ int.val a d↦{q} b }}}
    Read #a @ stk; E
  {{{ s, RET slice_val s;
      int.val a d↦{q} b ∗
      is_slice s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) ">Hda HΦ".
  wp_call.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl&_)".
  iDestruct (block_array_to_slice _ _ 4096 with "Hl") as "Hs".
  wp_pures.
  wp_apply (wp_raw_slice with "Hs").
  iIntros (s) "Hs".
  iApply "HΦ".
  iFrame.
Qed.

Definition is_hdr_block (sz disk_sz: u64) (b: Block) :=
∃ extra, Block_to_vals b = b2val <$> encode [EncUInt64 sz; EncUInt64 disk_sz] ++ extra.

Definition is_hdr (sz disk_sz: u64): iProp Σ :=
  ∃ b, 0 d↦ b ∗
       ⌜is_hdr_block sz disk_sz b⌝.

Definition is_log' (sz disk_sz: u64) (vs:list Block): iProp Σ :=
  is_hdr sz disk_sz ∗
  1 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ ∗
  (∃ (free: list Block), (1 + length vs) d↦∗ free ∗
  ⌜ (1 + length vs + length free)%Z = int.val disk_sz ⌝)
.

Definition is_log (v:val) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    ⌜v = (#sz, #disk_sz)%V⌝ ∗
   is_log' sz disk_sz vs.

Open Scope Z.

Theorem wpc_Write stk k E1 E2 (a: u64) s b :
  {{{ ▷ ∃ b0, int.val a d↦ b0 ∗ is_slice_small s byteT (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); int.val a d↦ b ∗ is_slice_small s byteT (Block_to_vals b) }}}
  {{{ ∃ b', int.val a d↦ b' ∗ is_slice_small s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ Φc) ">Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  rewrite /Write /slice.ptr.
  wpc_pures.
  { iExists b0; iFrame. }
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wpc_atomic.
  { iExists b0; iFrame. }
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0; iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iSplit.
  - iModIntro; crash_case.
    iExists b; iFrame.
    destruct s; simpl in Hsz.
    replace sz with (U64 4096).
    + by iApply block_array_to_slice.
    + rewrite length_Block_to_vals in Hsz.
      change block_bytes with (Z.to_nat 4096) in Hsz.
      apply word.unsigned_inj.
      word.
  - iApply "HΦ".
    iFrame.
    iSplitL; auto.
    by iApply array_to_block_array.
Qed.

Theorem wpc_Write' stk k E1 E2 (a: u64) s b0 b :
  {{{ ▷ int.val a d↦ b0 ∗ is_slice_small s byteT (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); int.val a d↦ b ∗ is_slice_small s byteT (Block_to_vals b) }}}
  {{{ (int.val a d↦ b0 ∨ int.val a d↦ b) ∗ is_slice_small s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ Φc) "[>Hda Hs] HΦ".
  rewrite /Write /slice.ptr.
  wpc_pures; iFrame.
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wpc_atomic; iFrame.
  wp_apply (wp_WriteOp with "[Hda Hs]").
  { iIntros "!>".
    iExists b0; iFrame.
    by iApply slice_to_block_array. }
  iIntros "[Hda Hmapsto]".
  iSplit.
  - iModIntro; crash_case; iFrame.
    destruct s; simpl in Hsz.
    replace sz with (U64 4096).
    + by iApply block_array_to_slice.
    + rewrite length_Block_to_vals in Hsz.
      change block_bytes with (Z.to_nat 4096) in Hsz.
      apply word.unsigned_inj.
      word.
  - iApply "HΦ".
    iFrame.
    iSplitL; auto.
    by iApply array_to_block_array.
Qed.

Theorem slice_to_block s bs :
  s.(Slice.sz) = 4096 ->
  is_slice_small s byteT (b2val <$> bs) -∗
  mapsto_block s.(Slice.ptr) 1 (list_to_block bs).
Proof.
  iIntros (Hsz) "Hs".
  iDestruct "Hs" as "[Hl %]".
  rewrite fmap_length in H.
  iApply (array_to_block with "Hl").
  assert (int.val (Slice.sz s) = 4096).
  { rewrite Hsz. reflexivity. }
  lia.
Qed.

Theorem wp_mkHdr stk E (sz disk_sz:u64) :
  {{{ True }}}
    Log__mkHdr (#sz, #disk_sz)%V @ stk; E
  {{{ l cap b, RET (slice_val (Slice.mk l 4096 cap)); mapsto_block l 1 b ∗ ⌜is_hdr_block sz disk_sz b⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_steps.
  wp_call.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { simpl; rewrite H; len. }
  iIntros "Henc".
  wp_steps.
  wp_call.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { simpl; rewrite H; len. }
  iIntros "Henc".
  wp_steps.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (s extra) "(Hs&%)".
  destruct s.
  replace sz0 with (U64 4096).
  { iApply "HΦ".
    iDestruct (is_slice_small_sz with "Hs") as %Hsz.
    autorewrite with len in Hsz.
    rewrite /= in Hsz.
    iDestruct (slice_to_block with "Hs") as "Hb"; [ done | ].
    iFrame.
    iPureIntro.
    rewrite /is_hdr_block.
    exists extra.
    rewrite -> list_to_block_to_vals; auto. }
  apply word.unsigned_inj.
  simpl in H0; subst.
  rewrite H.
  reflexivity.
Qed.

Theorem wpc_write_hdr stk k E1 E2 (sz0 disk_sz0 sz disk_sz:u64) :
  {{{ is_hdr sz0 disk_sz0 }}}
    Log__writeHdr (#sz, #disk_sz)%V @ stk; k; E1; E2
  {{{ RET #(); is_hdr sz disk_sz }}}
  {{{ is_hdr sz0 disk_sz0 ∨ is_hdr sz disk_sz }}}.
Proof.
  iIntros (Φ Φc) "Hhdr HΦ".
  rewrite /Log__writeHdr.
  wpc_pures; eauto.
  wpc_bind (Log__mkHdr _).
  wpc_frame "Hhdr HΦ".
  { iIntros "(Hhdr&HΦ)"; crash_case; iFrame. }
  wp_apply wp_mkHdr.
  iIntros (l cap b) "(Hb&%) (Hhdr&HΦ)".
  iDestruct "Hhdr" as (b0) "(Hd0&%)".
  wpc_apply (wpc_Write' with "[Hd0 Hb]").
  { iFrame.
    iApply (block_array_to_slice with "Hb"). }
  iSplit.
  - iIntros "Hcrash".
    iDestruct "Hcrash" as "[Hd0 _]".
    iDestruct "Hd0" as "[Hd0 | Hd0]".
    + iApply "HΦ".
      iLeft.
      iExists _; by iFrame.
    + iApply "HΦ".
      iRight.
      rewrite /is_hdr.
      iExists _; iFrame.
      eauto.
  - iIntros "!> [Hd0 _]".
    iApply "HΦ".
    rewrite /is_hdr.
    iExists _; iFrame; eauto.
Qed.

Theorem wp_write_hdr stk E (sz0 disk_sz0 sz disk_sz:u64) :
  {{{ is_hdr sz0 disk_sz0 }}}
    Log__writeHdr (#sz, #disk_sz)%V @ stk; E
  {{{ RET #(); is_hdr sz disk_sz }}}.
Proof.
  iIntros (Φ) "Hhdr HΦ".
  wp_call.
  wp_apply wp_mkHdr.
  iIntros (l cap b) "(Hb&%)".
  iDestruct "Hhdr" as (b0) "(Hd0&%)".
  wp_apply (wp_Write with "[Hd0 Hb]").
  { iExists _; iFrame.
    iApply (block_array_to_slice with "Hb"). }
  iIntros "(Hd0&_)".
  iApply "HΦ".
  rewrite /is_hdr.
  iExists _; iFrame; eauto.
Qed.

Lemma block_to_is_hdr_block b :
  ∃ sz disk_sz, is_hdr_block sz disk_sz b.
Proof.
  exists (le_to_u64 (take 8 $ vec_to_list b)).
  exists (le_to_u64 (take 8 $ drop 8 $ vec_to_list b)).
  rewrite /is_hdr_block /Block_to_vals.
  exists (drop 16 $ vec_to_list b).
  f_equal.
  rewrite !encode_cons app_nil_r.
  cbn [encode encode1].
  rewrite !le_to_u64_le; len.
  { rewrite -[b in b = _](take_drop 8 b) -app_assoc.
    f_equal.
    rewrite -[lhs in lhs = _](take_drop 8 (drop 8 b)) drop_drop //.
  }
  { change block_bytes with (Z.to_nat 4096).
    lia. }
  { change block_bytes with (Z.to_nat 4096).
    lia. }
Qed.

Lemma block_to_is_hdr b :
  0 d↦ b -∗ ∃ sz disk_sz, is_hdr sz disk_sz.
Proof.
  iIntros "Hd0".
  rewrite /is_hdr.
  destruct (block_to_is_hdr_block b) as (sz&disk_sz&His_hdr).
  iExists _, _, _; iFrame.
  eauto.
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
  - destruct vs.
    { simpl in *.
      word. }
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

Theorem is_log'_sz sz disk_sz bs :
  is_log' sz disk_sz bs -∗ ⌜length bs = int.nat sz⌝.
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
    { word. }
    iFrame.
    iIntros "Hdi"; iDestruct ("Hupd" with "Hdi") as "Hlog".
    rewrite /is_log.
    iExists _, _; iSplitR; eauto.
    rewrite /is_log'.
    iFrame.
    rewrite list_insert_id; eauto.
  - apply lookup_ge_None in Heqo.
    iDestruct (is_log'_sz with "Hlog") as "%".
    word.
Qed.

Theorem wp_Log__Get stk E v bs (i: u64) :
  {{{ is_log v bs ∗ ⌜int.val i < 2^64-1⌝ }}}
    Log__Get v #i @ stk; E
  {{{ s (ok: bool), RET (slice_val s, #ok);
      (if ok
       then ∃ b, ⌜bs !! int.nat i = Some b⌝ ∗ is_slice s byteT (Block_to_vals b)
       else ⌜bs !! int.nat i = None⌝) ∗
      is_log v bs }}}.
Proof.
  iIntros (Φ) "[Hlog %] HΦ".
  iDestruct (is_log_elim with "Hlog") as (sz disk_sz) "[-> Hlog]".
  wp_call.
  wp_call.
  wp_if_destruct.
  - iDestruct (is_log_read i with "Hlog") as (b) "(%& Hdi&Hupd)"; auto.
    wp_apply (wp_Read with "[Hdi]").
    { word_cleanup.
      iFrame. }
    iIntros (s) "[Hdi Hs]".
    wp_steps.
    iApply "HΦ".
    iSplitR "Hupd Hdi"; eauto.
    iApply "Hupd".
    word_cleanup.
    iFrame.
  - wp_steps.
    rewrite /slice.nil.
    rewrite slice_val_fold.
    iApply "HΦ".
    iDestruct (is_log_sz with "Hlog") as "%".
    iFrame.
    iPureIntro.
    apply lookup_ge_None.
    lia.
Qed.

Definition blocks_slice (bk_s: Slice.t) (bks: list Slice.t) (bs: list Block): iProp Σ :=
  is_slice_small bk_s (slice.T byteT) (fmap slice_val bks) ∗
   [∗ list] _ ↦ b_s;b ∈ bks;bs , is_slice_small b_s byteT (Block_to_vals b).

Lemma blocks_slice_length bk_s bks bs :
  blocks_slice bk_s bks bs -∗ ⌜length bks = length bs⌝.
Proof.
  iIntros "(_&Hslices)".
  iDestruct (big_sepL2_length with "Hslices") as "%".
  auto.
Qed.

Lemma blocks_slice_length' bk_s bks bs :
  blocks_slice bk_s bks bs -∗ ⌜length bks = int.nat bk_s.(Slice.sz)⌝.
Proof.
  iIntros "(Hs&_)".
  iDestruct (is_slice_small_sz with "Hs") as "%".
  iPureIntro.
  rewrite fmap_length in H.
  auto.
Qed.

Lemma insert_0_drop {A} l (x: A) :
  (0 < length l)%nat ->
  <[0%nat:=x]> l = [x] ++ (drop 1 l).
Proof.
  intros.
  destruct l; simpl in *.
  - lia.
  - rewrite drop_0; auto.
Qed.

Lemma list_copy_new {A} (i: nat) x0 x (l1 l2: list A) :
  l2 !! i = Some x0 ->
  l1 !! i = Some x ->
  <[i:=x]> (take i l1 ++ drop i l2) =
  take (i + 1) l1 ++ drop (i + 1) (<[i:=x]> l2).
Proof.
  intros.
  apply lookup_lt_Some in H.
  rewrite insert_app_r_alt; last len.
  assert (i < length l1)%nat.
  { apply lookup_lt_Some in H0; auto. }
  len.
  rewrite Nat.min_l; last lia.
  replace (i - i)%nat with 0%nat by lia.
  rewrite drop_insert; last lia.
  replace (i + 1)%nat with (S i) at 1 by lia.
  erewrite take_S_r; eauto.
  rewrite insert_0_drop; last len.
  destruct l2; [ simpl in *; lia | ].
  rewrite drop_drop.
  rewrite app_assoc.
  simpl.
  destruct i.
  - simpl.
    rewrite drop_0; auto.
  - simpl.
    rewrite <- app_assoc.
    auto.
Qed.

(* TODO: move to basic_triples *)
Lemma wpc_slice_len k stk E1 E2 s Φ Φc :
  Φc ∧ Φ #(Slice.sz s) -∗
  WPC slice.len (slice_val s) @ stk; k; E1; E2 {{ v, Φ v }} {{ Φc }}.
Proof.
  iIntros "HΦ".
  rewrite /slice.len.
  wpc_pures.
  { iDestruct "HΦ" as "[$ _]". }
  { iDestruct "HΦ" as "[_ $]". }
Qed.

Lemma wpc_SliceGet stk k E1 E2 s t vs (i: u64) v0 :
  {{{ is_slice_small s t vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t (slice_val s) #i @ stk; k; E1; E2
  {{{ RET v0; is_slice_small s t vs ∗ ⌜val_ty v0 t⌝ }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "[Hs %] HΦ".
  wpc_frame "HΦ".
  { iIntros "HΦ".
    crash_case.
    auto. }
  wp_apply (wp_SliceGet with "[$Hs]").
  { eauto. }
  iIntros "[Hs %] HΦ".
  iRight in "HΦ".
  iAssert (▷ Φ v0)%I with "[Hs HΦ]" as "HΦ'".
  { iApply "HΦ".
    iSplitL; auto.
  }
  (* TODO: is there a way to strip the later? *)
Admitted.

Theorem wpc_forSlice (I: u64 -> iProp Σ) Φc' stk k E1 E2 s t vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ ∗
                ⌜val_ty x t⌝ }}}
        body #i x @ stk; k; E1; E2
      {{{ RET #(); I (word.add i (U64 1)) }}}
      {{{ Φc' }}}) -∗
    □ (∀ x, I x -∗ Φc') -∗
    {{{ I (U64 0) ∗ is_slice_small s t vs }}}
      forSlice t body (slice_val s) @ stk; k; E1; E2
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t vs }}}
    {{{ Φc' }}}.
Proof.
  iIntros "#Hind #HΦcI".
  iIntros (Φ Φc) "!> [Hi0 Hs] HΦ".
  rewrite /forSlice.
  wpc_pures.
  { iApply ("HΦcI" with "[$]"). }
  wpc_apply wpc_slice_len.
  iSplit; crash_case.
  { iApply ("HΦcI" with "[$]"). }
  wpc_pures.
  { iApply ("HΦcI" with "[$]"). }
  remember 0 as z.
  iRename "Hi0" into "Hiz".
  assert (0 <= z <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_small_sz with "Hs") as %Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange.
  assert (int.val (U64 z) = z) by (rewrite /U64; word).
  (iLöb as "IH" forall (z Hzrange H)).
  wpc_if_destruct.
  - wpc_pures.
    { iApply ("HΦcI" with "[$]"). }
    destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wpc_apply (wpc_SliceGet with "[$Hs] [HΦ Hiz]").
    { replace (int.val z); eauto. }
    { iSplit.
      - iIntros "_"; crash_case.
        iApply ("HΦcI" with "[$]").
      - iIntros "!> [Hs %]".
        wpc_pures.
        { iApply ("HΦcI" with "[$]"). }
        wpc_apply ("Hind" with "[Hiz]").
        + iFrame.
          iPureIntro.
          split; try lia.
          replace (int.nat z) with (Z.to_nat z) by lia; auto.
        + iSplit; crash_case.
          { iLeft in "HΦ"; iFrame. }
          iIntros "!> Hiz1".
          wpc_pures.
          { iApply ("HΦcI" with "[$]"). }
          assert (int.val (z + 1) = int.val z + 1) by word.
          replace (word.add z 1) with (U64 (z + 1)); last first.
          { apply word.unsigned_inj.
            word. }
          iSpecialize ("IH" $! (z+1) with "[] []").
          { iPureIntro; word. }
          { iPureIntro; word. }
          wpc_apply ("IH" with "[$] [$] [$]"). }
  - assert (z = int.val s.(Slice.sz)) by lia; subst z.
    wpc_pures.
    { iApply ("HΦcI" with "[$]"). }
    iRight in "HΦ".
    replace (U64 (int.val s.(Slice.sz))) with s.(Slice.sz); last first.
    { rewrite /U64 word.of_Z_unsigned //. }
    iApply ("HΦ" with "[$]").
Qed.

Theorem wpc_WriteArray stk k E1 E2 l bs (s: Slice.t) b (off: u64) :
  {{{ l d↦∗ bs ∗ is_slice_small s byteT (Block_to_vals b) ∗ ⌜0 <= int.val off - l < Z.of_nat (length bs)⌝ }}}
    Write #off (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); l d↦∗ <[Z.to_nat (int.val off - l) := b]> bs ∗ is_slice_small s byteT (Block_to_vals b) }}}
  {{{ ∃ bs', l d↦∗ bs' ∗ ⌜length bs' = length bs⌝ ∗ is_slice_small s byteT (Block_to_vals b) }}}.
Proof.
  iIntros (Φ Φc) "(Hda&Hs&%&%) HΦ".
  destruct (list_lookup_lt _ bs (Z.to_nat (int.val off - l))) as [b0 Hlookup].
  { word. }
  iDestruct (update_disk_array _ _ (int.val off - l) with "[$Hda]") as "[Hoff Hda_rest]"; eauto.
  replace (l + (int.val off - l)) with (int.val off) by lia.
  iApply (wpc_Write with "[Hoff Hs] [Hda_rest HΦ]").
  - iExists _; iFrame.
  - iSplit.
    + iIntros "Hcrash"; crash_case.
      iDestruct "Hcrash" as (b') "(Hoff&Hs)".
      iSpecialize ("Hda_rest" with "Hoff").
      iExists _; iFrame.
      iPureIntro.
      len.
    + iIntros "!> (Hoff&Hs)".
      iApply "HΦ".
      iSpecialize ("Hda_rest" with "Hoff").
      iFrame.
Qed.

Theorem wpc_writeAll stk (k: nat) E1 E2 bk_s bks bs0 bs (off: u64) :
  {{{ blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs0 ∗
                                 ⌜length bs0 = length bs⌝ ∗
                                 ⌜int.val off + length bs0 < 2^64⌝ }}}
    writeAll (slice_val bk_s) #off @ stk; k; E1; E2
  {{{ RET #(); blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs }}}
  {{{ ∃ bs', int.val off d↦∗ bs' ∗ ⌜length bs' = length bs0⌝ }}}.
Proof.
  iIntros (Φ Φc) "(Hbs&Hd&%&%) HΦ".
  rewrite /writeAll.
  wpc_pures.
  { iExists bs0; iFrame. auto. }
  iDestruct (blocks_slice_length with "Hbs") as %Hbs_len.
  iDestruct (blocks_slice_length' with "Hbs") as %Hbk_s_sz.
  iDestruct "Hbs" as "[Hbk_s Hbks]".

  iApply (wpc_forSlice (fun i =>
                         (([∗ list] b_s;b ∈ bks;bs, is_slice_small b_s byteT (Block_to_vals b)) ∗
                         int.val off d↦∗ (take (int.nat i) bs ++ drop (int.nat i) bs0))%I)
            with "[] [] [$Hbk_s $Hbks $Hd] [HΦ]"); last first.
  - iSplit.
    + iDestruct "HΦ" as "[$ _]".
    + rewrite -> firstn_all2 by lia.
      rewrite -> skipn_all2 by lia.
      rewrite app_nil_r.
      iRight in "HΦ".
      iIntros "!> (Hbk_s&Hbks)".
      iApply "HΦ"; iFrame.
  - iModIntro. iIntros (x) "(Hbk_s&bks)".
    iExists _; iFrame.
    iPureIntro; len.
  - iIntros (i bk_z_val).
    iIntros (Φ' Φc') "!> ((Hbks&Hd)&%&%&%) HΦ'".
    wpc_pures.
    { iExists _; iFrame.
      iPureIntro.
      rewrite app_length take_length drop_length; lia. }
    destruct (list_lookup_Z_lt bs0 (int.val i)) as [b0_z Hlookup_b0]; first word.
    destruct (list_lookup_Z_lt bs (int.val i)) as [b_z Hlookup_b]; first word.
    rewrite list_lookup_fmap in H2.
    apply fmap_Some_1 in H2; destruct H2 as [bk_z (H2&->)].
    iDestruct (big_sepL2_lookup_acc _ _ _ (int.nat i) with "Hbks")
      as "[Hbsz Hbs_rest]"; eauto.
    word_cleanup.

    wpc_apply (wpc_WriteArray with "[$Hd $Hbsz] [Hbs_rest HΦ']").
    + iPureIntro.
      len.
    + iSplit.
      * len.
        iIntros "Hcrash".
        iDestruct "Hcrash" as (bs') "(Hd&%&_)".
        crash_case.
        iExists _; iFrame.
        iPureIntro.
        lia.
      * iIntros "!> [Hdz Hbsz]".
        iDestruct ("Hbs_rest" with "Hbsz") as "Hbs".
        word_cleanup.
        replace (int.val off + int.val i - int.val off) with (int.val i) by lia.
        erewrite list_copy_new; eauto.
        rewrite drop_insert; last lia.
        rewrite Z2Nat.inj_add; [ | word | word ].
        iApply "HΦ'"; iFrame.
Qed.

Definition ptsto_log (l:loc) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    (l ↦ Free #sz ∗
     (l +ₗ 1) ↦ Free #disk_sz) ∗
    is_log' sz disk_sz vs.

Transparent struct.loadField struct.storeStruct.

Lemma is_log_intro sz disk_sz bs :
  is_log' sz disk_sz bs -∗ is_log (#sz, #disk_sz)%V bs.
Proof.
  iIntros "Hlog".
  iExists _, _; iFrame; eauto.
Qed.

Lemma is_log_crash_l sz disk_sz bs (Q: val -> iProp Σ) :
  is_log' sz disk_sz bs -∗ ∃ v, is_log v bs ∨ (Q v).
Proof.
  iIntros "Hlog".
  iExists _.
  iLeft.
  iApply (is_log_intro with "Hlog").
Qed.

Lemma is_log_split sz disk_sz bs free1 free2 z1 z2 :
  is_hdr sz disk_sz -∗
  1 d↦∗ bs -∗ (* log *)
  z1 d↦∗ free1 -∗ (* potentially modified free space *)
  z2 d↦∗ free2 -∗
  ⌜z1 = (1 + int.val sz)%Z⌝ ∗
  ⌜int.val sz = Z.of_nat (length bs)⌝ ∗
  ⌜z2 = (1 + int.val sz + Z.of_nat (length free1))%Z⌝ ∗
  ⌜(z2 + length free2)%Z = int.val disk_sz⌝ -∗
  is_log' sz disk_sz bs.
Proof.
  iIntros "Hhdr Hlog Hfree1 Hfree2 (->&%&->&%)".
  rewrite /is_log'; iFrame.
  iSplitR.
  { iPureIntro; lia. }
  iDestruct (disk_array_app with "[$Hfree1 Hfree2]") as "Hfree".
  { iFrame. }
  rewrite H.
  iExists _; iFrame.
  iPureIntro.
  rewrite app_length; lia.
Qed.

Lemma is_log'_append (sz new_elems disk_sz: u64) bs0 bs free :
  is_hdr (word.add sz new_elems) disk_sz -∗
  1 d↦∗ bs0 -∗
  (1 + int.val sz) d↦∗ bs -∗
  (1 + length bs0 + length bs) d↦∗ free -∗
  (⌜int.val sz = Z.of_nat (length bs0)⌝ ∗
   ⌜int.val new_elems = Z.of_nat (length bs)⌝ ∗
   ⌜(1 + int.val sz + length bs + length free = int.val disk_sz)%Z⌝) -∗
  is_log' (word.add sz new_elems) disk_sz (bs0 ++ bs).
Proof.
  iIntros "Hhdr Hlog Hnew Hfree (%&%&%)".
  iDestruct (disk_array_app with "[$Hlog Hnew]") as "Hlog".
  { replace (1 + length bs0) with (1 + int.val sz) by word.
    iFrame. }
  rewrite /is_log'.
  iFrame.
  iSplitR.
  { iPureIntro. len. }
  iExists _; iFrame.
  replace (1 + length (bs0 ++ bs)) with (1 + length bs0 + length bs) by len.
  iFrame.
  iPureIntro; word.
Qed.

Lemma is_log_append (sz new_elems disk_sz: u64) bs0 bs free :
  is_hdr (word.add sz new_elems) disk_sz -∗
  1 d↦∗ bs0 -∗
  (1 + int.val sz) d↦∗ bs -∗
  (1 + length bs0 + length bs) d↦∗ free -∗
  (⌜int.val sz = Z.of_nat (length bs0)⌝ ∗
   ⌜int.val new_elems = Z.of_nat (length bs)⌝ ∗
   ⌜(1 + int.val sz + length bs + length free = int.val disk_sz)%Z⌝) -∗
  is_log (#(LitInt $ word.add sz new_elems), #disk_sz)%V (bs0 ++ bs).
Proof.
  iIntros "Hhdr Hlog Hnew Hfree (%&%&%)".
  iExists _, _.
  iSplitR; eauto.
  iApply (is_log'_append with "[$] [$] [$] [$] [%]"); auto.
Qed.

Theorem wpc_Log__Append k stk E1 E2 l bs0 bk_s bks bs :
  {{{ ptsto_log l bs0 ∗ blocks_slice bk_s bks bs }}}
    Log__Append #l (slice_val bk_s) @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok; (ptsto_log l (if ok then bs0 ++ bs else bs0)) ∗
                          blocks_slice bk_s bks bs }}}
  {{{ ∃ v, is_log v bs0 ∨ is_log v (bs0 ++ bs) }}}.
Proof.
  iIntros (Φ Φc) "[Hptsto_log Hbs] HΦ".
  iDestruct "Hptsto_log" as (sz disk_sz) "[(Hf0&Hf1) Hlog]".
  rewrite /Log__Append.
  unfold struct.loadField; simpl.
  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }
  rewrite loc_add_0.

  wpc_bind (Load _).
  wpc_atomic.
  { iApply (is_log_crash_l with "Hlog"). }
  wp_load.
  iSplit.
  { iModIntro; crash_case; iApply (is_log_crash_l with "Hlog"). }
  iModIntro.
  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }

  wpc_bind (Load _).
  wpc_atomic.
  { iApply (is_log_crash_l with "Hlog"). }
  wp_load.
  iSplit.
  { iModIntro; crash_case; iApply (is_log_crash_l with "Hlog"). }
  iModIntro.
  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }

  wpc_apply wpc_slice_len.
  iSplit; crash_case.
  { iApply (is_log_crash_l with "Hlog"). }

  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }

  wpc_if_destruct.
  - wpc_pures.
    { iApply (is_log_crash_l with "Hlog"). }
    iApply "HΦ".
    iFrame.
    rewrite /ptsto_log.
    iExists _, _; iFrame.
  - wpc_pures.
    { iApply (is_log_crash_l with "Hlog"). }
    iDestruct "Hlog" as "(Hhdr & Hlog & % & Hfree)".
    iDestruct "Hfree" as (free) "[Hfree %]".
    iDestruct (blocks_slice_length with "Hbs") as %Hlenbks.
    iDestruct (blocks_slice_length' with "Hbs") as %Hlenbk_s.
    rewrite word.unsigned_sub in Heqb.
    rewrite word.unsigned_sub in Heqb.
    rewrite wrap_small in Heqb; last word.
    rewrite wrap_small in Heqb; last word.
    iDestruct (disk_array_split _ _ (length bs) with "Hfree") as "[Halloc Hfree]".
    { word. }
    wpc_apply (wpc_writeAll with "[Halloc $Hbs]").
    + word_cleanup.
      replace (1 + int.val sz) with (1 + length bs0) by word.
      iFrame.
      iPureIntro.
      len.
    + iSplit.
      * len; word_cleanup.
        rewrite Nat.min_l; last lia.
        iIntros "Hcrash".
        iDestruct "Hcrash" as (bs') "(Hfree0&%)".
        crash_case.
        iApply (is_log_crash_l with "[$Hhdr $Hlog Hfree Hfree0]").
        iSplitR.
        { iPureIntro.
          lia. }
        iExists (bs' ++ drop (Z.to_nat (length bs)) free).
        iDestruct (disk_array_app with "[$Hfree0 Hfree]") as "Hfree".
        { replace (1 + int.val sz + length bs') with (1 + length bs0 + length bs) by lia.
          iFrame. }
        replace (1 + length bs0) with (1 + int.val sz) by lia.
        iFrame.
        iPureIntro.
        len.
      * word_cleanup.
        iIntros "!> [Hbs Hnew]".
        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }

        wpc_apply wpc_slice_len.
        iSplit; crash_case.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }

        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }
        word_cleanup.
        wpc_bind (Load _).
        wpc_atomic.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }
        wp_load.
        iSplit; iModIntro; crash_case.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }

        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }

        wpc_apply (wpc_write_hdr with "Hhdr").
        iSplit.
        { iIntros "Hhdr".
          iDestruct "Hhdr" as "[Hhdr | Hhdr]"; crash_case.
          - iExists (#sz, #disk_sz)%V.
            iLeft.
            rewrite /is_log.
            iExists _, _; iSplitR; eauto.
            iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len.
          - iExists _; iRight.
            iApply (is_log_append with "[$] [$] [$] [$] [%]"); [len]. }
        iIntros "!> Hhdr".
        wpc_pures.
        { iExists _; iRight.
          iApply (is_log_append with "[$] [$] [$] [$] [%]"); [len]. }

        wpc_bind (struct.storeStruct _ _ _).
        wpc_frame "Hhdr Hlog Hnew Hfree HΦ".
        { iIntros "(Hhdr&Hlog&Hnew&Hfree&HΦ)".
          crash_case.
          iExists _; iRight.
          iApply (is_log_append with "[$] [$] [$] [$] [%]"); [len]. }
        wp_call.
        wp_store.
        wp_store.
        iIntros "(Hhdr&Hlog&Hnew&Hfree&HΦ)".
        wpc_pures.
        { iExists _; iRight.
          iApply (is_log_append with "[$] [$] [$] [$] [%]"); [len]. }
        iApply "HΦ".
        rewrite /ptsto_log.
        iSplitR "Hbs"; [ | iFrame ].
        iExists _, _; iFrame "Hf0 Hf1".
        iApply (is_log'_append with "[$] [$] [$] [$] [%]"); [len].
Qed.

Lemma is_log_reset disk_sz vs free :
  is_hdr 0 disk_sz -∗
  1 d↦∗ vs -∗
  (1 + length vs) d↦∗ free -∗
  ⌜(1 + length vs + length free)%Z = int.val disk_sz⌝ -∗
  is_log' (U64 0) disk_sz [].
Proof.
  iIntros "Hhdr Hold Hfree %".
  iDestruct (disk_array_app with "[$Hold $Hfree]") as "Hfree".
  rewrite /is_log' /=; iFrame.
  rewrite disk_array_emp.
  iSplitR; auto.
  iSplitR; auto.
  iExists _; iFrame.
  len.
Qed.

Theorem wpc_Log__Reset stk k E1 E2 l vs :
  {{{ ptsto_log l vs }}}
    Log__Reset #l @ stk; k; E1; E2
  {{{ RET #(); ptsto_log l [] }}}
  {{{ ∃ v, is_log v vs ∨ is_log v [] }}}.
Proof.
  iIntros (Φ Φc) "Hlog HΦ".
  iDestruct "Hlog" as (sz disk_sz) "[[Hf0 Hf1] Hlog]".
  rewrite /Log__Reset.
  wpc_pures.
  { iApply (is_log_crash_l with "[$]"). }
  wpc_bind (struct.loadField _ _ _).
  wpc_frame "Hlog HΦ".
  { iIntros "(Hlog&HΦ)".
    crash_case.
    iApply (is_log_crash_l with "[$]"). }
  wp_call.
  wp_load.
  iIntros "(Hlog&HΦ)".
  wpc_pures.
  { iApply (is_log_crash_l with "[$]"). }
  iDestruct "Hlog" as "(Hhdr&Hlog&%&Hfree)".
  iDestruct "Hfree" as (free) "[Hfree %]".
  wpc_apply (wpc_write_hdr with "Hhdr").
  iSplit.
  - iIntros "[Hhdr | Hhdr]"; crash_case.
    + iApply is_log_crash_l.
      rewrite /is_log'.
      iFrame.
      iSplitR; [ auto | ].
      iExists _; by iFrame.
    + iExists _.
      iRight.
      rewrite /is_log.
      iExists _, _; iSplitR; [ eauto | ].
      by iApply (is_log_reset with "Hhdr Hlog Hfree [%]").
  - iIntros "!> Hhdr".
    wpc_pures.
    { iExists _.
      iRight.
      rewrite /is_log.
      iExists _, _; iSplitR; [ eauto | ].
      by iApply (is_log_reset with "Hhdr Hlog Hfree [%]"). }
    rewrite /struct.storeStruct.
    simpl.
    wpc_pures.
    { iExists _.
      iRight.
      rewrite /is_log.
      iExists _, _; iSplitR; [ eauto | ].
      by iApply (is_log_reset with "Hhdr Hlog Hfree [%]"). }
    wpc_frame "Hhdr Hlog Hfree HΦ".
    { iIntros "(Hhdr&Hlog&Hfree&HΦ)"; crash_case.
      iExists _.
      iRight.
      rewrite /is_log.
      iExists _, _; iSplitR; [ eauto | ].
      by iApply (is_log_reset with "Hhdr Hlog Hfree [%]"). }
    wp_store.
    wp_store.
    iIntros "(Hhdr&Hlog&Hfree&HΦ)".
    iApply "HΦ".
    rewrite /ptsto_log.
    iExists _, _; iFrame "Hf0 Hf1".
    by iApply (is_log_reset with "Hhdr Hlog Hfree [%]").
Qed.

Transparent struct.loadStruct.

(* TODO: this should be proven generically on top of a shallow representation of
the struct *)
Theorem wp_loadLog stk E l vs :
  {{{ ptsto_log l vs }}}
    struct.loadStruct Log.S #l @ stk; E
  {{{ v, RET v; is_log v vs }}}.
Proof.
  iIntros (Φ) "Hptsto_log HΦ".
  iDestruct "Hptsto_log" as (sz disk_sz) "[[Hf0 Hf1] Hlog]".
  wp_call.
  wp_load.
  wp_load.
  wp_steps.
  iApply "HΦ".
  iExists _, _; by iFrame.
Qed.

Theorem wp_Open stk E sz disk_sz vs :
  {{{ is_log' sz disk_sz vs }}}
    Open #() @ stk; E
  {{{ v, RET v; is_log v vs }}}.
Proof.
  iIntros (Φ) "Hlog HΦ".
  iDestruct "Hlog" as "[Hhdr Hlog_rest]".
  wp_call.
  iDestruct "Hhdr" as (b) "[Hd0 %]".
  wp_apply (wp_Read with "[Hd0]").
  { change (int.val 0) with 0.
    iFrame. }
  iIntros (s) "[Hd0 Hs]".
  wp_steps.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  rewrite length_Block_to_vals in Hsz.
  assert (int.val s.(Slice.sz) = 4096).
  { change block_bytes with 4096%nat in Hsz; lia. }
  pose proof H.
  destruct H as (extra&Hb).
  rewrite Hb.
  wp_apply (wp_NewDec with "[Hs]").
  { iApply (is_slice_to_small with "[$]"). }
  iIntros (dec) "[Hdec %]".
  wp_pures.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "_".
  wp_steps.
  iApply "HΦ".
  rewrite /is_log.
  iExists _, _; iFrame.
  iSplitR; [ auto | ].
  rewrite /is_hdr.
  iExists _; iFrame.
  eauto.
Qed.

End heap.
