From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

(* TODO: is this still needed? *)
Local Opaque struct_mapsto.

Definition is_hdr_block (sz disk_sz: u64) (b: Block) :=
  ∃ (extra: list u8), Block_to_vals b = b2val <$> encode [EncUInt64 sz; EncUInt64 disk_sz] ++ extra.

Definition is_hdr (sz disk_sz: u64): iProp Σ :=
  ∃ b, 0 d↦ b ∗
       ⌜is_hdr_block sz disk_sz b⌝.

Definition is_log' (sz disk_sz: u64) (vs:list Block): iProp Σ :=
  is_hdr sz disk_sz ∗
  1 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ ∗
  (∃ (free: list Block), (1 + length vs) d↦∗ free ∗
  ⌜ (1 + length vs + length free)%Z = int.val disk_sz ⌝)
.

Definition log_fields (l:loc) (sz disk_sz: u64): iProp Σ :=
  l ↦[Log.S :: "sz"] #sz ∗
  l ↦[Log.S :: "diskSz"] #disk_sz.

Definition ptsto_log (l:loc) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    log_fields l sz disk_sz ∗
    is_log' sz disk_sz vs.

Open Scope Z.

Theorem wp_mkHdr stk E lptr (sz disk_sz: u64) :
  {{{ log_fields lptr sz disk_sz }}}
    Log__mkHdr #lptr @ stk; E
  {{{ l cap b, RET (slice_val (Slice.mk l 4096 cap)); mapsto_block l 1 b ∗ ⌜is_hdr_block sz disk_sz b⌝ ∗
                                                      log_fields lptr sz disk_sz }}}.
Proof.
  iIntros (Φ) "[Hsz Hdisk_sz] HΦ".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %]".
  wp_steps.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); [ word | iIntros "Henc" ].
  wp_steps.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); [ word | iIntros "Henc" ].
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (s) "(Hs&%)".
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  autorewrite with len in H0, Hsz.
  destruct s.
  replace sz0 with (U64 4096).
  { iApply "HΦ".
    iDestruct (slice_to_block with "Hs") as "Hb"; [ done | ].
    iFrame.
    iPureIntro.
    rewrite /is_hdr_block.
    eexists _.
    rewrite list_to_block_to_vals; eauto. }
  simpl in Hsz.
  word.
Qed.

Theorem wpc_write_hdr stk k E1 E2 lptr (sz0 disk_sz0 sz disk_sz:u64) :
  {{{ is_hdr sz0 disk_sz0 ∗
      log_fields lptr sz disk_sz }}}
    Log__writeHdr #lptr @ stk; k; E1; E2
  {{{ RET #(); is_hdr sz disk_sz ∗ log_fields lptr sz disk_sz }}}
  {{{ is_hdr sz0 disk_sz0 ∨ is_hdr sz disk_sz }}}.
Proof.
  iIntros (Φ Φc) "[Hhdr Hlog] HΦ".
  rewrite /Log__writeHdr.
  wpc_pures; eauto.
  wpc_bind (Log__mkHdr _).
  wpc_frame "Hhdr HΦ".
  { crash_case; iFrame. }
  wp_apply (wp_mkHdr with "[$]").
  iIntros (l cap b) "(Hb&%&Hfields) (Hhdr&HΦ)".
  iDestruct "Hhdr" as (b0) "(Hd0&%)".
  wpc_apply (wpc_Write' with "[Hd0 Hb]").
  { iFrame.
    iApply (block_array_to_slice with "Hb"). }
  iSplit.
  - iIntros "Hcrash".
    iDestruct "Hcrash" as "[Hd0 | Hd0]".
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
    iFrame.
    rewrite /is_hdr.
    iExists _; iFrame; eauto.
Qed.

Theorem wp_write_hdr stk E lptr (sz0 disk_sz0 sz disk_sz:u64) :
  {{{ is_hdr sz0 disk_sz0 ∗ log_fields lptr sz disk_sz }}}
    Log__writeHdr #lptr @ stk; E
  {{{ RET #(); is_hdr sz disk_sz ∗ log_fields lptr sz disk_sz }}}.
Proof.
  iIntros (Φ) "[Hhdr Hfields] HΦ".
  wp_call.
  wp_apply (wp_mkHdr with "Hfields").
  iIntros (l cap b) "(Hb&%&Hfields)".
  iDestruct "Hhdr" as (b0) "(Hd0&%)".
  wp_apply (wp_Write with "[Hd0 Hb]").
  { iExists _; iFrame.
    iApply (block_array_to_slice with "Hb"). }
  iIntros "(Hd0&_)".
  iApply "HΦ".
  iFrame.
  rewrite /is_hdr.
  iExists _; iFrame; eauto.
Qed.

Lemma block_to_is_hdr_block b :
  ∃ sz disk_sz, is_hdr_block sz disk_sz b.
Proof.
  exists (le_to_u64 (take 8 $ (vector.vec_to_list b))).
  exists (le_to_u64 (take 8 $ (list.drop 8) $ (vector.vec_to_list b))).
  rewrite /is_hdr_block /Block_to_vals.
  exists (drop 16 $ (vector.vec_to_list b)).
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

Theorem log_struct_to_fields lptr (ml: loc) (sz disk_sz: u64) :
  lptr ↦[struct.t Log.S] (#ml, (#sz, (#disk_sz, #()))) -∗
  log_fields lptr sz disk_sz.
Proof.
  iIntros "Hs".
  iDestruct (struct_fields_split with "Hs") as "(_&Hsz&Hdisk_sz&_)".
  iFrame.
Qed.

Theorem log_struct_to_fields' lptr (ml: loc) (sz disk_sz: u64) :
  lptr ↦[struct.t Log.S] (#ml, (#sz, (#disk_sz, #()))) -∗
  log_fields lptr sz disk_sz ∗ lptr ↦[Log.S :: "m"] #ml.
Proof.
  iIntros "Hs".
  iDestruct (struct_fields_split with "Hs") as "(?&Hsz&Hdisk_sz&?)".
  iFrame.
Qed.

Theorem is_log'_sz sz disk_sz bs :
  is_log' sz disk_sz bs -∗ ⌜length bs = int.nat sz⌝.
Proof.
  iIntros "(_&_&%&_)"; auto.
Qed.

Theorem is_log_read (i: u64) (sz disk_sz: u64) bs :
  int.val i < int.val sz ->
  is_log' sz disk_sz bs -∗
    ∃ b, ⌜bs !! int.nat i = Some b⌝ ∗
         (1 + int.val i) d↦ b ∗
         ((1 + int.val i) d↦ b -∗ is_log' sz disk_sz bs).
Proof.
  iIntros (Hi) "Hlog".
  destruct_with_eqn (bs !! int.nat i).
  - iExists b.
    iSplitR; eauto.
    iDestruct "Hlog" as "(Hhdr & Hlog & % & free)".
    iDestruct (disk_array_acc 1 bs (int.val i) with "Hlog") as "(Hdi&Hupd)"; eauto.
    { word. }
    iFrame.
    iIntros "Hdi"; iDestruct ("Hupd" with "Hdi") as "Hlog".
    rewrite list_insert_id; eauto.
  - apply lookup_ge_None in Heqo.
    iDestruct (is_log'_sz with "Hlog") as "%".
    word.
Qed.

Theorem wp_Log__get stk E (lptr: loc) bs (i: u64) :
  {{{ ptsto_log lptr bs ∗ ⌜int.val i < 2^64-1⌝ }}}
    Log__get #lptr #i @ stk; E
  {{{ s (ok: bool), RET (slice_val s, #ok);
      (if ok
       then ∃ b, ⌜bs !! int.nat i = Some b⌝ ∗ is_slice s byteT 1%Qp (Block_to_vals b)
       else ⌜bs !! int.nat i = None⌝) ∗
      ptsto_log lptr bs }}}.
Proof.
  iIntros (Φ) "[Hlog %] HΦ".
  iDestruct "Hlog" as (sz disk_sz) "[[Hsz Hdisk_sz] Hlog]".
  wp_call.
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  - iDestruct (is_log_read i with "Hlog") as (b) "(%& Hdi&Hupd)"; auto.
    wp_apply (wp_Read with "[Hdi]").
    { word_cleanup.
      iFrame. }
    iIntros (s) "[Hdi Hs]".
    wp_steps.
    iApply "HΦ".
    iSplitR "Hsz Hdisk_sz Hupd Hdi"; eauto.
    iExists sz, disk_sz; iFrame.
    iApply "Hupd".
    word_cleanup.
    iFrame.
  - wp_steps.
    rewrite /slice.nil.
    rewrite slice_val_fold.
    iApply "HΦ".
    iDestruct (is_log'_sz with "Hlog") as %Hsz.
    iSplitR.
    { iPureIntro.
      apply lookup_ge_None.
      lia. }
    iExists _, _; iFrame.
Qed.

(* TODO: prove this based on [wp_Log__get] *)
Theorem wpc_Log__get stk k E1 E2 (lptr: loc) bs (i: u64) :
  {{{ ptsto_log lptr bs ∗ ⌜int.val i < 2^64-1⌝ }}}
    Log__get #lptr #i @ stk; k; E1; E2
  {{{ s (ok: bool), RET (slice_val s, #ok);
      (if ok
       then ∃ b, ⌜bs !! int.nat i = Some b⌝ ∗ is_slice s byteT 1%Qp (Block_to_vals b)
       else ⌜bs !! int.nat i = None⌝) ∗
      ptsto_log lptr bs }}}
  {{{ ptsto_log lptr bs }}}.
Proof.
  iIntros (Φ Φc) "[Hlog %] HΦ".
  iDestruct "Hlog" as (sz disk_sz) "[[Hsz Hdisk_sz] Hlog]".
Abort.

Definition blocks_slice (bk_s: Slice.t) (bks: list Slice.t) (bs: list Block): iProp Σ :=
  is_slice_small bk_s (slice.T byteT) 1%Qp (fmap slice_val bks) ∗
   [∗ list] _ ↦ b_s;b ∈ bks;bs , is_slice_small b_s byteT 1%Qp (Block_to_vals b).

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
  rewrite drop_insert_gt; last lia.
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

Lemma wpc_SliceGet stk k E1 E2 s t q vs (i: u64) v0 :
  {{{ is_slice_small s t q vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet t (slice_val s) #i @ stk; k; E1; E2
  {{{ RET v0; is_slice_small s t q vs ∗ ⌜val_ty v0 t⌝ }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "[Hs %] HΦ".
  rewrite /SliceGet.
  wpc_pures; first auto.
  wpc_frame "HΦ".
  { by crash_case. }
  iApply (wp_SliceGet_body with "[$Hs]").
  { eauto. }
  iIntros "!> [Hs %] HΦ". iNamed "HΦ".
  iRight in "HΦ".
  iApply "HΦ".
  iSplitL; auto.
Qed.

Theorem wpc_forSlice (I: u64 -> iProp Σ) Φc' stk k E1 E2 s t q vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ ∗
                ⌜val_ty x t⌝ }}}
        body #i x @ stk; k; E1; E2
      {{{ RET #(); I (word.add i (U64 1)) }}}
      {{{ Φc' }}}) -∗
    □ (∀ x, I x -∗ Φc') -∗
    {{{ I (U64 0) ∗ is_slice_small s t q vs }}}
      forSlice t body (slice_val s) @ stk; k; E1; E2
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice_small s t q vs }}}
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
          replace (word.add z 1) with (U64 (z + 1)) by word.
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

Theorem wpc_WriteArray stk k E1 E2 l bs q (s: Slice.t) b (off: u64) :
  {{{ l d↦∗ bs ∗ is_block s q b ∗ ⌜0 <= int.val off - l < Z.of_nat (length bs)⌝ }}}
    Write #off (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); l d↦∗ <[Z.to_nat (int.val off - l) := b]> bs ∗ is_block s q b }}}
  {{{ ∃ bs', l d↦∗ bs' ∗ ⌜length bs' = length bs⌝ }}}.
Proof.
  iIntros (Φ Φc) "(Hda&Hs&%&%) HΦ".
  destruct (list_lookup_lt _ bs (Z.to_nat (int.val off - l))) as [b0 Hlookup].
  { word. }
  iDestruct (disk_array_acc _ _ (int.val off - l) with "[$Hda]") as "[Hoff Hda_rest]"; eauto.
  replace (l + (int.val off - l)) with (int.val off) by lia.
  iApply (wpc_Write with "[Hoff Hs] [Hda_rest HΦ]").
  - iExists _; iFrame.
  - iSplit.
    + iIntros "Hcrash"; crash_case.
      iDestruct "Hcrash" as (b') "Hoff".
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
                         (([∗ list] b_s;b ∈ bks;bs, is_slice_small b_s byteT 1%Qp (Block_to_vals b)) ∗
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
        iDestruct "Hcrash" as (bs') "(Hd&%)".
        crash_case.
        iExists _; iFrame.
        iPureIntro.
        lia.
      * iIntros "!> [Hdz Hbsz]".
        iDestruct ("Hbs_rest" with "Hbsz") as "Hbs".
        word_cleanup.
        replace (int.val off + int.val i - int.val off) with (int.val i) by lia.
        erewrite list_copy_new; eauto.
        rewrite drop_insert_gt; last lia.
        rewrite Z2Nat.inj_add; [ | word | word ].
        iApply "HΦ'"; iFrame.
Qed.

Definition crashed_log bs: iProp Σ :=
  ∃ sz disk_sz, is_log' sz disk_sz bs.
Definition uninit_log sz: iProp Σ :=
  ∃ vs, 0 d↦∗ vs ∗ ⌜ length vs = sz ⌝.
Definition unopened_log sz : iProp Σ := uninit_log sz ∨ (∃ bs, crashed_log bs).

Lemma is_log_crash_l sz disk_sz bs (Q: iProp Σ) :
  is_log' sz disk_sz bs -∗ crashed_log bs ∨ Q.
Proof.
  iIntros "Hlog".
  iLeft.
  iExists _, _; iFrame.
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

Theorem wpc_init (sz: u64) k E1 E2 vs:
  {{{ 0 d↦∗ vs ∗ ⌜length vs = int.nat sz⌝ }}}
    Init #sz @ NotStuck; k; E1; E2
  {{{ l (ok: bool), RET (#l, #ok); ⌜ int.nat sz > 0 → ok = true ⌝ ∗
      if ok then ptsto_log l [] ∗ (∃ (ml: loc), l ↦[Log.S :: "m"] #ml ∗ is_free_lock ml)
      else 0 d↦∗ vs }}}
  {{{ 0 d↦∗ vs ∨ (∃ b b' vs', ⌜ vs = b :: vs' ⌝ ∗ 0 d↦∗ (b' :: vs') ) }}}.
Proof.
  iIntros (Φ Φc) "[Hdisk %] HΦ".
  rewrite /Init.
  wpc_pures; first by eauto.
  wpc_if_destruct; wpc_pures; try by eauto.
  - wpc_frame "Hdisk HΦ".
    { iApply "HΦ". eauto. }
    wp_apply wp_new_free_lock; iIntros (ml) "_".
    wp_apply wp_allocStruct; [ val_ty | iIntros (lptr) "Hs" ].
    wp_pures.
    iIntros "(Hdisk&HΦ)".
    iApply "HΦ". iFrame. iPureIntro. word.
  - destruct vs.
    { simpl in *.
      word. }
    wpc_bind (struct.alloc _ _).
    wpc_frame "Hdisk HΦ".
    { iApply "HΦ". eauto. }
    wp_apply wp_new_free_lock; iIntros (ml) "Hlock".
    wp_apply wp_allocStruct; [ val_ty | iIntros (lptr) "Hs" ].
    iDestruct (log_struct_to_fields' with "Hs") as "(Hfields&Hm)".
    wp_pures.
    iIntros "H". iNamed "H".
    wpc_pures; first by eauto.
    iDestruct (disk_array_cons with "Hdisk") as "[Hd0 Hdrest]".
    iDestruct (block_to_is_hdr with "Hd0") as (sz0 disk_sz0) "Hhdr".
    wpc_apply (wpc_write_hdr with "[$Hhdr $Hfields]").
    iSplit.
    { iIntros "Hcase". iApply "HΦ".
      iRight.
      iDestruct "Hcase" as "[H|H]".
      - rewrite /is_hdr. iDestruct "H" as (?) "(?&?)".
        iExists _, _, _. iSplitR; first done. iApply disk_array_cons. by iFrame.
      - rewrite /is_hdr. iDestruct "H" as (?) "(?&?)".
        iExists _, _, _. iSplitR; first done. iApply disk_array_cons. by iFrame.
    }
    iNext. iIntros "(Hhdr&Hlog)".
    wpc_pures.
    { iRight.
      rewrite /is_hdr. iDestruct "Hhdr" as (?) "(?&?)".
      iExists _, _, _. iSplitR; first done. iApply disk_array_cons. by iFrame.
    }
    iApply "HΦ". rewrite /ptsto_log.
    rewrite /ptsto_log /is_log'.
    change (0 + 1) with 1.
    simpl.
    iSplitL "".
    { eauto. }
    iSplitR "Hm Hlock"; last first.
    { iExists _. iFrame. }
    iExists _, _; iFrame.
    rewrite disk_array_emp.
    iSplitR; first by auto.
    iSplitR; first by auto.
    iExists vs; iFrame.
    iPureIntro.
    simpl in H.
    lia.
Qed.


Transparent struct.store.
Definition struct_ty_unfold d :
  ltac:(let x := constr:(struct.t d) in
        let x' := (eval red in x) in
        exact (x = x')) := eq_refl.
Opaque struct.t.

Theorem wpc_Log__append k stk E1 E2 l bs0 bk_s bks bs :
  {{{ ptsto_log l bs0 ∗ blocks_slice bk_s bks bs }}}
    Log__append #l (slice_val bk_s) @ stk; k; E1; E2
  {{{ (ok: bool), RET #ok; (ptsto_log l (if ok then bs0 ++ bs else bs0)) ∗
                          blocks_slice bk_s bks bs }}}
  {{{ crashed_log bs0 ∨ crashed_log (bs0 ++ bs) }}}.
Proof.
  iIntros (Φ Φc) "[Hptsto_log Hbs] HΦ".
  iDestruct "Hptsto_log" as (sz disk_sz) "((Hsz&Hdisk_sz)&Hlog)".
  rewrite /Log__append.

  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }
  wpc_bind (struct.loadF _ _ _).
  wpc_frame "Hlog HΦ".
  { crash_case.
    iApply (is_log_crash_l with "Hlog"). }
  wp_apply (wp_loadField with "Hsz"); iIntros "Hsz".
  iIntros "H"; iNamed "H".

  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }
  wpc_bind (struct.loadF _ _ _).
  wpc_frame "Hlog HΦ".
  { crash_case.
    iApply (is_log_crash_l with "Hlog"). }
  wp_apply (wp_loadField with "Hdisk_sz"); iIntros "Hdisk_sz".
  iIntros "H"; iNamed "H".

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

        (* TODO: finish proof *)
        wpc_bind (struct.storeF _ _ _ _).
        wpc_frame "Hhdr Hlog Hnew Hfree HΦ".
        { crash_case.
          iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }
        wp_loadField.
        wp_pures.
        wp_apply wp_slice_len.
        wp_pures.
        wp_storeField.
        iIntros "H". iNamed "H".

        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len. }

        wpc_apply (wpc_write_hdr with "[$Hhdr $Hsz $Hdisk_sz]").
        iSplit.
        { iIntros "Hhdr".
          iDestruct "Hhdr" as "[Hhdr | Hhdr]"; crash_case.
          - iLeft.
            iExists sz, disk_sz.
            iApply (is_log_split with "[$] [$] Hnew Hfree [%]"); len.
          - iRight.
            iExists _, _.
            iApply (is_log'_append with "[$] [$] [$] [$] [%]"); [len]. }
        iIntros "!> [Hhdr [Hsz Hdisk_sz]]".
        wpc_pures.
        { iRight.
          iExists _, _.
          iApply (is_log'_append with "[$] [$] [$] [$] [%]"); [len]. }

        iApply "HΦ".
        rewrite /ptsto_log.
        iSplitR "Hbs"; [ | iFrame ].
        iExists _, _; iFrame "Hsz Hdisk_sz".
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

Theorem wpc_Log__reset stk k E1 E2 l bs :
  {{{ ptsto_log l bs }}}
    Log__reset #l @ stk; k; E1; E2
  {{{ RET #(); ptsto_log l [] }}}
  {{{ crashed_log bs ∨ crashed_log [] }}}.
Proof.
  iIntros (Φ Φc) "Hlog HΦ".
  iDestruct "Hlog" as (sz disk_sz) "((Hsz&Hdisk_sz)&Hlog)".
  rewrite /Log__reset.
  wpc_pures.
  { iApply (is_log_crash_l with "[$]"). }
  wpc_bind (struct.storeF _ _ _ _).
  wpc_frame "Hlog HΦ".
  { crash_case. iApply (is_log_crash_l with "[$]"). }
  wp_storeField.
  iIntros "H"; iNamed "H".
  wpc_pures.
  { iApply (is_log_crash_l with "[$]"). }
  iDestruct "Hlog" as "(Hhdr&Hlog&%&Hfree)".
  iDestruct "Hfree" as (free) "[Hfree %]".
  wpc_apply (wpc_write_hdr with "[$Hhdr $Hsz $Hdisk_sz]").
  iSplit.
  - iIntros "[Hhdr | Hhdr]"; crash_case.
    + iApply is_log_crash_l.
      rewrite /is_log'.
      iFrame.
      iSplitR; [ auto | ].
      iExists _; by iFrame.
    + iRight.
      iExists _, _.
      by iApply (is_log_reset with "Hhdr Hlog Hfree [%]").
  - iIntros "!> [Hhdr [Hsz Hdisk_sz]]".
    iApply "HΦ".
    rewrite /ptsto_log.
    iExists _, _; iFrame "Hsz Hdisk_sz".
    by iApply (is_log_reset with "Hhdr Hlog Hfree [%]").
Qed.

Theorem wpc_Open k E1 E2 vs :
  {{{ crashed_log vs }}}
    Open #() @ NotStuck; k; E1; E2
  {{{ lptr, RET #lptr; ptsto_log lptr vs ∗ ∃ (ml: loc), lptr ↦[Log.S :: "m"] #ml ∗ is_free_lock ml }}}
  {{{ crashed_log vs }}}.
Proof.
  iIntros (Φ Φc) "Hlog HΦ".
  rewrite /Open.
  wpc_pures; first done.
  iDestruct "Hlog" as (sz disk_sz) "[Hhdr Hlog_rest]".
  iDestruct "Hhdr" as (b) "[Hd0 Hhdr]".
  wpc_apply (wpc_Read with "[Hd0]").
  { iFrame. }
  iSplit.
  { iIntros. iApply "HΦ". iExists _, _. iFrame. iExists _. iFrame. }
  iNext.
  iIntros (s) "[Hd0 Hs]".
  iDestruct "Hhdr" as %Hhdr.
  wpc_frame "Hd0 HΦ Hlog_rest".
  { iApply "HΦ". iExists _, _. iFrame. iExists _. iFrame; eauto. }
  wp_steps.
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  rewrite length_Block_to_vals in Hsz.
  assert (int.val s.(Slice.sz) = 4096) as Hlen.
  { change block_bytes with 4096%nat in Hsz; lia. }
  pose proof Hhdr as Hhdr'.
  destruct Hhdr' as (extra&Hb).
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
  wp_apply wp_new_free_lock; iIntros (ml) "Hlock".
  wp_apply wp_allocStruct; [ rewrite struct_ty_unfold; val_ty | iIntros (lptr) "Hs" ].
  iDestruct (log_struct_to_fields' with "Hs") as "(Hfields&Hm)".
  iIntros "(?&HΦ&?&?&?)".
  iApply "HΦ".
  rewrite /ptsto_log.
  iSplitR "Hm Hlock"; last by (iExists _; iFrame).
  iExists _, _; iFrame.
  rewrite /is_hdr.
  iExists _; iFrame.
  eauto.
Qed.

End heap.

Section crash.
Context `{!heapG Σ}.

Instance is_hdr_durable sz disk_sz:
  IntoCrash (is_hdr sz disk_sz) (λ _, is_hdr sz disk_sz).
Proof. apply _. Qed.

Instance is_log'_durable sz disk_sz vs:
  IntoCrash (is_log' sz disk_sz vs) (λ _, is_log' sz disk_sz vs).
Proof. apply _. Qed.

Instance crashed_log_durable bs:
  IntoCrash (crashed_log bs) (λ _, crashed_log bs).
Proof. apply _. Qed.

Instance uninit_log_durable sz:
  IntoCrash (uninit_log sz) (λ _, uninit_log sz).
Proof. apply _. Qed.

Instance unopened_log_durable sz:
  IntoCrash (unopened_log sz) (λ _, unopened_log sz).
Proof. apply _. Qed.

Instance ptsto_log_into_crash l vs:
  IntoCrash (ptsto_log l vs) (λ _, crashed_log vs).
Proof.
  rewrite /IntoCrash.
  iIntros "HP". iDestruct "HP" as (??) "(H1&H2)".
  (* log_fields gets cleared because it's not durable, is_log' sticks around *)
  iCrash. iExists _, _. eauto.
Qed.

Lemma ptsto_log_into_crash_test l vs:
  ptsto_log l vs -∗ post_crash (λ hG, crashed_log vs).
Proof.
  iIntros "HP".
  (* ptsto_log gets transformed into crashed_log when we go under the modality *)
  iCrash. eauto.
Qed.

End crash.
