From iris.proofmode Require Import coq_tactics reduction.
From Perennial.go_lang.examples Require Import append_log.
From Perennial.go_lang Require Import wpc_proofmode.
From Perennial.go_lang Require Import basic_triples.
From Perennial.go_lang Require Import slice encoding.
From Perennial.go_lang Require Import ffi.disk.
From Perennial.go_lang Require Import ffi.disk_prelude.
Import uPred.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Existing Instance diskG0.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types stk : stuckness.

Lemma loc_add_Sn l n :
  l +ₗ S n = (l +ₗ 1) +ₗ n.
Proof.
  rewrite loc_add_assoc.
  f_equal.
  lia.
Qed.

Lemma array_to_block_array l b :
  array l (Block_to_vals b) ⊣⊢ mapsto_block l 1 b.
Proof.
  rewrite /mapsto_block /array.
  generalize dependent (Block_to_vals b).
  intros vs.
  iInduction (vs) as [| v vs] "IH" forall (l).
  - simpl.
    rewrite big_sepM_empty.
    auto.
  - simpl.
    rewrite loc_add_0.
    setoid_rewrite loc_add_Sn.
    rewrite big_sepM_union.
    { rewrite big_sepM_singleton.
      iSplit.
      + iIntros "(Hl&Hvs)"; iFrame.
        iDestruct ("IH" $! (l +ₗ 1) with "Hvs") as "Hvs"; iFrame.
      + iIntros "(Hl&Hvs)"; iFrame.
        iDestruct ("IH" $! (l +ₗ 1) with "Hvs") as "Hvs"; iFrame.
    }
    symmetry.
    apply heap_array_map_disjoint; intros.
    apply (not_elem_of_dom (D := gset loc)).
    rewrite dom_singleton.
    intros ?%elem_of_singleton.
    rewrite loc_add_assoc in H2.
    (* surely this is easy *)
Admitted.

Lemma slice_to_block_array s b :
  is_slice s (Block_to_vals b) -∗ mapsto_block s.(Slice.ptr) 1 b.
Proof.
  iIntros "(Ha&_)".
  by iApply array_to_block_array.
Qed.

Lemma block_array_to_slice l b :
  mapsto_block l 1 b -∗ is_slice (Slice.mk l 4096) (Block_to_vals b).
Proof.
  iIntros "Hm".
  iSplitL.
  { by iApply array_to_block_array. }
  iPureIntro.
  rewrite length_Block_to_vals.
  simpl.
  reflexivity.
Qed.

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
  iDestruct (is_slice_sz with "Hs") as %Hsz.
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
  {{{ ⌜int.val a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ is_slice s (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; E
  {{{ RET #(); z d↦ b ∗ is_slice s (Block_to_vals b) }}}.
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
      is_slice s (Block_to_vals b) }}}.
Proof.
  iIntros (Φ) ">Hda HΦ".
  wp_call.
  wp_apply (wp_ReadOp with "Hda").
  iIntros (l) "(Hda&Hl&_)".
  iDestruct (block_array_to_slice with "Hl") as "Hs".
  wp_pures.
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

Ltac mia :=
  change (int.val 1) with 1 in *;
  change (int.val 4) with 4 in *;
  change (int.val 8) with 8 in *;
  change (int.val 4096) with 4096 in *;
  lia.

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length u64_le_bytes_length : len.
Hint Rewrite @vec_to_list_length : len.

Ltac len := autorewrite with len; try mia.

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
  wp_bind (UInt64Put _ _).
  rewrite slice_val_fold.
  wp_apply (wp_UInt64Put with "[Hs]").
  { iFrame.
    iPureIntro.
    simpl; len. }
  iIntros "Hs".
  wp_steps.
  wp_call.
  wp_bind (SliceSkip _ _).
  wp_apply (wp_SliceSkip with "[$Hs]").
  { iPureIntro; len. }
  cbv [Slice.ptr Slice.sz slice_skip].
  iIntros "[Hrest Htake]".
  rewrite take_app_le ?drop_app_ge; [ | len .. ].
  { wp_bind (UInt64Put _ _).
    wp_apply (wp_UInt64Put with "[Hrest]").
    { iSplitL.
      { rewrite drop_drop drop_replicate.
        len.
        match goal with
        | |- context[replicate ?n _] => change n with (Z.to_nat 4088)
        end.
        change (word.sub 4096 8) with (U64 4088).
        iExact "Hrest". }
      iPureIntro.
      len.
    }
    rewrite drop_replicate.
    change (Z.to_nat 4088 - 8)%nat with (Z.to_nat 4080).
    iIntros "Hrest".
    wp_steps.
    iDestruct "Hrest" as "[Hskip _]".
    cbv [Slice.ptr].
    rewrite firstn_all2; len.
    iDestruct (array_app with "[$Htake $Hskip]") as "Hl".
    iDestruct (array_to_block with "[$Hl]") as (Hlength) "Hb".
    { iPureIntro.
      len. }
    wp_apply (wp_Write with "[Hd0 Hb]").
    { iExists b.
      iModIntro.
      iSplitL "Hd0"; [ iFrame | ].
      iDestruct (block_array_to_slice with "Hb") as "Hs".
      iExact "Hs". }
    iIntros "[Hd0 Hs]".
    iApply "HΦ".
    rewrite /is_hdr.
    iExists _; iFrame "Hd0".
    iPureIntro.
    admit. }
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
    { len. rewrite Nat.min_l; auto.
      change block_bytes with 4096%nat; lia. }
    unfold Block_to_vals.
    rewrite fmap_take.
    auto.
  - rewrite /u64_le_bytes.
    rewrite le_to_u64_le; last first.
    { len.
      rewrite Nat.min_l; auto.
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
  - destruct vs.
    { simpl in *.
      mia. }
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
      (if ok
       then ⌜bs !! int.nat i = Some b⌝ ∗ is_slice s (Block_to_vals b)
       else ⌜bs !! int.nat i = None⌝) ∗
      is_log v bs }}}.
Proof.
  iIntros (Φ) "Hlog HΦ".
  iDestruct (is_log_elim with "Hlog") as (sz disk_sz) "[-> Hlog]".
  wp_call.
  wp_call.
  wp_if_destruct.
  - iDestruct (is_log_read i with "Hlog") as (b) "(%& Hdi&Hupd)"; auto.
    wp_apply (wp_Read with "[Hdi]").
    { rewrite word.unsigned_add.
      (* TODO: need to assume this! get is actually incorrect if getting from
      the (2^64-1)th index from a disk of size 2^64 *)
      rewrite wrap_small; [ | admit ].
      iFrame. }
    iIntros (s) "[Hdi Hs]".
    wp_steps.
    iApply "HΦ".
    iSplitR "Hupd Hdi"; eauto.
    iApply "Hupd".
    rewrite word.unsigned_add.
    rewrite wrap_small; [ | admit ].
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

    Grab Existential Variables.
    { refine inhabitant. }
Admitted.

Lemma is_slice_sz s vs :
  is_slice s vs -∗ ⌜length vs = int.nat s.(Slice.sz)⌝.
Proof.
  iIntros "[_ %]".
  auto.
Qed.

Definition blocks_slice (bk_s: Slice.t) (bks: list Slice.t) (bs: list Block): iProp Σ :=
  is_slice bk_s (fmap slice_val bks) ∗
   [∗ list] _ ↦ b_s;b ∈ bks;bs , is_slice b_s (Block_to_vals b).

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
  iDestruct (is_slice_sz with "Hs") as "%".
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
  Φc ∧ Φ #(Slice.sz s)-∗
  WPC slice.len (slice_val s) @ stk; k; E1; E2 {{ v, Φ v }} {{ Φc }}.
Proof.
  iIntros "HΦc_Φ".
  rewrite /slice.len.
  wpc_pures.
  { iDestruct "HΦc_Φ" as "[$ _]". }
  { iDestruct "HΦc_Φ" as "[_ $]". }
Qed.

Lemma wpc_SliceGet stk k E1 E2 s vs (i: u64) v0 :
  {{{ is_slice s vs ∗ ⌜ vs !! int.nat i = Some v0 ⌝ }}}
    SliceGet (slice_val s) #i @ stk; k; E1; E2
  {{{ RET v0; is_slice s vs }}}
  {{{ is_slice s vs }}}.
Proof.
  iIntros (Φ Φc) "[Hs %] HΦ_Φc".
  rewrite /SliceGet /slice.ptr.
  wpc_pures.
  { iDestruct "HΦ_Φc" as "[HΦc _]".
    iApply ("HΦc" with "Hs"). }
  iApply wpc_atomic_no_mask.
  iSplit.
  { iDestruct "HΦ_Φc" as "[HΦc _]".
    iApply ("HΦc" with "Hs"). }
  destruct s as [ptr sz].
  iDestruct "Hs" as "[Ha %]".
  cbv [Slice.ptr Slice.sz] in *.
  iDestruct (update_array ptr _ _ _ H with "Ha") as "[Hi Ha']".
  word_cleanup.
  wp_load.
  iAssert (is_slice (Slice.mk ptr sz) vs)
    with "[Hi Ha']" as "Hs".
  - rewrite /is_slice /=.
    iSplitR ""; eauto.
    iDestruct ("Ha'" with "Hi") as "Ha".
    erewrite list_insert_id by eauto; auto.
  - iSplit; iFrame.
    + iDestruct "HΦ_Φc" as "[HΦc _]".
      iApply ("HΦc" with "[$]").
    + iDestruct "HΦ_Φc" as "[_ HΦc]".
      iApply ("HΦc" with "Hs").
Qed.

(* TODO: this is an utter hack, surely there's a better way? *)
Tactic Notation "iLeft" "in" constr(H) := let pat := constr:("[" +:+ H +:+ " _]") in
                                          iDestruct H as pat.
Tactic Notation "iRight" "in" constr(H) := let pat := constr:("[_ " +:+ H +:+ "]") in
                                          iDestruct H as pat.

Ltac crash_case :=
  try lazymatch goal with
      | [ |- envs_entails (Envs ?ienv ?senv _) ?Φc ] =>
        is_var Φc;
        lazymatch senv with
        | context[Esnoc _ ?H ((_ -∗ Φc) ∧ _)%I] => iApply H
        end
      end.

Ltac wpc_pures := wpc_proofmode.wpc_pures; crash_case.

Theorem wpc_forSlice (I: u64 -> iProp Σ) Φc' stk k E1 E2 s vs (body: val) :
  (∀ (i: u64) (x: val),
      {{{ I i ∗ ⌜int.val i < int.val s.(Slice.sz)⌝ ∗
                ⌜vs !! int.nat i = Some x⌝ }}}
        body #i x @ stk; k; E1; E2
      {{{ RET #(); I (word.add i (U64 1)) }}}
      {{{ Φc' }}}) -∗
    □ (I (U64 0) -∗ Φc') -∗
    {{{ I (U64 0) ∗ is_slice s vs }}}
      forSlice body (slice_val s) @ stk; k; E1; E2
    {{{ RET #(); I s.(Slice.sz) ∗ is_slice s vs }}}
    {{{ Φc' }}}.
Proof.
  iIntros "#Hind #HΦc0".
  iIntros (Φ Φc) "!> [Hi0 Hs] HΦ".
  rewrite /forSlice.
  wpc_pures.
  { iApply ("HΦc0" with "[$]"). }
  wpc_apply wpc_slice_len.
  iSplit; crash_case.
  { iApply ("HΦc0" with "[$]"). }
  wpc_pures.
  { iApply ("HΦc0" with "[$]"). }
  iAssert (I 0 ∧ Φc')%I with "[Hi0]" as "Hi0".
  { iSplit; iFrame.
    iApply ("HΦc0" with "[$]"). }
  iClear "HΦc0".
  remember 0 as z.
  assert (0 <= z <= int.val s.(Slice.sz)) by word.
  iDestruct (is_slice_sz with "Hs") as %Hslen.
  clear Heqz; generalize dependent z.
  intros z Hzrange.
  pose proof (word.unsigned_range s.(Slice.sz)).
  assert (int.val (U64 z) = z) by (rewrite /U64; word).
  iRename "Hi0" into "Hiz".
  (iLöb as "IH" forall (z Hzrange H0) "Hiz").
  wpc_if_destruct.
  - wpc_pures.
    { iDestruct "Hiz" as "[_ $]". }
    destruct (list_lookup_Z_lt vs z) as [xz Hlookup]; first word.
    wpc_apply (wpc_SliceGet with "[$Hs] [HΦ Hiz]").
    { replace (int.val z); eauto. }
    { iSplit.
      - iIntros "_"; crash_case.
        iRight in "Hiz"; iFrame.
      - iIntros "!> Hs".
        wpc_pures.
        { iRight in "Hiz"; iFrame. }
        (* FIXME: should not frame the entire ∧ *)
        wpc_apply ("Hind" with "[Hiz]").
        + iLeft in "Hiz"; iFrame.
          iPureIntro.
          split; try lia.
          replace (int.nat z) with (Z.to_nat z) by lia; auto.
        + iSplit; crash_case.
          { iLeft in "HΦ"; iFrame. }
          iIntros "!> Hiz1".
          wpc_pures.
          { (* TODO: framed Hiz in wpc_apply, but only wanted to supply the left half *)
            admit. }
          assert (int.val (z + 1) = int.val z + 1) by word.
          replace (word.add z 1) with (U64 (z + 1)); last first.
          { apply word.unsigned_inj.
            word. }
          iSpecialize ("IH" $! (z+1) with "[] []").
          { iPureIntro; word. }
          { iPureIntro; word. }
          wpc_apply ("IH" with "Hs HΦ [Hiz1]").
          iSplit; auto.
          admit. (* again, lost Φc *) }
  - assert (z = int.val s.(Slice.sz)) by lia; subst z.
    wpc_pures.
    { iRight in "Hiz"; iFrame. }
    iRight in "HΦ".
    iLeft in "Hiz".
    replace (U64 (int.val s.(Slice.sz))) with s.(Slice.sz); last first.
    { rewrite /U64 word.of_Z_unsigned //. }
    iApply ("HΦ" with "[$]").
Admitted.

Theorem wpc_Write stk k E1 E2 (a: u64) s b :
  {{{ ▷ ∃ b0, int.val a d↦ b0 ∗ is_slice s (Block_to_vals b) }}}
    Write #a (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); int.val a d↦ b ∗ is_slice s (Block_to_vals b) }}}
  {{{ ∃ b', int.val a d↦ b' ∗ is_slice s (Block_to_vals b) }}}.
Proof.
  iIntros (Φ Φc) ">Hpre HΦ".
  iDestruct "Hpre" as (b0) "[Hda Hs]".
  rewrite /Write /slice.ptr.
  wpc_pures.
  { iExists b0; iFrame. }
  iDestruct (is_slice_sz with "Hs") as %Hsz.
  iApply wpc_atomic_no_mask.
  iSplit; crash_case.
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

(* this theorem is true but no longer used *)
Theorem wpc_frame (s : stuckness) (k : nat) (E1 E2 : coPset)
        (e: expr) (Φ Φ': val -> iProp Σ) (Φc Φc': iProp Σ) (R : iPropI Σ) :
    R -∗
    WPC e @ s; k; E1; E2 {{ v, Φ v }} {{Φc}} -∗
    (R ∗ Φc -∗ Φc') -∗
    (∀ v, R ∗ Φ v -∗ Φ' v) -∗
    WPC e @ s; k; E1; E2 {{ v, Φ' v }} {{Φc'}}.
Proof.
  iIntros "F Hwpc HΦc' HΦ'".
  iDestruct (wpc_frame_l with "[F $Hwpc]") as "Hwpc".
  { iExact "F". }
  iApply (wpc_strong_mono' with "Hwpc"); eauto.
  iSplit.
  - iIntros (v) "HΦ".
    iApply ("HΦ'" with "HΦ").
  - iIntros "HΦc".
    iApply fupd_mask_weaken; [ set_solver+ | ].
    iApply ("HΦc'" with "HΦc").
Qed.

Hint Rewrite @insert_length : len.

Theorem wpc_WriteArray stk k E1 E2 l bs (s: Slice.t) b (off: u64) :
  {{{ l d↦∗ bs ∗ is_slice s (Block_to_vals b) ∗ ⌜0 <= int.val off - l < Z.of_nat (length bs)⌝ }}}
    Write #off (slice_val s) @ stk; k; E1; E2
  {{{ RET #(); l d↦∗ <[Z.to_nat (int.val off - l) := b]> bs ∗ is_slice s (Block_to_vals b) }}}
  {{{ ∃ bs', l d↦∗ bs' ∗ ⌜length bs' = length bs⌝ ∗ is_slice s (Block_to_vals b) }}}.
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
  {{{ blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs0 ∗ ⌜length bs0 = length bs⌝ }}}
    writeAll (slice_val bk_s) #off @ stk; k; E1; E2
  {{{ RET #(); blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs }}}
  {{{ ∃ bs', int.val off d↦∗ bs' ∗ ⌜length bs' = length bs0⌝ }}}.
Proof.
  iIntros (Φ Φc) "(Hbs&Hd&%) HΦ".
  rewrite /writeAll.
  wpc_pures.
  { iExists bs0; iFrame. auto. }
  iDestruct (blocks_slice_length with "Hbs") as %Hbs_len.
  iDestruct (blocks_slice_length' with "Hbs") as %Hbk_s_sz.
  iDestruct "Hbs" as "[Hbk_s Hbks]".
  iApply (wpc_forSlice (fun i =>
                         (([∗ list] b_s;b ∈ bks;bs, is_slice b_s (Block_to_vals b)) ∗
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
  - iIntros "!> (Hbk_s&bks)".
    change (int.nat 0) with 0%nat; simpl.
    rewrite drop_0.
    iExists _; iFrame; auto.
  - iIntros (i bk_z_val).
    pose proof (word.unsigned_range i).
    iIntros (Φ' Φc') "!> ((Hbks&Hd)&%&%) HΦ'".
    wpc_pures.
    { iExists _; iFrame.
      iPureIntro.
      rewrite app_length take_length drop_length; lia. }
    destruct (list_lookup_Z_lt bs0 (int.val i)) as [b0_z Hlookup_b0]; first lia.
    destruct (list_lookup_Z_lt bs (int.val i)) as [b_z Hlookup_b]; first lia.
    rewrite list_lookup_fmap in H2.
    apply fmap_Some_1 in H2; destruct H2 as [bk_z (H2&->)].
    iDestruct (big_sepL2_lookup_acc _ _ _ (int.nat i) with "Hbks")
      as "[Hbsz Hbs_rest]"; eauto.
    word_cleanup.

    wpc_apply (wpc_WriteArray with "[$Hd $Hbsz] [Hbs_rest HΦ']").
    + iPureIntro.
      len; word_cleanup.
      rewrite -> Nat.min_l by lia.
      (* TODO: probably a bound on i is missing from the invariant *)
      admit.
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
        rewrite wrap_small; last admit.
        rewrite wrap_small; last admit.
        replace (int.val off + int.val i - int.val off) with (int.val i) by lia.
        erewrite list_copy_new; eauto.
        rewrite drop_insert; last lia.
        rewrite Z2Nat.inj_add; [ | word | word ].
        iApply "HΦ'"; iFrame.
Admitted.

Definition ptsto_log (l:loc) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    (l ↦ Free #sz ∗
     (l +ₗ 1) ↦ Free #disk_sz) ∗
    is_log' sz disk_sz vs.

Transparent struct.loadField struct.storeStruct.

Notation length := strings.length.

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
  iApply wpc_atomic_no_mask.
  iSplit; crash_case.
  { iApply (is_log_crash_l with "Hlog"). }
  wp_load.
  iSplit.
  { iModIntro; crash_case; iApply (is_log_crash_l with "Hlog"). }
  iModIntro.
  wpc_pures.
  { iApply (is_log_crash_l with "Hlog"). }

  wpc_bind (Load _).
  iApply wpc_atomic_no_mask.
  iSplit; crash_case.
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
    pose proof (word.unsigned_range disk_sz).
    pose proof (word.unsigned_range sz).
    pose proof (word.unsigned_range bk_s.(Slice.sz)).
    rewrite word.unsigned_add in Heqb.
    rewrite word.unsigned_add in Heqb.
    rewrite wrap_small in Heqb; last admit.
    rewrite wrap_small in Heqb; last word.
    iDestruct (disk_array_split _ _ (length bs) with "Hfree") as "[Halloc Hfree]".
    { word. }
    wpc_apply (wpc_writeAll with "[Halloc $Hbs]").
    + word_cleanup.
      replace (1 + int.val sz) with (1 + length bs0) by mia.
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
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }

        wpc_apply wpc_slice_len.
        iSplit; crash_case.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }

        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }
        change (int.val (1 + 0)) with 1.
        wpc_bind (Load _).
        iApply wpc_atomic_no_mask.
        iSplit; crash_case.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }
        wp_load.
        iSplit; iModIntro; crash_case.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }

        wpc_pures.
        { iApply is_log_crash_l.
          iApply (is_log_split with "[$] [$] Hnew Hfree").
          iPureIntro.
          len. }

        (* TODO: need a crash spec for writeHdr (which is annoying because
        it's essentially atomic, except for pure steps on pairs) *)

        (*
      wp_apply (wp_write_hdr with "Hhdr").
      iIntros "Hhdr".
      wp_steps.
      wp_call.
      wp_store.
      wp_steps.
      wp_store.
      iApply "HΦ".
      iFrame.
      iSplitL; iIntros ([]).
      rewrite /ptsto_log.
      iExists _, _; iFrame.
      iFrame.
      iSplitR.
      { iPureIntro.
        len.
        rewrite word.unsigned_add.
        rewrite wrap_small; last admit.
        mia. }
      len.
      iExists _; iFrame.
      replace (1 + (length bs0 + length bs)%nat) with (1 + length bs0 + length bs) by lia.
      iFrame.
      iPureIntro.
      len.
*)
Abort.

Theorem wp_Log__Reset stk E l vs :
  {{{ ptsto_log l vs }}}
    Log__Reset #l @ stk; E
  {{{ RET #(); ptsto_log l [] }}}.
Proof.
  iIntros (Φ) "Hlog HΦ".
  iDestruct "Hlog" as (sz disk_sz) "[[Hf0 Hf1] Hlog]".
  wp_call.
  wp_call.
  wp_load.
  wp_steps.
  iDestruct "Hlog" as "(Hhdr&Hlog&%&Hfree)".
  iDestruct "Hfree" as (free) "[Hfree %]".
  wp_apply (wp_write_hdr with "Hhdr"); iIntros "Hhdr".
  wp_steps.
  wp_call.
  wp_store.
  wp_store.
  iApply "HΦ".
  iExists _, _; iFrame.
  rewrite disk_array_emp.
  iSplitL ""; auto.
  iSplitL ""; auto.
  iDestruct (disk_array_app with "[$Hlog $Hfree]") as "Hfree".
  iExists _; iFrame.
  iPureIntro.
  len.
  simpl; mia.
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
  iDestruct "Hhdr" as (b) "[Hd0 (%&%)]".
  wp_apply (wp_Read with "[Hd0]").
  { change (int.val 0) with 0.
    iFrame. }
  iIntros (s) "[Hd0 Hs]".
  wp_steps.
  wp_apply (wp_UInt64Get with "[$Hs]"); eauto.
  iIntros "Hs".
  wp_steps.
  wp_apply (wp_SliceSkip with "[$Hs]").
  { iPureIntro.
    len. }
  (* we start dropping the parts of the slice since we can deallocate the buffer
  from UInt64Get *)
  iIntros "[Hs Hfirst]"; iClear "Hfirst".
  wp_apply (wp_UInt64Get with "[$Hs]"); eauto; iIntros "Hskip".
  iClear "Hskip".
  wp_steps.
  iApply "HΦ".
  rewrite /is_log.
  iExists _, _; iFrame.
  iSplitR; eauto.
  iExists _; by iFrame.
Qed.

End heap.
