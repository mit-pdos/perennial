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
      iDestruct (slice_to_block_array (Slice.mk l 4096) with "[$Hb]") as "Hs".
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
  - rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_ge in Heqb.
    wp_lam.
    destruct vs.
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

Lemma list_lookup_lt A (l: list A) (i: nat) :
  (i < length l)%nat ->
  exists x, l !! i = Some x.
Proof.
  intros.
  destruct_with_eqn (l !! i); eauto.
  exfalso.
  apply lookup_ge_None in Heqo.
  lia.
Qed.

Lemma list_lookup_Z_lt {A} (l: list A) (i: Z) :
  (0 <= i < Z.of_nat (length l)) ->
  exists x, l !! Z.to_nat i = Some x.
Proof.
  intros.
  apply list_lookup_lt.
  apply Nat2Z.inj_le; lia.
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
      (* TODO: need to assume this! get is actually incorrect if getting from
      the (2^64-1)th index from a disk of size 2^64 *)
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

Theorem wp_writeAll stk E bk_s bks bs0 bs (off: u64) :
  {{{ blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs0 ∗ ⌜length bs0 = length bs⌝ }}}
    writeAll (slice_val bk_s) #off @ stk; E
  {{{ RET #(); blocks_slice bk_s bks bs ∗ int.val off d↦∗ bs }}}.
Proof.
  iIntros (Φ) "(Hbs&Hd&%) HΦ".
  wp_call.
  wp_call.
  wp_call.
  wp_alloc i as "Hi".
  wp_let.
  (* FIXME: 1-1 is a hack to get generalization to work *)
  (* TODO: should probably be stated in terms of (U64 0), not z *)
  assert ((1-1) <= 0) by lia.
  assert (0 <= int.val (Slice.sz bk_s)) by
      (pose proof (word.unsigned_range (Slice.sz bk_s)); lia).
  replace bs0 with (take (Z.to_nat 0) bs ++
                         drop (Z.to_nat 0) bs0);
    last first.
  { change (Z.to_nat 0) with 0%nat.
    simpl.
    destruct bs0; auto. }
  generalize dependent 0.
  change (1-1) with 0.
  intros.
  wp_pures.
  (iLöb as "IH" forall (bs0 H z H0 H1) "Hi").
  wp_call.
  wp_load.
  wp_pures.
  assert (int.val (U64 z) = z) as Hzval.
  { rewrite word.unsigned_of_Z.
    rewrite wrap_small; auto.
    pose proof (word.unsigned_range bk_s.(Slice.sz)).
    lia. }
  wp_if_destruct.
  - rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_lt in Heqb.
    wp_load.
    wp_bind (SliceGet _ _).
    iDestruct (blocks_slice_length with "Hbs") as "%".
    iDestruct "Hbs" as "[Hbk_s Hbs]".
    iDestruct (is_slice_sz with "Hbk_s") as "%".
    rewrite fmap_length in H3.
    pose proof (word.unsigned_range off).
    destruct (list_lookup_Z_lt bks z) as [bk_z Hlookup_bk]; first lia.
    wp_apply (wp_SliceGet with "[$Hbk_s]").
    { iPureIntro.
      rewrite list_lookup_fmap.
      rewrite Hzval; eauto.
      rewrite Hlookup_bk.
      eauto. }
    iIntros "Hbk_s".
    wp_steps.
    wp_load.
    wp_steps.

    destruct (list_lookup_Z_lt bs0 z) as [b0_z Hlookup_b0]; first lia.
    destruct (list_lookup_Z_lt bs z) as [b_z Hlookup_b]; first lia.
    iDestruct (update_disk_array (int.val off) _ z with "Hd")
      as "[Hdz Hd_rest]"; eauto.
    { rewrite lookup_app_r; len.
      rewrite Nat.min_l; last lia.
      rewrite lookup_drop.
      replace (Z.to_nat z - Z.to_nat z)%nat with 0%nat by lia.
      rewrite Nat.add_0_r.
      eauto. }
    iDestruct (big_sepL2_lookup_acc _ _ _ (Z.to_nat z) with "Hbs")
      as "[Hbsz Hbs_rest]"; eauto.
    wp_apply (wp_Write' with "[Hdz $Hbsz]").
    { iSplitR.
      - iPureIntro.
        rewrite word.unsigned_add.
        rewrite wrap_small.
        + replace (int.val z).
          reflexivity.
        + split; try lia.
          admit. (* TODO: need to know all disk addresses being used are < 2^64 *)
      - iExists _; iFrame. }
    iIntros "[Hdz Hbsz]".
    wp_steps.
    wp_load.
    wp_store.
    iDestruct ("Hd_rest" with "Hdz") as "Hd".
    iDestruct ("Hbs_rest" with "Hbsz") as "Hbs".
    (* FIXME: need this binding to make sure Insert typeclass is resolved *)
    let l := constr:(<[Z.to_nat z:=b_z]> bs0) in
    iSpecialize ("IH" $! l with "[]").
    { rewrite insert_length; auto. }
    iSpecialize ("IH" $! (int.val (word.add z 1)) with "[] []").
    { iPureIntro.
      pose proof (word.unsigned_range (word.add z 1)).
      lia. }
    { iPureIntro.
      rewrite word.unsigned_add.
      admit. (* TODO: need to think about this bound *) }
    iSpecialize ("IH" with "[Hbk_s Hbs] [Hd] [$HΦ] [Hi]").
    { iFrame. }
    { rewrite word.unsigned_add.
      rewrite wrap_small; last admit.
      rewrite Z2Nat.inj_add; [ | mia | mia ].
      change (int.nat 1) with 1%nat.
      replace (int.val z).
      erewrite <- list_copy_new; eauto.
    }
    { rewrite /U64.
      rewrite word.of_Z_unsigned.
      iFrame. }
    iApply "IH".
  - rewrite word.unsigned_ltu in Heqb.
    apply Z.ltb_ge in Heqb.
    assert (z = int.val bk_s.(Slice.sz)) by lia.
    subst z.
    iDestruct (blocks_slice_length with "Hbs") as "%".
    iDestruct (blocks_slice_length' with "Hbs") as "%".
    rewrite skipn_all2; last lia.
    rewrite firstn_all2; last lia.
    rewrite app_nil_r.
    iApply "HΦ"; iFrame.

    Fail idtac.
Admitted.

Definition ptsto_log (l:loc) (vs:list Block): iProp Σ :=
  ∃ (sz: u64) (disk_sz: u64),
    (l ↦ Free #sz ∗
     (l +ₗ 1) ↦ Free #disk_sz) ∗
    is_log' sz disk_sz vs.

Transparent struct.loadField struct.storeStruct.

Notation length := strings.length.

Theorem wp_Log__Append stk E l bs0 bk_s bks bs :
  {{{ ptsto_log l bs0 ∗ blocks_slice bk_s bks bs }}}
    Log__Append #l (slice_val bk_s) @ stk; E
  {{{ (ok: bool), RET #ok; ((⌜ok⌝ -∗ ptsto_log l (bs0 ++ bs)) ∗
                            (⌜negb ok⌝ -∗ ptsto_log l bs0)) ∗
                           blocks_slice bk_s bks bs }}}.
Proof.
  iIntros (Φ) "[Hptsto_log Hbs] HΦ".
  iDestruct "Hptsto_log" as (sz disk_sz) "[(Hf0&Hf1) Hlog]".
  wp_call.
  unfold struct.loadField; simpl.
  wp_call.
  rewrite loc_add_0.
  wp_load.
  wp_steps.
  wp_call.
  wp_load.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct; wp_pures; rewrite word.unsigned_ltu in Heqb.
  - apply Z.ltb_lt in Heqb.
    iApply "HΦ".
    iFrame.
    iSplitR; [ iIntros ([]) | iIntros ([]) ].
    rewrite /ptsto_log.
    iExists _, _; iFrame.
  - apply Z.ltb_ge in Heqb.
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
    rewrite wrap_small in Heqb; last admit.
    iDestruct (disk_array_split _ _ (length bs) with "Hfree") as "[Halloc Hfree]".
    { mia. }
    wp_apply (wp_writeAll with "[Halloc $Hbs]").
    { rewrite word.unsigned_add.
      rewrite wrap_small; last admit.
      replace (int.val 1 + int.val sz) with (1 + length bs0) by mia.
      iFrame.
      iPureIntro.
      len. }
    (* TODO: need a general strategy for re-using these in-bounds proofs,
    maybe as soon as we see a u64 expression (rather than waiting to see
    int.val) *)
    rewrite word.unsigned_add.
    rewrite wrap_small; last admit.
    iIntros "[Hbs Hnew]".
    iDestruct (disk_array_app with "[$Hlog Hnew]") as "Hlog".
    { replace (1 + length bs0) with (int.val 1 + int.val sz) by mia.
      iFrame. }
    wp_steps.
    wp_apply wp_slice_len.
    wp_steps.
    wp_call.
    wp_load.
    wp_steps.
    wp_call.
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
Admitted.

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
  wp_call.
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
