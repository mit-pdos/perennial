From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com.mit_pdos.go_nfsd Require Import simple.
From Perennial.program_proof Require Import obj.obj_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_proof.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec simple.invariant.

Section heap.
Context `{!heapGS Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Theorem wp_inum2Addr (inum : u64) :
  {{{ ⌜ uint.nat inum < NumInodes ⌝ }}}
    inum2Addr #inum
  {{{ RET (addr2val (inum2addr inum)); True }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_rec. wp_pures.
  wp_rec. wp_pures.
  rewrite /addr2val /inum2addr /=.
  rewrite /LogSz /InodeSz.

  rewrite /NumInodes /InodeSz in H.
  replace (4096 `div` 128) with (32) in H by reflexivity.

  replace (word.add (word.divu (word.sub 4096 8) 8) 2)%Z with (W64 513) by reflexivity.
  replace (word.mul (word.mul inum 128) 8)%Z with (W64 (uint.nat inum * 128 * 8)%nat).
  { iApply "HΦ". done. }

  assert (uint.Z (word.mul (word.mul inum 128) 8) = uint.Z inum * 1024)%Z.
  { rewrite word.unsigned_mul.
    rewrite word.unsigned_mul. word. }

  word.
Qed.

Theorem wp_block2addr bn :
  {{{ True }}}
    block2addr #bn
  {{{ RET (addr2val (blk2addr bn)); True }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_rec. wp_pures.
  wp_rec. wp_pures.
  iApply "HΦ". done.
Qed.

Opaque slice_val.

Theorem wp_fh2ino s i :
  {{{ is_fh s i }}}
    fh2ino (slice_val s, #())%V
  {{{ RET #i; True }}}.
Proof.
  iIntros (Φ) "Hfh HΦ".
  iNamed "Hfh".
  iMod (readonly_load with "Hfh_slice") as (q) "Hslice".
  wp_rec. wp_pures.
  wp_rec. wp_pures.
  wp_apply (wp_new_dec with "Hslice"); first by eauto.
  iIntros (dec) "Hdec".
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  iApply "HΦ".
  done.
Qed.

Theorem wp_Fh__MakeFh3 inum :
  {{{ True }}}
    Fh__MakeFh3 (#inum, #())%V
  {{{ s, RET (slice_val s, #()); is_fh s inum }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_pures.
  wp_rec. wp_pures.
  wp_apply wp_new_enc.
  iIntros (enc) "Henc".
  wp_apply (wp_Enc__PutInt with "Henc"); first by word.
  iIntros "Henc".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s data) "(%Henc & %Hlen & Hs)".
  iDestruct (own_slice_to_small with "Hs") as "Hs".
  iMod (readonly_alloc_1 with "Hs") as "Hs".
  wp_pures.
  iApply "HΦ".
  iExists _. iFrame. done.
Qed.

Lemma elem_of_covered_inodes (x:u64) :
  x ∈ covered_inodes ↔ (2 ≤ uint.Z x < 32)%Z.
Proof.
  rewrite /covered_inodes.
  rewrite rangeSet_lookup //.
Qed.

Theorem wp_validInum (i : u64) :
  {{{ True }}}
    validInum #i
  {{{ (valid : bool), RET #valid; ⌜ valid = true <-> i ∈ covered_inodes ⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    move: H; word. }
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    move: H; word. }
  wp_rec. wp_pures.
  change (uint.Z (word.divu _ _)) with 32%Z.
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    word. }
  iApply "HΦ".
  iPureIntro. intuition.
  rewrite elem_of_covered_inodes.
  split; [ | word ].
  assert (i ≠ W64 0) as Hnot_0%(not_inj (f:=uint.Z)) by congruence.
  assert (i ≠ W64 1) as Hnot_1%(not_inj (f:=uint.Z)) by congruence.
  change (uint.Z 0%Z) with 0%Z in *.
  change (uint.Z 1%Z) with 1%Z in *.
  word.
Qed.

Lemma is_inode_crash_next γsrc γnext fh state blk :
  fh [[γsrc]]↦ state ∗
  ( is_inode fh state (durable_pointsto_own γnext)
    ∨ is_inode_enc fh (length state) blk (durable_pointsto_own γnext)
    ∗ is_inode_data (length state) blk state (durable_pointsto_own γnext) )
  -∗ is_inode_stable γsrc γnext fh.
Proof.
  iIntros "[Hfh Hi]".
  iExists _. iFrame.
  iDestruct "Hi" as "[$|[He Hd]]".
  iExists _. iFrame.
Qed.

Lemma is_inode_crash_prev γsrc γprev γnext fh state blk :
  txn_cinv Njrnl γprev γnext -∗
  fh [[γsrc]]↦ state ∗
  ( is_inode fh state (durable_pointsto γprev)
    ∨ is_inode_enc fh (length state) blk (durable_pointsto γprev)
    ∗ is_inode_data (length state) blk state (durable_pointsto γprev) )
  -∗
  |C={⊤}=>
  is_inode_stable γsrc γnext fh.
Proof.
  iIntros "#Hcinv [Hfh H]".

  iDestruct (@liftable _ _ _ _ _ (λ m, is_inode fh state m ∨ is_inode_enc fh (length state) blk m ∗ is_inode_data (length state) blk state m)%I with "H") as (mlift) "[H #Hrestore]".

  iMod (exchange_durable_pointsto with "[$Hcinv $H]") as "H".
  iDestruct ("Hrestore" with "H") as "H".

  iModIntro.
  iApply is_inode_crash_next; iFrame.
Qed.

Lemma is_inode_crash_prev_own γsrc γprev γnext fh state blk :
  txn_cinv Njrnl γprev γnext -∗
  fh [[γsrc]]↦ state ∗
  ( is_inode fh state (durable_pointsto_own γprev)
    ∨ is_inode_enc fh (length state) blk (durable_pointsto_own γprev)
    ∗ is_inode_data (length state) blk state (durable_pointsto_own γprev) )
  -∗
  |C={⊤}=>
  is_inode_stable γsrc γnext fh.
Proof.
  iIntros "#Hcinv [Hfh H]".

  iDestruct (liftable_mono (Φ := λ m, is_inode fh state m
      ∨ is_inode_enc fh (length state) blk m
        ∗ is_inode_data (length state) blk state m)%I
    _ (durable_pointsto γprev) with "H") as "H".
  { iIntros (??) "[_ $]". }

  iApply (is_inode_crash_prev with "Hcinv"). iFrame.
Qed.

Lemma is_inode_stable_crash γsrc γprev γnext fh :
  txn_cinv Njrnl γprev γnext -∗
  is_inode_stable γsrc γprev fh
  -∗
  |C={⊤}=>
  is_inode_stable γsrc γnext fh.
Proof.
  iIntros "#Hcinv".
  rewrite /is_inode_stable.
  iDestruct 1 as (?) "(H1&H2)".
  iApply is_inode_crash_prev_own; iFrame "∗#".
  Unshelve.
  exact (W64 0).
Qed.

End heap.
