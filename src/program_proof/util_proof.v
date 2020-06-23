From Perennial.Helpers Require Import ModArith.

From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import util.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Implicit Types (v:val).
Implicit Types (stk:stuckness) (E: coPset).

Theorem wp_Min_l stk E (n m: u64) Φ :
  int.val n <= int.val m ->
  Φ #n -∗ WP (Min #n #m) @ stk; E {{ Φ }}.
Proof.
  iIntros (Hlt) "HΦ".
  wp_call.
  wp_if_destruct.
  - iFrame.
  - assert (int.val n = int.val m) by word.
    apply word.unsigned_inj in H; subst.
    iFrame.
Qed.

Theorem wp_Min_r stk E (n m: u64) Φ :
  int.val n >= int.val m ->
  Φ #m -∗ WP (Min #n #m) @ stk; E {{ Φ }}.
Proof.
  iIntros (Hlt) "HΦ".
  wp_call.
  wp_if_destruct.
  - assert (int.val n = int.val m) by word.
    apply word.unsigned_inj in H; subst.
    iFrame.
  - iFrame.
Qed.

Theorem wp_DPrintf stk E (level: u64) (msg arg: val) :
  {{{ True }}}
    util.DPrintf #level msg arg @ stk; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iSpecialize ("HΦ" with "[//]").
  wp_call.
  wp_if_destruct; auto.
Qed.

Theorem wp_SumOverflows stk E (x y: u64) :
  {{{ True }}}
    util.SumOverflows #x #y @ stk; E
  {{{ (ok: bool), RET #ok; ⌜ok = bool_decide (int.val x + int.val y >= 2^64)⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iApply "HΦ".
  iPureIntro.
  apply bool_decide_iff, sum_overflow_check.
Qed.

Theorem wp_CloneByteSlice stk E s q vs :
  {{{ is_slice_small s u8T q vs }}}
    CloneByteSlice (slice_val s) @ stk; E
  {{{ (s':Slice.t), RET (slice_val s'); is_slice_small s u8T q vs ∗ is_slice s' u8T 1 vs }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  wp_call.
  wp_apply wp_slice_len.
  iDestruct (is_slice_small_sz with "Hs") as %Hlen.
  wp_apply wp_new_slice; first by auto.
  iIntros (s') "Hs'".
  iDestruct (is_slice_small_acc with "Hs'") as "[Hs'_small Hs']".
  wp_pures.
  wp_apply (wp_SliceCopy_full with "[$Hs $Hs'_small]").
  { iPureIntro.
    autorewrite with len.
    auto. }
  iIntros "(Hs&Hs'_small)".
  iSpecialize ("Hs'" with "Hs'_small").
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

End heap.
