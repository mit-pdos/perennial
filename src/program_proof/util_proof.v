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

End heap.
