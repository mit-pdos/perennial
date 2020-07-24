From Goose.github_com.tchajed Require Import marshal.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import marshal_proof_new.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Definition block_encodes (b:Block) r :=
  has_encoding (vec_to_list b) r.

Typeclasses Opaque block_encodes.

Section goose_lang.
Context `{!heapG Σ}.

Notation is_benc enc_v r remaining :=
  (is_enc enc_v 4096 r remaining).

Theorem wp_Enc__Finish_block stk E enc_v r remaining :
  {{{ is_benc enc_v r remaining }}}
    Enc__Finish enc_v @ stk; E
  {{{ s b, RET slice_val s; is_block s 1 b ∗ ⌜block_encodes b r⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_apply (wp_Enc__Finish with "Hpre").
  iIntros (??) "(%Henc&%Hdatalen&Hs)".
  iApply ("HΦ" $! _ (list_to_block data)).
  iSplitL.
  - iApply is_slice_to_small in "Hs".
    rewrite /is_slice_small /is_block.
    rewrite -> list_to_block_to_vals by word.
    iFrame.
  - rewrite /block_encodes.
    iPureIntro.
    rewrite list_to_block_to_list //.
Qed.

Theorem wp_new_dec_block stk E s q b r :
  block_encodes b r →
  {{{ is_block s q b }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec_v, RET dec_v; is_dec dec_v r }}}.
Proof.
  iIntros (Henc Φ) "Hpre HΦ".
  wp_apply (wp_new_dec with "Hpre"); eauto.
Qed.

End goose_lang.

Opaque block_encodes.
