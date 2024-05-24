From Goose.github_com.tchajed Require Import marshal.

From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Export marshal_proof.
From Perennial.goose_lang.lib Require Export slice.typed_slice.

Definition block_encodes (b:Block) r :=
  has_encoding (vec_to_list b) r.

Typeclasses Opaque block_encodes.

(* it's common to need to match up a record built from the specs to one in an
invariant because the invariant is more cleanly stated, ad this lemma helps to
automate transforming the record from one to the other *)
Lemma block_encodes_eq b r r' :
  block_encodes b r →
  r = r' →
  block_encodes b r'.
Proof. by intros ? ->. Qed.

Notation is_benc enc_v r remaining :=
  (is_enc enc_v 4096 r remaining).

Section goose_lang.
Context `{!heapGS Σ}.

Theorem wp_Enc__Finish stk E enc_v r remaining :
  {{{ is_benc enc_v r remaining }}}
    Enc__Finish enc_v @ stk; E
  {{{ s b, RET slice_val s; ⌜block_encodes b r⌝ ∗ is_block s (DfracOwn 1) b }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_apply (marshal_proof.wp_Enc__Finish with "Hpre").
  iIntros (??) "(%Henc&%Hdatalen&Hs)".
  iApply ("HΦ" $! _ (list_to_block data)).
  iSplitR.
  - rewrite /block_encodes.
    iPureIntro.
    rewrite list_to_block_to_list //.
  - iApply own_slice_to_small in "Hs".
    rewrite /own_slice_small /is_block.
    rewrite -> list_to_block_to_vals by word.
    iFrame.
Qed.

Theorem wp_new_dec stk E s q b r :
  block_encodes b r →
  {{{ is_block s q b }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec_v, RET dec_v; is_dec dec_v r s q b }}}.
Proof.
  iIntros (Henc Φ) "Hpre HΦ".
  wp_apply (marshal_proof.wp_new_dec with "Hpre"); eauto.
Qed.

Lemma is_dec_to_is_block dec_v r s q (b: Block) :
  is_dec dec_v r s q b -∗
  is_block s q b.
Proof.
  iIntros "H". iDestruct (is_dec_to_own_slice_small with "H") as "H".
  iFrame.
Qed.

End goose_lang.

Opaque block_encodes.
