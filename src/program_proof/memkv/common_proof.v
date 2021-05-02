From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

Section common_proof.

Context `{!heapG Σ}.

Definition uNSHARD : Z := 65536%Z.

Definition shardOfC (key:u64) : u64 := (word.modu key uNSHARD).

Lemma wp_shardOf key :
  {{{
       True
  }}}
    shardOf #key
  {{{
       RET #(shardOfC key); True
  }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_shardOf_bound (key:u64) :
  {{{
      True
  }}}
    shardOf #key
  {{{
     (s:u64), RET #s; ⌜int.Z s < uNSHARD⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_shardOf; first done.
  iIntros "!> _". iApply "HΦ".
  rewrite /shardOfC /uNSHARD.
  iPureIntro. rewrite word.unsigned_modu_nowrap //.
  apply Z.mod_pos_bound. done.
Qed.

Lemma wp_bytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ typed_slice.is_slice x byteT qx xs ∗ typed_slice.is_slice y byteT qy ys }}}
    bytesEqual (slice_val x) (slice_val y)
  {{{ RET #(bool_decide (xs = ys)); typed_slice.is_slice x byteT qx xs ∗ typed_slice.is_slice y byteT qy ys }}}.
Proof.
  iIntros (Φ) "[Hx Hy] HΦ". wp_lam. wp_pures.
  do 2 wp_apply wp_slice_len.
  wp_pures.
  iDestruct (typed_slice.is_slice_sz with "Hx") as %Hxlen.
  iDestruct (typed_slice.is_slice_sz with "Hy") as %Hylen.
  destruct_decide (bool_decide_reflect (#x.(Slice.sz) = #y.(Slice.sz))) as Hlen; last first.
  { (* Different lengths. *)
    wp_pures.
    case_bool_decide as Hsl.
    - subst ys. exfalso. apply Hlen. do 2 f_equal.
      rewrite Hxlen in Hylen.
      apply Z2Nat.inj in Hylen; [|word..].
      apply (inj (R:=(=))) in Hylen; last by apply _.
      done.
    - iApply "HΦ". eauto with iFrame. }
  wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (l) "Hi". wp_pures.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (ret) "Hret". wp_pures.
Admitted.

End common_proof.
