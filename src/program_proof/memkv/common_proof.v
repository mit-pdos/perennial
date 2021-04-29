From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

Section common_proof.

Context `{!heapG Σ}.

Definition shardOfC (key:u64) : u64 := (word.modu key (65536%Z)).

Definition uNSHARD : Z := 65536%Z.

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
Admitted.

Lemma wp_bytesEqual (x y : Slice.t) (xs ys : list byte) qx qy :
  {{{ typed_slice.is_slice x byteT qx xs ∗ typed_slice.is_slice y byteT qy ys }}}
    bytesEqual (slice_val x) (slice_val y)
  {{{ RET #(bool_decide (xs = ys)); typed_slice.is_slice x byteT qx xs ∗ typed_slice.is_slice y byteT qy ys }}}.
Proof.
Admitted.

End common_proof.
