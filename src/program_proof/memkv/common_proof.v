From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section common_proof.

Context `{!heapG Σ}.

Definition shardOfC (key:u64) : u64 := (word.modu key (65536%Z)).

Definition uNSHARD : nat := Z.to_nat 65536.

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
     (s:u64), RET #s; ⌜((int.nat s) < uNSHARD)%nat⌝
  }}}.
Proof.
Admitted.

End common_proof.
