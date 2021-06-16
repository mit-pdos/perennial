From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

Section common_proof.

Context `{!heapGS Σ}.

Definition uNSHARD : Z := 65536%Z.

Definition shardOfC (key:u64) : u64 := (word.modu key uNSHARD).

Lemma shardOfC_bound k : int.Z (shardOfC k) < uNSHARD.
Proof.
  rewrite /shardOfC /uNSHARD.
  rewrite word.unsigned_modu_nowrap //.
  apply Z.mod_pos_bound. done.
Qed.

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
  iPureIntro. apply shardOfC_bound.
Qed.

End common_proof.
