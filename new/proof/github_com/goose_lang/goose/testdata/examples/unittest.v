From New.proof Require Import fmt.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.primitive Require Import disk.
From New.proof.github_com.goose_lang Require Import std.
From New.proof Require Import log.
From New.proof Require Import sync.
From New.proof Require Import disk_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import unittest.
From New.generatedproof Require Import fmt.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ} `{unittest.GlobalAddrs}.

#[global] Program Instance : IsPkgInit unittest := ltac2:(build_pkg_init ()).

Lemma wp_BasicNamedReturn :
  {{{ is_pkg_init unittest }}}
    unittest@"BasicNamedReturn" #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_VoidButEndsWithReturn :
  {{{ is_pkg_init unittest }}}
    unittest@"VoidButEndsWithReturn" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  wp_apply wp_BasicNamedReturn.
  by iApply "HΦ".
Qed.

Lemma wp_VoidImplicitReturnInBranch (b: bool) :
  {{{ is_pkg_init unittest }}}
    unittest@"VoidImplicitReturnInBranch" #b
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  destruct b; wp_auto.
  - by iApply "HΦ".
  - wp_apply wp_BasicNamedReturn.
    by iApply "HΦ".
Qed.

End proof.
