From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} `{!GoContext}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'primitive).
#[global] Program Instance : IsPkgInit primitive :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Lemma wp_Assume (cond : bool) :
  {{{ is_pkg_init primitive }}}
    @! primitive.Assume #cond
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  wp_start as "#Hdef".
  destruct cond; wp_auto.
  - iApply ("HΦ" with "[//]").
  - iLöb as "IH". wp_auto.
    wp_apply ("IH" with "[$]").
Qed.

Lemma wp_RandomUint64 :
  {{{ is_pkg_init primitive }}}
    @! primitive.RandomUint64 #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start as "_".
  wp_apply wp_ArbitraryInt.
  iIntros (x).
  iApply "HΦ".
  done.
Qed.

Lemma wp_AssumeNoStringOverflow (s: byte_string) :
  {{{ is_pkg_init primitive }}}
    @! primitive.AssumeNoStringOverflow #s
  {{{ RET #(); ⌜Z.of_nat (length s) < 2^64⌝ }}}.
Proof.
  wp_start as "_".
  wp_call.
  wp_if_destruct.
  - iApply "HΦ". done.
  - iLöb as "IH".
    wp_pures.
    iApply "IH".
    iApply "HΦ".
Qed.

End wps.
