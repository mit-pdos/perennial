From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Local Notation deps := (ltac2:(build_pkg_init_deps 'primitive) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit primitive :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init primitive = (is_pkg_init primitive) →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined primitive }}}
    primitive.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init primitive }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown $Hinit]").
  2:{ rewrite Hinit //. }
  iIntros "Hown". wp_auto. wp_call.
  rewrite Hinit is_pkg_init_unfold /=.
  by iFrame "∗#".
Qed.

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
