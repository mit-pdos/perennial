From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_inst : IsPkgInit (PROP:=iProp Σ) primitive :=
  ltac2:(build_pkg_init ()).

Lemma wp_Assume (cond : bool) :
  {{{ is_pkg_init primitive }}}
    primitive@"Assume" #cond
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
    primitive@"RandomUint64" #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start as "_".
  wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  replace (LitV x) with (#x) by (rewrite to_val_unseal //).
  iApply "HΦ".
  done.
Qed.

End wps.
