From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_inst : IsPkgInit (PROP:=iProp Σ) primitive :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Lemma wp_Assume (cond : bool) :
  {{{ is_pkg_init primitive }}}
    func_call #primitive #"Assume" #cond
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  wp_start as "#Hdef".
  destruct cond; wp_pures.
  - wp_pures. iApply ("HΦ" with "[//]").
  - wp_pures.
    iLöb as "IH".
    wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

End wps.
