From New.proof Require Import proof_prelude.
From New.code Require Import github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Lemma wp_Assume {stk E} (cond : bool) :
  {{{ is_defined }}}
    machine.Assume #cond @ stk ; E
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  destruct cond; wp_pures.
  - wp_pures. iApply ("HΦ" with "[//]").
  - wp_pures.
    iLöb as "IH".
    wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

End wps.
