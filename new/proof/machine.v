From New.proof Require Import proof_prelude.
From New.code Require github_com.tchajed.goose.machine.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Lemma wp_Assume {stk E} (cond : bool) :
  {{{ True }}}
    machine.Assume #cond @ stk ; E
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  - iApply ("HΦ" with "[//]").
  - wp_pures.
    iLöb as "IH".
    wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

End wps.
