Require Import New.code.log.
Require Import New.generatedproof.log.
Require Import New.proof.proof_prelude.

Section heap.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit log := define_is_pkg_init True%I.

Theorem wp_Printf (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init log }}}
    @! log.Printf #msg #arg
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_". iApply "HΦ". done.
Qed.

End heap.
