Require Import New.code.log.
Require Import New.generatedproof.log.
Require Import New.proof.proof_prelude.

Section heap.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit log := ltac2:(build_pkg_init ()).

Theorem wp_Printf (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init log }}}
    log@"Printf" #msg #arg
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_". iApply "HΦ". done.
Qed.

End heap.
