Require Import New.code.log.
Require Import New.generatedproof.log.
Require Import New.proof.proof_prelude.

Section heap.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} `{!GoContext}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'log).
#[global] Program Instance : IsPkgInit log :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Theorem wp_Printf (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init log }}}
    @! log.Printf #msg #arg
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_". iApply "HΦ". done.
Qed.

End heap.
