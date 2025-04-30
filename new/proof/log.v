Require Import New.code.log.
Require Import New.generatedproof.log.
Require Import New.proof.proof_prelude.

Section heap.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit log := ltac2:(build_pkg_init ()).

(* XXX is this the right way to say Printf returns some arbitrary value? *)
Theorem wp_Printf (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init log }}}
    log@"Printf" #msg #arg
  {{{ T (_: IntoVal T) (v:T), RET #v; True }}}.
Proof.
  wp_start as "_".
  wp_call.
  iApply "HΦ".
  done.
Qed.

End heap.
