(* Begin imports. Could be generated from imports of Go package. *)
Require Import New.proof.proof_prelude.
Require Import New.generatedproof.github_com.mit_pdos.gokv.partialapp.
(* End imports. *)

Section proof.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Context `{!heapGS Σ} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit main := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf main := build_get_is_pkg_init_wf.

Lemma wp_partiallyApplyMe (s : go_string) (x : w64):
  Z.of_nat (length s) = sint.Z x →
  {{{ is_pkg_init main }}}
    @! main.partiallyApplyMe #s #x
  {{{ RET #(); True }}}.
Proof.
  intros ?. wp_start as "_".
  wp_auto.
  rewrite -> bool_decide_true by word.
  wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Foo__someMethod (f : main.Foo.t) :
  {{{ is_pkg_init main }}}
    f @ main.Foo.id @ "someMethod" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".
  wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Foo__someMethodWithArgs (f : main.Foo.t) (y : go_string) (z : w64) :
  Z.of_nat (length (f ++ y)) = sint.Z z →
  {{{ is_pkg_init main }}}
    f @ main.Foo.id @ "someMethodWithArgs" #y #z
  {{{ RET #(); True }}}.
Proof.
  intros ?. wp_start as "_".
  wp_auto.
  wp_apply wp_partiallyApplyMe; first done. by iApply "HΦ".
Qed.

Lemma wp_main :
  {{{ is_pkg_init main }}}
    @! main.main #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".
  wp_apply wp_with_defer as "%defer defer".
  simpl subst. wp_auto.
  wp_apply wp_partiallyApplyMe; first done.
  wp_apply wp_Foo__someMethod.
  wp_apply wp_Foo__someMethodWithArgs; first done.
  wp_apply wp_Foo__someMethodWithArgs; first done.
  wp_apply wp_partiallyApplyMe; first done.
  wp_apply wp_partiallyApplyMe; first done.
  by iApply "HΦ".
Qed.

End proof.
