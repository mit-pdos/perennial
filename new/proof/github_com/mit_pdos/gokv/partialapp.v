Require Import New.code.github_com.mit_pdos.gokv.partialapp.
Require Import New.generatedproof.github_com.mit_pdos.gokv.partialapp.
Require Import New.proof.proof_prelude.

Section proof.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

#[global]
Program Instance : IsPkgInit main := ltac2:(build_pkg_init ()).

Lemma wp_partiallyApplyMe (s : go_string) (x : w64):
  Z.of_nat (length s) = sint.Z x →
  {{{ is_pkg_init main }}}
    #(func_callv main "partiallyApplyMe") #s #x
  {{{ RET #(); True }}}.
Proof.
  intros ?. wp_start as "_".
  wp_auto.
  rewrite bool_decide_true.
  2:{
    (* FIXME: word. *)
    apply word.signed_inj.
    rewrite H.
    rewrite signed_U64.
    unfold word.swrap.
    word.
  }
  wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Foo__someMethod (f : main.Foo.t) :
  {{{ is_pkg_init main }}}
    #(method_callv main "Foo" "someMethod" #f) #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_".
  wp_auto. by iApply "HΦ".
Qed.

Lemma wp_Foo__someMethodWithArgs (f : main.Foo.t) (y : go_string) (z : w64) :
  Z.of_nat (length (f ++ y)) = sint.Z z →
  {{{ is_pkg_init main }}}
    #(method_callv main "Foo" "someMethodWithArgs" #f) #y #z
  {{{ RET #(); True }}}.
Proof.
  intros ?. wp_start as "_".
  wp_auto.
  wp_apply wp_partiallyApplyMe.
  { done. } by iApply "HΦ".
Qed.

Lemma wp_main :
  {{{ is_pkg_init main }}}
    #(func_callv main "main") #()
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
