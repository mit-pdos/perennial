Require Export New.generatedproof.runtime.

Section defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : runtime.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) runtime := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) runtime := build_get_is_pkg_init_wf.
Lemma wp_Gosched :
  {{{
        is_pkg_init runtime ∗
        True
  }}}
    @! runtime.Gosched #()
  {{{
        RET #(); True
  }}}.
Proof using W.
  wp_start.
  iApply "HΦ".
  done.
Qed.

End defns.
