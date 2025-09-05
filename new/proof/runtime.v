Require Export New.generatedproof.runtime.

Section defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{contextG Σ}.

#[global] Instance : IsPkgInit runtime := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf runtime := build_get_is_pkg_init_wf.

Lemma wp_Gosched :
  {{{
        is_pkg_init runtime ∗
        True
  }}}
    @! runtime.Gosched #()
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start.
  iApply "HΦ".
  done.
Qed.

End defns.
