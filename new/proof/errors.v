Require Export New.generatedproof.errors.

Section defns.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{contextG Σ}.

#[global] Instance : IsPkgInit errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf errors := build_get_is_pkg_init_wf.

End defns.
