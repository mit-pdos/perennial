From New.generatedproof.github_com.sanjit_bhat.pav Require Import netffi.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module netffi.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit netffi := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf netffi := build_get_is_pkg_init_wf.

End proof.
End netffi.
