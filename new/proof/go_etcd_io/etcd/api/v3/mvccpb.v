Require Export New.generatedproof.go_etcd_io.etcd.api.v3.mvccpb.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : mvccpb.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) mvccpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) mvccpb := build_get_is_pkg_init_wf.

End wps.
