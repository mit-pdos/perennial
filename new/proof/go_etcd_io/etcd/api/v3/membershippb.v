Require Export New.generatedproof.go_etcd_io.etcd.api.v3.membershippb.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : membershippb.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) membershippb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) membershippb := build_get_is_pkg_init_wf.

End wps.
