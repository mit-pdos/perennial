Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync New.proof.fmt.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) raftpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raftpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) strconv := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strconv := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) slices := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) math := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) math := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) quorum := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) quorum := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) tracker := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) tracker := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) confchange := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) confchange := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) big := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) big := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) rand := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) rand := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) bytes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bytes := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) os := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) os := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) log := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) log := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) io := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) errors := build_get_is_pkg_init_wf.

Definition is_initialized : iProp Σ :=
  ∃ errStopped,
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝.

#[global] Instance : IsPkgInit (iProp Σ) raft := define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raft := build_get_is_pkg_init_wf.

End init.
