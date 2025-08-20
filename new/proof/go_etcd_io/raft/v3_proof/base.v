Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync.


Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit raftpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf raftpb := build_get_is_pkg_init.

#[global] Instance : IsPkgInit strconv := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strconv := build_get_is_pkg_init.

#[global] Instance : IsPkgInit slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf slices := build_get_is_pkg_init.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init.

#[global] Instance : IsPkgInit math := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf math := build_get_is_pkg_init.

#[global] Instance : IsPkgInit fmt := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf fmt := build_get_is_pkg_init.

#[global] Instance : IsPkgInit quorum := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf quorum := build_get_is_pkg_init.

#[global] Instance : IsPkgInit tracker := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf tracker := build_get_is_pkg_init.

#[global] Instance : IsPkgInit confchange := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf confchange := build_get_is_pkg_init.

#[global] Instance : IsPkgInit big := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf big := build_get_is_pkg_init.

#[global] Instance : IsPkgInit rand := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf rand := build_get_is_pkg_init.

#[global] Instance : IsPkgInit bytes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf bytes := build_get_is_pkg_init.

#[global] Instance : IsPkgInit os := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf os := build_get_is_pkg_init.

#[global] Instance : IsPkgInit log := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf log := build_get_is_pkg_init.

#[global] Instance : IsPkgInit io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf io := build_get_is_pkg_init.

#[global] Instance : IsPkgInit errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf errors := build_get_is_pkg_init.

Definition is_initialized : iProp Σ :=
  ∃ errStopped,
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝.

#[global] Instance : IsPkgInit raft := define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf raft := build_get_is_pkg_init.

End init.
