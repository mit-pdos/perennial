Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync.


Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit raftpb := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit strconv := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit slices := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit math := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit fmt := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit quorum := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit tracker := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit confchange := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit big := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit rand := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit bytes := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit os := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit log := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit io := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit errors := define_is_pkg_init True%I.

Definition is_initialized : iProp Σ :=
  ∃ errStopped,
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝.

#[global] Instance : IsPkgInit raft := define_is_pkg_init is_initialized.

End init.
