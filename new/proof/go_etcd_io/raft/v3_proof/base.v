Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync.


Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Local Notation deps_raftpb := (ltac2:(build_pkg_init_deps 'raftpb) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit raftpb :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_raftpb;
  |}.

Local Notation deps_strconv := (ltac2:(build_pkg_init_deps 'strconv) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit strconv :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_strconv;
  |}.

Local Notation deps_slices := (ltac2:(build_pkg_init_deps 'slices) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit slices :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_slices;
  |}.

Local Notation deps_strings := (ltac2:(build_pkg_init_deps 'strings) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit strings :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_strings;
  |}.

Local Notation deps_math := (ltac2:(build_pkg_init_deps 'math) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit math :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_math;
  |}.

Local Notation deps_fmt := (ltac2:(build_pkg_init_deps 'fmt) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit fmt :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_fmt;
  |}.

Local Notation deps_quorum := (ltac2:(build_pkg_init_deps 'quorum) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit quorum :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_quorum;
  |}.

Local Notation deps_tracker := (ltac2:(build_pkg_init_deps 'tracker) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit tracker :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_tracker;
  |}.

Local Notation deps_confchange := (ltac2:(build_pkg_init_deps 'confchange) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit confchange :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_confchange;
  |}.

Local Notation deps_big := (ltac2:(build_pkg_init_deps 'big) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit big :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_big;
  |}.

Local Notation deps_rand := (ltac2:(build_pkg_init_deps 'rand) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit rand :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_rand;
  |}.

Local Notation deps_bytes := (ltac2:(build_pkg_init_deps 'bytes) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit bytes :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_bytes;
  |}.

Local Notation deps_os := (ltac2:(build_pkg_init_deps 'os) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit os :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_os;
  |}.

Local Notation deps_log := (ltac2:(build_pkg_init_deps 'log) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit log :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_log;
  |}.

Local Notation deps_io := (ltac2:(build_pkg_init_deps 'io) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit io :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_io;
  |}.

Local Notation deps_errors := (ltac2:(build_pkg_init_deps 'errors) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit errors :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_errors;
  |}.

Definition is_initialized : iProp Σ :=
  ∃ errStopped,
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝.

Local Notation deps := (ltac2:(build_pkg_init_deps 'raft) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit raft :=
  {|
    is_pkg_init_def := is_initialized;
    is_pkg_init_deps := deps;
  |}.

End init.
