Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync.


Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} `{!GoContext}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'raftpb).
#[global] Program Instance : IsPkgInit raftpb :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'strconv).
#[global] Program Instance : IsPkgInit strconv :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'slices).
#[global] Program Instance : IsPkgInit slices :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'strings).
#[global] Program Instance : IsPkgInit strings :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'math).
#[global] Program Instance : IsPkgInit math :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'fmt).
#[global] Program Instance : IsPkgInit fmt :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'quorum).
#[global] Program Instance : IsPkgInit quorum :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'tracker).
#[global] Program Instance : IsPkgInit tracker :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'confchange).
#[global] Program Instance : IsPkgInit confchange :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'big).
#[global] Program Instance : IsPkgInit big :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'rand).
#[global] Program Instance : IsPkgInit rand :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'bytes).
#[global] Program Instance : IsPkgInit bytes :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'os).
#[global] Program Instance : IsPkgInit os :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'log).
#[global] Program Instance : IsPkgInit log :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'io).
#[global] Program Instance : IsPkgInit io :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'errors).
#[global] Program Instance : IsPkgInit errors :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

Definition foo := ltac2:(build_pkg_init ()).

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'raft).
#[global] Program Instance : IsPkgInit raft :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End init.
