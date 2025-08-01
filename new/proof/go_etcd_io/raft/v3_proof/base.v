Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
Require Export New.proof.context New.proof.sync.


Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context  `{!quorum.GlobalAddrs}.
Context  `{!tracker.GlobalAddrs}.
Context  `{!raft.GlobalAddrs}.

#[global]
Program Instance is_pkg_init_raftpb : IsPkgInit raftpb :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_raftpb.

#[global]
Program Instance is_pkg_init_strconv : IsPkgInit strconv :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_strconv.

#[global]
Program Instance is_pkg_init_slices : IsPkgInit slices :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_slices.

#[global]
Program Instance is_pkg_init_strings : IsPkgInit strings :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_strings.

#[global]
Program Instance is_pkg_init_math : IsPkgInit math :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_math.

#[global]
Program Instance is_pkg_init_fmt : IsPkgInit fmt :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_fmt.

#[global]
Program Instance is_pkg_init_quorum : IsPkgInit quorum :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_quorum.

#[global]
Program Instance is_pkg_init_tracker : IsPkgInit tracker :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_tracker.

#[global]
Program Instance is_pkg_init_confchange : IsPkgInit confchange :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_confchange.

#[global]
Program Instance is_pkg_init_big : IsPkgInit big :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_big.

#[global]
Program Instance is_pkg_init_rand : IsPkgInit rand :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_rand.

#[global]
Program Instance is_pkg_init_bytes : IsPkgInit bytes :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_bytes.

#[global]
Program Instance is_pkg_init_os : IsPkgInit os :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_os.

#[global]
Program Instance is_pkg_init_log : IsPkgInit log :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_log.

#[global]
Program Instance is_pkg_init_io : IsPkgInit io :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_io.

#[global]
Program Instance is_pkg_init_errors : IsPkgInit errors :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_errors.

Definition foo := ltac2:(build_pkg_init ()).

#[global]
Program Instance is_pkg_init_raft : IsPkgInit raft :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_raft.

End init.
