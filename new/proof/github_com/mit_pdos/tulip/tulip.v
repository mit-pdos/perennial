From New.proof Require Import github_com.mit_pdos.gokv.grove_ffi.

From New.generatedproof.github_com.mit_pdos.tulip Require Import tulip.

Section program.
Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_inst : IsPkgInit tulip :=
  ltac2:(build_pkg_init ()).

End program.
