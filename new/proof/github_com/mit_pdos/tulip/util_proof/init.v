From New.proof.github_com.goose_lang Require Export std.
From New.proof.github_com.mit_pdos.tulip Require Export tulip.
From New.proof.github_com.tchajed Require Export marshal.
From New.proof Require Import grove_prelude.
From New.generatedproof.github_com.mit_pdos.tulip Require Export util.

Section proof.
Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ}.

#[global] Program Instance : IsPkgInit util := ltac2:(build_pkg_init ()).

End proof.
