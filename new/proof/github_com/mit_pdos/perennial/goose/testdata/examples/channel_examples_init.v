From New.proof Require Export proof_prelude.
From New.proof Require Import strings time sync.
From New.generatedproof.github_com.mit_pdos.perennial.goose.testdata.examples Require Export channel.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) pkg_id.lock := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pkg_id.lock := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) channel_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) channel_examples := build_get_is_pkg_init_wf.
End proof.
