From New.proof Require Export proof_prelude.
From New.proof Require Import strings time sync.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Export channel.
From New.code Require Import github_com.goose_lang.goose.testdata.examples.channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) chan_spec_raw_examples := build_get_is_pkg_init_wf.
End proof.
