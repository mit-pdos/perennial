From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import future spsc done chan_au_sel.
From New.proof Require Import time.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanGhostStateG Σ w64}.

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

End proof.
