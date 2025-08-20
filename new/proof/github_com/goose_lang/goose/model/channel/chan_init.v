From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.  
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context  `{!chanGhostStateG Σ}.
#[global] Instance : IsPkgInit channel := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf channel := build_get_is_pkg_init.
#[global] Instance : IsPkgDefinedTransitiveClosure channel := build_is_pkg_defined_tc.
End proof.
