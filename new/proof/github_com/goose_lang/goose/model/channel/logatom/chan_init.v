From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
From New.code.github_com.goose_lang.goose Require Export model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Export model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context  `{!chanG Σ}.
#[global] Instance : IsPkgInit (iProp Σ) channel := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) channel := build_get_is_pkg_init_wf.
End proof.
