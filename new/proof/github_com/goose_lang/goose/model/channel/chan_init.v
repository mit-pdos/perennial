From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.  
Context `{!goGlobalsGS Σ}.
Context  `{!chanGhostStateG Σ}.
#[global] Program Instance : IsPkgInit channel := ltac2:(build_pkg_init ()).
End proof.
