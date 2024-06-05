From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang.lib Require Export typed_mem.impl.

Set Default Proof Using "Type".

Section go_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.
End go_lang.
