From iris.proofmode Require Import coq_tactics reduction.
From Perennial.goose_lang Require Import notation proofmode.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export list.impl.
Import uPred.

Set Default Proof Using "Type".

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types v : val.

Fixpoint val_of_list (l: list val) : val :=
  match l with
  | nil => InjLV (LitV LitUnit)
  | v :: l => InjRV (PairV v (val_of_list l))
  end.

End heap.
