From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From Perennial.goose_lang Require Import proofmode notation.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.goose_lang Require Import typing adequacy.
Set Default Proof Using "Type".

Section recovery_adequacy.

Context `{ffi_semantics: ext_semantics}.
Context {ext_tys: ext_types ext}.
Context `{!ffi_interp ffi}.

Definition heap_namesO := leibnizO heap_names.
Global Instance heapG_perennialG `{!heapG Σ} : perennialG heap_lang heap_crash_lang heap_namesO Σ :=
{
  perennial_irisG := λ Hinv hnames, @heapG_irisG _ _ _ _ _ (heap_update _ _ Hinv (@pbundleT _ _ hnames));
  perennial_invG := λ _ _, eq_refl
}.

Section test.
Context `{!heapG Σ}.

Remark test s k Hi Hc t E (e: expr heap_lang) rec Φ Φinv Φr :
  wpr s k Hi Hc t E e rec Φ Φinv Φr -∗ True.
Proof. eauto. Qed.

End test.
End recovery_adequacy.
