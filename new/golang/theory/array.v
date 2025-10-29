From Perennial.Helpers Require Import List ListLen Fractional NamedProps.
From iris.algebra Require Import dfrac.
From Perennial.iris_lib Require Import dfractional.
From Perennial.goose_lang Require Import ipersist.
From New.golang.defn Require Export slice.
From New.golang.theory Require Import loop.
From Perennial Require Import base.

Section lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Context `{!IntoVal V}.
Context `{!TypedPointsto (Σ:=Σ) V}.
Context `{!IntoValTyped V t}.

Lemma own_array_nil ptr dq :
  ⊢ ptr ↦{dq} (array.mk t 0 []).
Proof.
  rewrite typed_pointsto_unseal. simpl. iPureIntro. done.
Qed.

Lemma own_array_len ptr dq n vs :
  ptr ↦{dq} (array.mk t n vs) -∗ ⌜ n = Z.of_nat $ length vs ⌝.
Proof.
  rewrite typed_pointsto_unseal. simpl. iIntros "[% _] !%". done.
Qed.

Lemma own_array_acc i dq n vs :
  0 ≤ sint.Z i →
  vs !! (sint.nat i) = Some v →
  s ↦[t]*{dq} vs -∗
  slice_index_ref t (sint.Z i) s ↦{dq} v ∗
  (∀ v', slice_index_ref t (sint.Z i) s ↦{dq} v' -∗
        s ↦[t]*{dq} (<[sint.nat i := v']> vs)).

  ptr ↦{dq} (array.mk t n vs) -∗ ⌜ n = Z.of_nat $ length vs ⌝.
