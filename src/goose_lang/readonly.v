From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.

Section goose_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.

  Definition ptsto_ro (l: loc) (v: val): iProp Σ :=
    ∃ q, l ↦{q} Free v.

  Notation "l ↦ro v" := (ptsto_ro l v)
                          (at level 20, format "l  ↦ro  v") : bi_scope.

  Global Instance ptsto_ro_timeless l v : Timeless (l ↦ro v) := _.

  Theorem ptsto_ro_from_q l q v :
    l ↦{q} Free v -∗ l ↦ro v.
  Proof.
    iIntros "Hl".
    iExists q; iFrame.
  Qed.

  Theorem ptsto_ro_weaken l v :
    l ↦ Free v -∗ l ↦ro v.
  Proof.
    apply (ptsto_ro_from_q l 1 v).
  Qed.

  Theorem ptsto_ro_dup l v :
    l ↦ro v -∗ l ↦ro v ∗ l ↦ro v.
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (q) "Hl".
    iDestruct "Hl" as "[Hl1 Hl2]".
    iSplitL "Hl1"; iExists _; iFrame.
  Qed.

  (* make it possible to iDestruct [l ↦ro v] into two copies of itself;
     above we do something similar to actually prove ptsto_ro_dup.
   *)
  Global Instance ptsto_ro_into_sep l v : IntoSep (l ↦ro v) (l ↦ro v) (l ↦ro v).
  Proof.
    hnf.
    apply ptsto_ro_dup.
  Qed.

  Theorem ptsto_ro_agree l v1 v2 :
    l ↦ro v1 -∗ l ↦ro v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct "Hl1" as (q1) "Hl1".
    iDestruct "Hl2" as (q2) "Hl2".
    iDestruct (mapsto_agree with "Hl1 Hl2") as %Heq.
    inversion Heq; auto.
  Qed.

  (* TODO: for now this exposes the implementation of ptsto_ro, but maybe this
  isn't necessary once we have a triple for loads *)
  Theorem ptsto_ro_load l v :
    l ↦ro v -∗ ∃ q, l ↦{q} Free v.
  Proof.
    iIntros "Hro".
    iDestruct "Hro" as (q) "Hl".
    iExists q; iFrame.
  Qed.

End goose_lang.

Notation "l ↦ro v" := (ptsto_ro l v)
                        (at level 20, format "l  ↦ro  v") : bi_scope.

Typeclasses Opaque ptsto_ro.
Opaque ptsto_ro.
