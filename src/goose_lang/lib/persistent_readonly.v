From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import iris.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.

Section goose_lang.
  Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.

  Class AsMapsTo (P: iProp Σ)
        (Φ : loc -> Qp -> val -> iProp Σ) (l: loc) (v: val) :=
    { as_mapsto : P ≡ Φ l 1%Qp v;
      as_mapsto_fractional :> forall l v, Fractional (λ q, Φ l q v);
      as_mapsto_timeless :> forall l q v, Timeless (Φ l q v);
    }.

  Arguments as_mapsto {P Φ l v} AsMapsTo.

  Let N := nroot .@ "readonly".

  Definition readonly P `{H: AsMapsTo P Φ l v}: iProp Σ :=
    inv N (∃ q, Φ l q v).

  Theorem readonly_alloc P `{H: AsMapsTo P Φ l v} q E :
    Φ l q v ={E}=∗ readonly P.
  Proof.
    iIntros "HP".
    iMod (inv_alloc with "[HP]") as "$"; auto.
  Qed.

  Theorem readonly_alloc_1 P `{H: AsMapsTo P Φ l v} E :
    P ={E}=∗ readonly P.
  Proof.
    iIntros "HP".
    rewrite {1}H.(as_mapsto).
    iApply (readonly_alloc with "HP").
  Qed.

  Global Instance readonly_persistent P `{H: AsMapsTo P Φ l v} : Persistent (readonly P) := _.

  Instance as_mapsto_AsFractional P `{H: AsMapsTo P Φ l v} :
    AsFractional (Φ l q v) (λ q, Φ l q v) q.
  Proof.
    split; auto.
    apply _.
  Qed.

  Theorem readonly_load P `{H: AsMapsTo P Φ l v} E :
    ↑N ⊆ E ->
    readonly P ={E}=∗ ∃ q, Φ l q v.
  Proof.
    iIntros (Hsub) "Hro".
    rewrite /readonly.
    assert (Timeless (∃ q, Φ l q v)).
    { apply _. }
    iMod (inv_dup_acc (∃ q, Φ l q v) with "Hro []") as ">H"; first by auto.
    { iIntros "HΦ".
      iDestruct "HΦ" as (q) "HΦ".
      iDestruct (fractional_half with "HΦ") as "[HΦ1 HΦ2]".
      iSplitL "HΦ1"; iExists _; iFrame. }
    iModIntro.
    auto.
  Qed.

End goose_lang.

Typeclasses Opaque readonly.
Opaque readonly.
