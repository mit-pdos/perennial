From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import iris.
From Perennial.algebra Require Import deletable_heap.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import lifting.
From Perennial.goose_lang Require Import proofmode.

Section goose_lang.
  Context `{!invG Σ}.
  Context {L V: Type}.

  Class AsMapsTo (P: iProp Σ)
        (Φ : L -> Qp -> V -> iProp Σ) (l: L) (v: V) :=
    { as_mapsto : P ≡ Φ l 1%Qp v;
      as_mapsto_fractional :> forall l v, Fractional (λ q, Φ l q v);
      as_mapsto_timeless :> forall l q v, Timeless (Φ l q v);
    }.

  Arguments as_mapsto {P Φ l v} AsMapsTo.

  Let N := nroot .@ "readonly".

  Definition readonly_def P `{H: AsMapsTo P Φ l v}: iProp Σ :=
    inv N (∃ q, Φ l q v).
  Definition readonly_aux : seal (@readonly_def). Proof. by eexists. Qed.
  Definition readonly := readonly_aux.(unseal).
  Definition readonly_eq : @readonly = @readonly_def := readonly_aux.(seal_eq).
  Arguments readonly P {Φ}%function_scope {l v H}.

  Ltac unseal := rewrite readonly_eq /readonly_def.

  Theorem readonly_alloc P `{H: AsMapsTo P Φ l v} q E :
    Φ l q v ={E}=∗ readonly P.
  Proof.
    unseal.
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

  Global Instance readonly_persistent P `{H: AsMapsTo P Φ l v} : Persistent (readonly P).
  Proof. unseal; apply _. Qed.

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
    unseal.
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

Instance heap_mapsto_AsMapsTo `{ext: !ext_op} `{!na_heapG loc val Σ}
         (l: loc) (v: val) :
  AsMapsTo (l ↦ v) (λ l q v, l ↦{q} v)%I l v.
Proof.
  split; [done|apply _|apply _].
Qed.

Instance mapsto_AsMapsTo `{ffi_sem: ext_semantics} `(hG: gen_heapG L V Σ) l v :
  AsMapsTo (mapsto (hG:=hG) l 1 v) (λ l q v, mapsto (hG:=hG) l q v) l v.
Proof.
  split; [done|apply _|apply _].
Qed.

Hint Mode AsMapsTo - - - + - - - : typeclass_instances.
Arguments readonly {Σ invG0} {L V}%type_scope _%bi_scope {Φ}%function_scope {l v H}.
