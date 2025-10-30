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

Lemma array_empty ptr dq :
  ⊢ ptr ↦{dq} (array.mk t 0 []).
Proof.
  rewrite typed_pointsto_unseal. simpl. iPureIntro. done.
Qed.

Lemma array_len ptr dq n vs :
  ptr ↦{dq} (array.mk t n vs) -∗ ⌜ n = Z.of_nat $ length vs ⌝.
Proof.
  rewrite typed_pointsto_unseal. simpl. iIntros "[% _] !%". done.
Qed.

Lemma array_acc p (i : Z) dq n (a : array.t t V n) (v: V) :
  0 ≤ i →
  a.(array.arr) !! (Z.to_nat i) = Some v →
  p ↦{dq} a -∗
  array_index_ref t i p ↦{dq} v ∗
  (∀ v', array_index_ref t i p ↦{dq} v' -∗
        p ↦{dq} (array.mk t n $ <[(Z.to_nat i) := v']> a.(array.arr))).
Proof.
  iIntros (Hpos Hlookup) "Harr".
  rewrite [in _ (array.t _ _ _)]typed_pointsto_unseal /=.
  iDestruct "Harr" as "[% Harr]".
  iDestruct (big_sepL_insert_acc _ _ (Z.to_nat i) with "Harr") as "[Hptsto Harr]".
  { done. }
  nat_cleanup. iFrame "Hptsto". iIntros (?) "Hptsto".
  iSpecialize ("Harr" with "Hptsto").
  iFrame. rewrite length_insert. done.
Qed.

Lemma array_split (k : w64) l dq n (a : array.t t V n) :
  0 ≤ sint.Z k ≤ sint.Z n →
  l ↦{dq} a ⊣⊢
  l ↦{dq} (array.mk t (sint.Z k) $ take (sint.nat k) a.(array.arr)) ∗
  array_index_ref t (sint.Z k) l ↦{dq} (array.mk t (n - sint.Z k) $ drop (sint.nat k) a.(array.arr)).
Proof.
  intros Hle. rewrite typed_pointsto_unseal /=. destruct a as [arr]. simpl.
  rewrite -{1}(take_drop (sint.nat k) arr).
  setoid_rewrite <- go.array_index_ref_add. len.
  iSplit.
  - iIntros "[% H]". subst. rewrite -!assoc. iSplitR; first len.
    rewrite comm. rewrite -assoc. iSplitR; first word.
    rewrite -{1}(take_drop (sint.nat k) arr).
    rewrite big_sepL_app. iDestruct "H" as "[H1 H2]".
    iFrame. iApply (big_sepL_impl with "H2").
    iIntros "!# * % H". iExactEq "H". f_equal.
    f_equal. len.
  - iIntros "([% H1] & [% H2])".
    iSplitR; first word.
    rewrite -{3}(take_drop (sint.nat k) arr).
    rewrite big_sepL_app. iFrame.
    iApply (big_sepL_impl with "H2").
    iIntros "!# * % H". iExactEq "H". f_equal.
    f_equal. len.
Qed.

End lemmas.
