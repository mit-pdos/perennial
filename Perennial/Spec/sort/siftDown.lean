/-
`sort.siftDown`'s spec.
-/
module

public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

open slices

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `siftDown(data, lo, hi, first)` sifts the element at `first + lo` down the heap
`[first + lo, first + hi)` (first conjunct; `lo < hi`), and returns at once for `lo = hi = 0`
(second conjunct). The two triples (`wp_siftDown` and the private `wp_siftDown_trivial`
before) are separate proofs, neither implying the other. -/
abbrev sort.siftDown.spec : Prop :=
  (∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF)
      (R : E → E → Prop) [StrictWeakOrder R] (lo hi a b : w64) (xs : List E),
      {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
          "Hxs" ∷ own xs ∗
          "#Hsrt" ∷ isSorter x own R ∗
          "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z a + sint.Z lo ∧
                          sint.Z a + sint.Z lo < sint.Z a + sint.Z hi ∧
                          sint.Z a + sint.Z hi ≤ sint.Z b ∧
                          sint.Z b ≤ xs.length ∧
                          xs.length ≤ 2 ^ 62⌝ ∗
          "%HSegSorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                      (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                      (sint.nat a ≤ i ∧ i < sint.nat b) →
                      xs[i]? = some xi →
                      xs[j]? = some xj → ¬ R xj xi⌝ ∗
          "%Heap" ∷ ⌜IsHeapSeg R xs (sint.nat a) (sint.nat b) (sint.nat lo + 1) (sint.nat hi)⌝ }}
        (App (App (App (App (Val (@! siftDown)) (Val #(interface.ok x))) (Val #lo)) (Val #hi)) (Val #a))
      {{ (xs' : List E), RET #();
          "Hxs" ∷ own xs' ∗
          "%HPermPost" ∷ ⌜xs ≡ₚ xs'⌝ ∗
          "%HSegSortedPost" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                      (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                      (sint.nat a ≤ i ∧ i < sint.nat b) →
                      xs'[i]? = some xi →
                      xs'[j]? = some xj → ¬ R xj xi⌝ ∗
          "%Heap" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi)⌝ ∗
          "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}) ∧
  (∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (a b : w64) (xs : List E),
      {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
          "Hxs" ∷ own xs ∗
          "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
        (App (App (App (App (Val (@! siftDown)) (Val #(interface.ok x))) (Val #(W64 0)))
          (Val #(W64 0))) (Val #a))
      {{ RET #(); "Hxs" ∷ own xs }})

end spec

end Perennial
