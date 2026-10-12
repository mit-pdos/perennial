/-
`slices.siftDownOrdered`'s spec.
-/
module

public import Perennial.Proof.slices.OrderedBasics
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `siftDownOrdered(data, lo, hi, first)` sifts the element at `first + lo` down the heap
`[first + lo, first + hi)` (first conjunct; `lo < hi`), and returns at once for `lo = hi = 0`
(second conjunct, `wp_siftDownOrdered_Trivial` in `Results.lean`). The two triples (`wp_siftDownOrdered` and
`wp_siftDownOrdered_Trivial` before) are separate proofs, neither implying the other. -/
abbrev slices.siftDownOrdered.spec : Prop :=
  (∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
      [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
      (lo hi a b : w64) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
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
      (App (App (App (App (Val #(functions siftDownOrdered [Et])) (Val #data)) (Val #lo))
        (Val #hi)) (Val #a))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%HPermPost" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%HSegSortedPost" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs'[i]? = some xi →
                    xs'[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}) ∧
  (∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
      [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
      (a b : w64) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions siftDownOrdered [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a))
    {{ RET #(); "Hxs" ∷ data ↦* xs }})

end spec

end Perennial
