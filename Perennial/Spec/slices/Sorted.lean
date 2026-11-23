/-
`slices.Sorted`'s spec.
-/
module

public import Perennial.Proof.slices.OrderedBasics
public import Perennial.Golang.Theory.RangeFunc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `slices.Sorted(seq)` (`s := Collect(seq); Sort(s); return s`), at an ordered element type `Et`
whose `cmp.Less` implements the strict weak order `R` (as `slices.Sort`'s spec): runs the iterator
`seq` once, with what it needs (`Rseq`, given back), and returns a fresh slice (whose whole capacity
the caller owns) holding the elements it yields, the list `xs` (`ok xs`), sorted by `R`; `nil` when
`seq` yields nothing. Every list `seq` may yield has at most `2^62` elements (`Sort`'s premise: the
heapsort fallback's `2*i+1` overflows past it). -/
abbrev slices.Sorted.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) (SWO : StrictWeakOrder R)
    (seq : GoFunc) (Rseq : IProp GF) (ok : List E → Prop),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hseq" ∷ iter.SeqRuns seq Rseq ok ∗ "HR" ∷ Rseq ∗
        "%Hlength_bound" ∷ ⌜∀ xs, ok xs → xs.length ≤ 2 ^ 62⌝ ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (Val #(functions slices.Sorted [Et])) (Val #seq))
    {{ (s : GoSlice) (xs ys : List E), RET #s;
        "Hs" ∷ s ↦* ys ∗ "Hcap" ∷ ownSliceCap E s (DFrac.own 1) ∗ "HR" ∷ Rseq ∗
        "%Hok" ∷ ⌜ok xs⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ ys⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (yi yj : E), ys[i]? = some yi → ys[j]? = some yj →
          i < j → ¬ R yj yi⌝ ∗
        "%Hnil" ∷ ⌜xs = [] → s = slice.nil⌝ }}

end spec

end Perennial
