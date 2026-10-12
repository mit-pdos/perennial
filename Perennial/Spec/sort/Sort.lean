/-
`sort.Sort`'s spec.
-/
module

public import Perennial.Proof.sort.SorterBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

open slices

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.Sort(data)` sorts the list a sorter holds by a strict weak order `R`: it leaves the
sorter holding a permutation of the list in which no element is `R`-less than an earlier one. As
`slices.SortFunc` (`Perennial/Proof/slices/SortFunc.lean`), it needs at most `2^62` elements:
past that, the heapsort fallback's `2*root+1` overflows `int`. -/
abbrev sort.«Sort».spec : Prop :=
  ∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    (SWO : StrictWeakOrder R) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "Hxs" ∷ own xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (@! «Sort»)) (Val #(interface.ok x)))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }}

end spec

end Perennial
