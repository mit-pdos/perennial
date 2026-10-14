/-
`sort.medianAdjacent`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

abbrev sort.medianAdjacent.spec : Prop :=
  ∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    [StrictWeakOrder R] (a : w64) (swaps_l : Loc) (xs : List E) (swaps : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (Val (@! medianAdjacent)) (Val #(interface.ok x))) (Val #a)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        own xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }}

end spec

end Perennial
