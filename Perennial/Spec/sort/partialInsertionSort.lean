/-
`sort.partialInsertionSort`'s spec.
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

abbrev sort.partialInsertionSort.spec : Prop :=
  ∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    [StrictWeakOrder R] (a b : w64) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%Header" ∷ ⌜header R xs (sint.nat a) (sint.nat b)⌝ ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val (@! partialInsertionSort)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (xs' : List E) (bl : Bool), RET #bl;
        own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜if bl then IsSortedSeg R xs' (sint.nat a) (sint.nat b) else True⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}

end spec

end Perennial
