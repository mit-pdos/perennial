/-
`sort.order2`'s spec.
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

abbrev sort.order2.spec : Prop :=
  ∀ {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF) (R : E → E → Prop)
    [StrictWeakOrder R] (a b : w64) (swaps_l : Loc) (xs : List E) (swaps : w64) (xa xb : E),
    0 ≤ sint.Z a →
    0 ≤ sint.Z b →
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hsrt" ∷ isSorter x own R }}
      (App (App (App (App (Val (@! order2)) (Val #(interface.ok x))) (Val #a)) (Val #b)) (Val #swaps_l))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        own xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }}

end spec

end Perennial
