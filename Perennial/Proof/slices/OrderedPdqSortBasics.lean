/-
`lessImplements_elim`, for the proof of `pdqsortOrdered` (which is that of
`pdqsortCmpFunc` for the `cmp.Ordered` copy of the code, from the same pure lemmas).
-/
module

public import Perennial.Proof.slices.PdqSortBasics
public import Perennial.Proof.slices.OrderedBasics
public import Perennial.Proof.slices.OrderedPartitionBasics
public import Perennial.Proof.slices.OrderedInsertionSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

/-- Unfold `lessImplements` into the Texan triple for `cmp.Less` (so that it can be
`wp_apply`ed without unfolding `lessImplements` in the goal). -/
theorem lessImplements_elim :
    lessImplements (GF := GF) (Et := Et) R ⊢ iprop(∀ (x y : E),
      {{ True }}
        (App (App (Val #(functions cmp.Less [Et])) (Val #x)) (Val #y))
      {{ (b : Bool), RET #b; ⌜b = true ↔ R x y⌝ }}) := by
  unfold lessImplements; exact .rfl

end proof

end slices

end Perennial
