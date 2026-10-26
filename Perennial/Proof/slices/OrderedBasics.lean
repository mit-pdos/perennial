/-
The comparison of the `cmp.Ordered` sorts (`zsortordered.go`), shared by the
`pdqsortOrdered` proofs.

The `Ordered` functions are the `CmpFunc` ones with `cmp(x, y) < 0`
replaced by `cmp.Less(x, y)` and without the `cmp` argument; their proofs reuse every
pure lemma of the `CmpFunc` proofs and assume of `cmp.Less` at the element type what
`cmpImplements` assumes of the comparison function (`lessImplements`).
-/
module

public import Perennial.Proof.slices.SortBasics
public import Perennial.Proof.cmp.Base
public import Perennial.Spec.cmp.Less

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop)

/-- `cmp.Less` at the element type `Et` implements `R`. -/
def lessImplements : IProp GF :=
  iprop(∀ (x y : E),
    {{ True }}
      (App (App (Val #(functions cmp.Less [Et])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ R x y⌝ }})

instance lessImplements_persistent : Persistent (lessImplements (GF := GF) (Et := Et) R) := by
  unfold lessImplements; infer_instance

end proof

section string
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

open Iris.ProofMode in
/-- At `string`, `cmp.Less` implements Go's order on strings (from `cmp.Less`'s spec). -/
theorem lessImplements_string_of (wp_Less : cmp.Less.spec (GF := GF) (hG := hG)) :
    ⊢ lessImplements (GF := GF) (Et := go.string) go.GoStringLt := by
  unfold lessImplements
  iintro %x %y
  imodintro
  iintro %Φ _ HΦ
  wp_apply wp_Less.2 x y with %b %Hb
  iapply HΦ
  ipureintro
  exact Hb

end string

end slices

end Perennial
end
