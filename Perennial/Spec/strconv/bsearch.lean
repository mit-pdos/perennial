/-
`strconv.bsearch`'s spec, at its two instantiations (`IsPrint`'s tables of `uint16` and `uint32`).
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `bsearch(s, v)` (a binary search, `slices.BinarySearch` without NaN checks) returns an index
`i` with `0 ≤ i ≤ len(s)` and a boolean, reading `s`; at `[]uint16` and at `[]uint32`. -/
abbrev strconv.bsearch.spec : Prop :=
  (∀ (s : GoSlice) (xs : List w16) (v : w16) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ s ↦*{dq} xs }}
      (App (App (Val #(functions bsearch [go.GoType.SliceType go.uint16, go.uint16])) (Val #s))
        (Val #v))
    {{ (i : w64) (found : Bool), RET (PairV #i #found);
        s ↦*{dq} xs ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ xs.length⌝ }}) ∧
  (∀ (s : GoSlice) (xs : List w32) (v : w32) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ s ↦*{dq} xs }}
      (App (App (Val #(functions bsearch [go.GoType.SliceType go.uint32, go.uint32])) (Val #s))
        (Val #v))
    {{ (i : w64) (found : Bool), RET (PairV #i #found);
        s ↦*{dq} xs ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ xs.length⌝ }})

end spec

end Perennial
