/-
`internal.bytealg.MakeNoZero`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.MakeNoZero(n)`, for `0 ≤ n ≤ maxAlloc`: a new slice of `n` bytes (zero in the
model, unspecified in Go: a caller must not read a byte before writing it). -/
abbrev internal.bytealg.MakeNoZero.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n ∧ sint.Z n ≤ maxAlloc →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val (@! MakeNoZero)) (Val #n))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* List.replicate (sint.nat n) (W8 0) ∗ ownSliceCap w8 sl (DFrac.own 1) }}

end spec

end Perennial
