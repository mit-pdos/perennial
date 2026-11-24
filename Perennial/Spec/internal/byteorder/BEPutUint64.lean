/-
`internal/byteorder.BEPutUint64`'s spec.
-/
module

public import Perennial.Proof.internal.byteorder.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.byteorder.Assumptions]

/-- `BEPutUint64(b, v)` writes `v`'s 8 bytes, big-endian, at the start of `b` (Go's bounds check
`_ = b[7]` panics on a shorter `b`, which the premise excludes). -/
abbrev internal.byteorder.BEPutUint64.spec : Prop :=
  ∀ (b : GoSlice) (space rem : List w8) (v : w64),
  space.length = 8 →
  {{ (b ↦* (space ++ rem) : IProp GF) }}
    (App (App (Val (@! internal.byteorder.BEPutUint64)) (Val #b)) (Val #v))
  {{ RET #(); b ↦* ((u64Le v).reverse ++ rem) }}

end spec

end Perennial
