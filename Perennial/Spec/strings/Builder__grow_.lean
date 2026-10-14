/-
`strings.Builder.grow`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `b.grow(n)` moves the bytes to a new buffer of `2 * cap + n` bytes, which must not exceed
`maxAlloc` (`MakeNoZero` panics there). -/
abbrev strings.Builder.grow.spec : Prop :=
  ∀ (b addr : Loc) (buf : GoSlice) (s : GoString) (n : w64),
  0 ≤ sint.Z n ∧ 2 * sint.Z buf.cap + sint.Z n ≤ internal.bytealg.maxAlloc →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗
        buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"grow")) (Val #n))
    {{ RET #(); ∃ buf' : GoSlice, b ↦ ({ addr' := addr, buf' := buf' } : Builder) ∗
        buf' ↦* s ∗ ownSliceCap w8 buf' (DFrac.own 1) }}

end spec

end Perennial
