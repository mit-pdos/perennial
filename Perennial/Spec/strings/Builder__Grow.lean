/-
`strings.Builder.Grow`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderDefs

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

/-- `b.Grow(n)`, for `n ≥ 0`. When the buffer has fewer than `n` free bytes, `grow` allocates
`2 * cap + n` bytes, which must not exceed `maxAlloc` (Go panics there). -/
abbrev strings.Builder.Grow.spec : Prop :=
  ∀ (b addr : Loc) (buf : GoSlice) (s : GoString) (n : w64),
  addr = null ∨ addr = b → 0 ≤ sint.Z n →
  (sint.Z buf.cap - sint.Z buf.len < sint.Z n →
    2 * sint.Z buf.cap + sint.Z n ≤ internal.bytealg.maxAlloc) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗
        buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"Grow")) (Val #n))
    {{ RET #(); ownBuilder b s }}

end spec

end Perennial
