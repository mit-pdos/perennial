/-
`math.bits.Len`'s spec.
-/
module

public import Perennial.Proof.math.bits.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- `Len(x)` (on a 64-bit platform, `Len64(x)`) is the bit length `l` of `x`: `x < 2 ^ l`,
and `2 ^ l ≤ 2 * x` unless `x = 0` (so `l ≤ 64`). -/
abbrev math.bits.Len.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len)) (Val #x))
    {{ (l : w64), RET #l; ⌜uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧
        (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x)⌝ }}

end spec

end Perennial
