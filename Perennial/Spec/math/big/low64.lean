/-
`math/big.low64`'s spec.
-/
module

public import Perennial.Proof.math.big.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

/-- `math/big.low64(s)`: the least significant word of the magnitude `s` (`0` if empty). -/
abbrev math.big.low64.spec : Prop :=
  ∀ (s : GoSlice) (ws : List w64) (dq : DFrac),
    {{ (s ↦*{dq} ws : IProp GF) }}
      (App (Val (@! low64)) (Val #s))
    {{ RET #(ws.headD (W64 0)); s ↦*{dq} ws }}

end spec

end Perennial
