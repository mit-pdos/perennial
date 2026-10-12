/-
`math/big.NewInt`'s spec.
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

/-- `math/big.NewInt(v)`: a new `big.Int` holding `v`. -/
abbrev math.big.NewInt.spec : Prop :=
  ∀ (v : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! NewInt)) (Val #v))
    {{ (p : Loc), RET #p; ownInt p (sint.Z v) }}

end spec

end Perennial
