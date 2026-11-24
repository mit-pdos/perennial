/-
The proof of `errors.As` (the real `wrap.go`: `As` and its tree walk `as`, over the Go model of
`internal/reflectlite`).
-/
module

public import Perennial.Spec.errors.As

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/- SORRY (reflect S0.5): `As` is now the real `wrap.go` over the model of `internal/reflectlite`
(the semantics' `AsAssign` and the Go model's `asWalk`/`asAssign` are retired); its proof over
`internal.reflectlite`'s specs (`ValueOf`, `Value.{Type,IsNil,Elem,Set}`,
`rtype.{Kind,Elem,Implements,AssignableTo}`) and `as`'s is to be redone. -/
theorem errors.As.wp_proof :
    errors.As.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end Perennial
