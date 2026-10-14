/-
The proof of `math.initialize'`.
-/
module

public import Perennial.Spec.math.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

/-- The initializer of `math` calls the package's (unmodeled) `init` function
`_'init`, so this is not provable. -/
theorem math.initialize'.wp_proof :
    math.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  -- Unprovable: `useFMA'init`, `_sin'init`, ... are opaque (axioms in Perennial/Code/math.lean).
  sorry

end proof

end Perennial
