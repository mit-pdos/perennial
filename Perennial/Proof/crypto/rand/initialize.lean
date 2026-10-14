/-
The proof of `crypto/rand.initialize'` (unfinished).
-/
module

public import Perennial.Spec.crypto.rand.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.rand.Assumptions]

theorem crypto.rand.initialize'.wp_proof :
    crypto.rand.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  -- Unprovable: `Reader'init` (`var Reader io.Reader = &reader{}` in Go, behind the
  -- platform's random source) is opaque (an axiom in Perennial/Code/crypto/rand.lean), and
  -- `isInitialized` asks for what it stores in `Reader`.
  sorry

end proof

end Perennial
