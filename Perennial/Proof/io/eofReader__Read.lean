/-
The proof of `eofReader__Read`.
-/
module

public import Perennial.Spec.io.eofReader__Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem io.eofReader.Read.wp_proof :
    io.eofReader.Read.spec (GF := GF) (hG := hG) :=
  fun p eof => by
  wp_start as #Heof
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
