/-
The proof of `sync.atomic.b32`.
-/
module

public import Perennial.Spec.sync.atomic.b32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.b32.wp_proof :
    sync.atomic.b32.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start as _
  cases b <;> simp only [b32w, Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;> iexact HΦ

end proof

end Perennial
