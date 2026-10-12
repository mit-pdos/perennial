/-
The proof of `sync.NewCond`.
-/
module

public import Perennial.Spec.sync.NewCond

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.NewCond.wp_proof :
    sync.NewCond.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as _
  wp_auto
  wp_pures
  wp_alloc c as Hc
  iStructNamed Hc
  ipersist L
  ipersist notify
  imod inv_alloc copyCheckerN ⊤ (copyCheckerInv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  wp_pures
  iapply HΦ
  rw [isCond_unseal]; unfold isCondDef
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
  iframe #
  done

end proof

end Perennial
