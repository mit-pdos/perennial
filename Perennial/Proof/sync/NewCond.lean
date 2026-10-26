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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.NewCond.wp_proof :
    sync.NewCond.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as _
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  iStructNamed Hc
  ipersist L
  ipersist notify
  imod inv_alloc copyCheckerN ⊤ (copyCheckerInv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  imodintro
  iapply HΦ
  rw [isCond_unseal]; unfold isCondDef
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
  iframe #
  done

end proof

end Perennial
