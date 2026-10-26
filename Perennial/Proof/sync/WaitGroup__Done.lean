/-
The proof of `sync.(*WaitGroup).Done`.
-/
module

public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Add

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.WaitGroup.Done.wp_proof
    (wp_WaitGroup_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG)) :
    sync.WaitGroup.Done.spec (GF := GF) (hG := hG) := by
  intro wg γ N
  wp_start as #His
  wp_auto
  wp_apply_core wp_WaitGroup_Add wg (W64 (-1)) γ N $$ [] [-]
  · iframe #
  imod HΦ with HΦ
  imodintro
  inext
  iNamed HΦ
  iexists oldc
  iframe Hwg
  have h1 : W32 (sint.Z (W64 (-1))) = W32 (-1) := by decide
  have h2 : sint.Z (W32 (-1)) = -1 := by decide
  rw [h1, h2]
  isplitr
  · ipureintro; omega
  ileft
  isplitr
  · ipureintro
    intro h; subst h; simp at Hbounds
  iintro Hctr
  imod HΦ $$ [Hctr] with HΦ
  · rw [show oldc - W32 1 = oldc + W32 (-1) by bv_omega]; iexact Hctr
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
