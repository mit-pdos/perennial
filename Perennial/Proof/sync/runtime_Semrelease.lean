/-
The proof of `sync.runtime_Semrelease`.
-/
module

public import Perennial.Spec.sync.runtime_Semrelease
public import Perennial.Spec.sync.atomic.AddUint32

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

theorem sync.runtime_Semrelease.wp_proof
    (wp_AddUint32 : sync.atomic.AddUint32.spec (GF := GF) (hG := hG)) :
    sync.runtime_Semrelease.spec (GF := GF) (hG := hG) := by
  intro sema γ N _u1 _u2
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_auto
  wp_apply_core wp_AddUint32 $$ [] [-]
  · iPkgInit
  iinv Hsem with Hi Hclose
  icases Hi with ⟨%v, >Hs, >Hv⟩
  imod HΦ with ⟨%v1, Hv2, HΦ⟩
  icombine Hv Hv2 gives % ⟨_, Heq⟩
  subst Heq
  inext
  iexists v
  iframe Hs
  iintro Hs
  imod ghostVar_update_halves (v + W32 1) γ v v $$ Hv Hv2 with ⟨Hv, Hv2⟩
  imod HΦ $$ Hv2 with HΦ
  imod Hclose $$ [Hs Hv] with _
  · inext; iexists _; iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
