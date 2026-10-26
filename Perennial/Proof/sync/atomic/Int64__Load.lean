/-
The proof of `sync.atomic.Int64.Load`.
-/
module

public import Perennial.Spec.sync.atomic.Int64__Load
public import Perennial.Spec.sync.atomic.LoadInt64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.Int64.Load.wp_proof
    (wp_LoadInt64 : sync.atomic.LoadInt64.spec (GF := GF) (hG := hG)) :
    sync.atomic.Int64.Load.spec (GF := GF) (hG := hG) := by
  intro u dq
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadInt64 $$ [] [HΦ «$res0»]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt64_unseal, ownInt64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
  iintro Hv
  imod HΦ $$ [- «$res0»] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
