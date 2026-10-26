/-
The proof of `sync.atomic.Bool.Load`.
-/
module

public import Perennial.Spec.sync.atomic.Bool__Load
public import Perennial.Spec.sync.atomic.LoadUint32

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

theorem sync.atomic.Bool.Load.wp_proof
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG)) :
    sync.atomic.Bool.Load.spec (GF := GF) (hG := hG) := by
  intro u dq
  wp_start as _
  wp_auto
  wp_apply_core wp_LoadUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w v)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  cases v <;> simp [b32w] <;> iexact HΦ

end proof

end Perennial
