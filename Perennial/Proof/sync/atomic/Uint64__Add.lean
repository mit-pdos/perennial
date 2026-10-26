/-
The proof of `sync.atomic.Uint64.Add`.
-/
module

public import Perennial.Spec.sync.atomic.Uint64__Add
public import Perennial.Spec.sync.atomic.AddUint64

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

theorem sync.atomic.Uint64.Add.wp_proof
    (wp_AddUint64 : sync.atomic.AddUint64.spec (GF := GF) (hG := hG)) :
    sync.atomic.Uint64.Add.spec (GF := GF) (hG := hG) := by
  intro u delta
  wp_start as _
  wp_auto
  wp_apply_core wp_AddUint64 $$ [] [HΦ new]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
  iframe v
  iintro Hv
  imod HΦ $$ [- new] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
