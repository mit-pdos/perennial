/-
The proof of `sync.atomic.Bool.Store`.
-/
module

public import Perennial.Spec.sync.atomic.Bool__Store
public import Perennial.Spec.sync.atomic.StoreUint32
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

theorem sync.atomic.Bool.Store.wp_proof
    (wp_b32 : sync.atomic.b32.spec (GF := GF) (hG := hG))
    (wp_StoreUint32 : sync.atomic.StoreUint32.spec (GF := GF) (hG := hG)) :
    sync.atomic.Bool.Store.spec (GF := GF) (hG := hG) := by
  intro u v
  wp_start as _
  wp_auto
  wp_apply wp_b32
  wp_apply_core wp_StoreUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists (b32w old)
  iframe v
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
