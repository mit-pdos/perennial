/-
The proof of `sync.atomic.Uint64.Store`.
-/
module

public import Perennial.Spec.sync.atomic.Uint64__Store
public import Perennial.Spec.sync.atomic.StoreUint64

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

theorem sync.atomic.Uint64.Store.wp_proof
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG)) :
    sync.atomic.Uint64.Store.spec (GF := GF) (hG := hG) := by
  intro u v
  wp_start as _
  wp_auto
  wp_apply_core wp_StoreUint64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
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
