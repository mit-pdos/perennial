/-
The proof of `sync.atomic.Int32.Store`.
-/
module

public import Perennial.Spec.sync.atomic.Int32__Store
public import Perennial.Spec.sync.atomic.StoreInt32

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

theorem sync.atomic.Int32.Store.wp_proof
    (wp_StoreInt32 : sync.atomic.StoreInt32.spec (GF := GF) (hG := hG)) :
    sync.atomic.Int32.Store.spec (GF := GF) (hG := hG) := by
  intro u v
  wp_start_folded as _
  iintro %hu
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  wp_auto
  wp_apply_core wp_StoreInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownInt32_unseal, ownInt32Def]
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
