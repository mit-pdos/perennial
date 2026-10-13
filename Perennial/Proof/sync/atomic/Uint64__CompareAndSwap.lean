/-
The proof of `sync.atomic.Uint64.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Uint64__CompareAndSwap
public import Perennial.Spec.sync.atomic.CompareAndSwapUint64

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

theorem sync.atomic.Uint64.CompareAndSwap.wp_proof
    (wp_CompareAndSwapUint64 : sync.atomic.CompareAndSwapUint64.spec (GF := GF) (hG := hG)) :
    sync.atomic.Uint64.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro u old new
  wp_start_folded as _
  iintro %hu %hal
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  wp_auto
  wp_apply_core (wp_CompareAndSwapUint64 _ _ _ (by first | exact hal | simpa using hal)) $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownUint64_unseal, ownUint64Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
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
