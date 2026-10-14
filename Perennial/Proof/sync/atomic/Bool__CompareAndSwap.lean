/-
The proof of `sync.atomic.Bool.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Bool__CompareAndSwap
public import Perennial.Spec.sync.atomic.CompareAndSwapUint32
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

theorem sync.atomic.Bool.CompareAndSwap.wp_proof
    (wp_b32 : sync.atomic.b32.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapUint32 : sync.atomic.CompareAndSwapUint32.spec (GF := GF) (hG := hG)) :
    sync.atomic.Bool.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro u old new
  wp_start_folded as _
  iintro %hu
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  wp_auto
  wp_apply wp_b32
  wp_apply wp_b32
  wp_apply_core wp_CompareAndSwapUint32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownBool_unseal, ownBoolDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  have hiff : (b32w v = b32w old) ↔ (v = old) := ⟨b32w_inj, fun h => h ▸ rfl⟩
  iexists (b32w v), dq
  iframe v
  isplitr
  · ipureintro; simp only [hiff]; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    by_cases h : v = old <;> simp [h, hiff]
    · iexact Hv
    · iexact Hv
  imodintro
  wp_auto
  simp only [decide_eq_decide.mpr hiff]
  iexact HΦ

end proof

end Perennial
