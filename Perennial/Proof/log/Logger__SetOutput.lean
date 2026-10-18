/-
The proof of `log.(*Logger).SetOutput`.
-/
module

public import Perennial.Spec.log.Logger__SetOutput
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Bool__Store

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
variable [package_sem : log.Assumptions]

theorem log.Logger.SetOutput.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Store : sync.atomic.Bool.Store.spec (GF := GF) (hG := hG)) :
    log.Logger.SetOutput.spec (GF := GF) (hG := hG) := by
  intro l b w
  wp_start as ⟨#Hmu, Hb⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hd := io.isInit_access $$ Hio
  icases Hd with ⟨%dv, #Hd⟩
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, %w0, Hout⟩
  -- `w == io.Discard`: `false` unless `w`'s dynamic type is `Discard`'s, `io.discard`, an
  -- empty struct (comparable, and all its values equal)
  cases w
  case' ok ii => by_cases hty : ii.ty = io.discard.ty <;> simp only [hty, ↓reduceIte]
  -- in each case of the comparison: store it in `isDiscard`, then the deferred `Unlock`
  all_goals
    wp_auto
    wp_apply_core wp_Store $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists _
    iframe Hb
    iintro Hb
    imod Hmask with -
    imodintro
    wp_auto
    wp_apply wp_Unlock $$ [Hlocked Hout]
    · iframe Hmu Hlocked; inext; iexists _; iexact Hout
    iapply HΦ
    iexists _
    iexact Hb

end proof

end Perennial
