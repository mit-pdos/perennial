/-
The proof of `log.(*Logger).SetFlags`.
-/
module

public import Perennial.Spec.log.Logger__SetFlags
public import Perennial.Spec.sync.atomic.Int32__Store

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

theorem log.Logger.SetFlags.wp_proof
    (wp_Store : sync.atomic.Int32.Store.spec (GF := GF) (hG := hG)) :
    log.Logger.SetFlags.spec (GF := GF) (hG := hG) := by
  intro l f flag
  wp_start as ⟨%Hal, Hf⟩
  have Hnn : _ ≠ null := Hal
  wp_auto
  wp_apply_core wp_Store $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hf
  iintro Hf
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ
  iexact Hf

end proof

end Perennial
