/-
The proof of `sync.atomic.StoreInt32`.
-/
module

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

theorem sync.atomic.StoreInt32.wp_proof :
    sync.atomic.StoreInt32.spec (GF := GF) (hG := hG) := by
  intro addr v hal
  wp_start as _
  wp_bind (SwapN _ _ _)
  imod HΦ with ⟨%oldv, >Haddr, HΦ⟩
  wp_apply_core typed.wp_atomic_swap addr oldv v hal $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

end proof

end Perennial
