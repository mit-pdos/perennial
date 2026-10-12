/-
The proof of `internal.bytealg.initialize'`.
-/
module

public import Perennial.Spec.internal.bytealg.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `MaxLen` is set by the model of bytealg's `init`
(`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.initialize'.wp_proof :
    internal.bytealg.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w64) MaxLen go.int as HM
  unfold MaxLenAddr
  rw [show (go!"internal/bytealg.MaxLen" : GoString) = MaxLen from rfl]
  wp_bind ArbitraryInt
  wp_apply wp_ArbitraryInt as %x _
  iapply wp_fupd
  wp_if_destruct
  all_goals
    ipersist HM
    imodintro
    iframe Hown
    isPkgInit_unfold
    isplitl []
    · ipureintro; simp
    imodintro
    iexists _
    iframe HM
    ipureintro
    simp

end proof

end Perennial
