/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.Listen`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.Listen

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

theorem github_com.mit_pdos.gokv.grove_ffi.Listen.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.Listen.spec (GF := GF) (hG := hG) := fun host Hhost => by
  wp_start as Hlis
  wp_bind (ExternalOp _ _ _)
  wp_apply wp_ListenOp host Hhost $$ Hlis with Hlis
  iapply wp_fupd
  wp_apply wp_alloc_untyped _ (by simp [val.isPanic]) with %l Hl
  ipersist Hl
  imodintro
  iapply HΦ
  unfold isListener
  iframe Hl Hpkg Hlis

end proof

end Perennial
