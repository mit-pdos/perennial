/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.Accept`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.Accept

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

theorem github_com.mit_pdos.gokv.grove_ffi.Accept.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.Accept.spec (GF := GF) (hG := hG) := fun l c_l => by
  wp_start as #Hl
  unfold isListener
  icases Hl with ⟨#Hpkg, #Hl⟩
  wp_apply wp_load $$ Hl with _
  wp_bind (ExternalOp _ _ _)
  wp_apply wp_AcceptOp with %c_r _
  iapply wp_fupd
  wp_apply wp_alloc_untyped _ (by simp [val.isPanic]) with %c Hc
  ipersist Hc
  imodintro
  iapply HΦ
  unfold isConnection
  iframe Hc Hpkg

end proof

end Perennial
