/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.Connect`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.Connect

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

theorem github_com.mit_pdos.gokv.grove_ffi.Connect.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.Connect.spec (GF := GF) (hG := hG) := fun c_r Hc_r => by
  wp_start
  wp_bind (ExternalOp _ _ _)
  wp_apply wp_ConnectOp c_r Hc_r with %err %c_l Hc
  rw [named_ConnectRet, named_Connection]
  cases err
  · iapply wp_fupd
    wp_auto
    wp_apply wp_alloc_untyped _ (by simp [val.isPanic]) with %c Hconn
    ipersist Hconn
    imodintro
    iapply HΦ $$ %false %c
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists c_l
    unfold isConnection
    iframe Hc Hconn Hpkg
  · wp_auto
    iapply HΦ $$ %true %null
    simp only [↓reduceIte]
    ipureintro; trivial

end proof

end Perennial
