/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.Receive`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.Receive
public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.AtomicOps

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

theorem github_com.mit_pdos.gokv.grove_ffi.Receive.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.Receive.spec (GF := GF) (hG := hG) := fun c c_l c_r => by
  iintro %Φ #Hc HAU
  wp_func_call
  unfold Receive.impl
  wp_pures
  unfold isConnection
  icases Hc with ⟨-, #Hc⟩
  wp_apply wp_load $$ Hc with _
  try wp_pures
  wp_bind (ExternalOp _ _ _)
  iapply wp_RecvOp_atomic c_l c_r
  imod HAU with ⟨%ms, Hm, Hclose⟩
  imodintro
  iexists ms
  iframe Hm
  iintro Hm
  imod Hclose $$ Hm with HΦ
  imodintro
  iintro %err %data %Hdata
  rw [named_ReceiveRet]
  cases err
  · wp_auto
    wp_apply wp_string_to_bytes data with %s ⟨Hs, Hcap⟩
    iapply HΦ $$ %false %s
    simp only [Bool.false_eq_true, ↓reduceIte] at Hdata ⊢
    iexists data
    iframe Hs Hcap
    ipureintro; exact Hdata
  · wp_auto
    iapply HΦ $$ %true %slice.nil
    simp only [↓reduceIte]
    ipureintro; trivial

end proof

end Perennial
