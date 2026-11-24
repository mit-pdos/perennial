/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.Send`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.Send
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

theorem github_com.mit_pdos.gokv.grove_ffi.Send.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.Send.spec (GF := GF) (hG := hG) := fun c c_l c_r s data dq => by
  iintro %Φ #Hc Hs HAU
  wp_func_call
  unfold Send.impl
  wp_pures
  unfold isConnection
  icases Hc with ⟨-, #Hc⟩
  wp_apply wp_load $$ Hc with _
  try wp_pures
  wp_apply wp_bytes_to_string s data dq $$ Hs with Hs
  try wp_pures
  iapply wp_SendOp_atomic c_l c_r data
  imod HAU with ⟨%ms, Hm, Hclose⟩
  imodintro
  iexists ms
  iframe Hm
  iintro Hm
  imod Hclose $$ Hm with HΦ
  imodintro
  iintro %b
  iapply HΦ $$ %b Hs

end proof

end Perennial
