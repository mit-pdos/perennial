/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.FileWrite`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileWrite
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

theorem github_com.mit_pdos.gokv.grove_ffi.FileWrite.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.FileWrite.spec (GF := GF) (hG := hG) := fun f s dq data => by
  iintro %Φ Hs HAU
  wp_func_call
  unfold FileWrite.impl
  wp_pures
  wp_apply wp_bytes_to_string s data dq $$ Hs with Hs
  try wp_pures
  iapply wp_FileWriteOp_atomic f data
  imod HAU with ⟨%old, Hf, Hclose⟩
  imodintro
  iexists old
  iframe Hf
  iintro Hf
  imod Hclose $$ Hf with HΦ
  imodintro
  iapply HΦ $$ Hs

end proof

end Perennial
