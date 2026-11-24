/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.FileRead`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileRead
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

theorem github_com.mit_pdos.gokv.grove_ffi.FileRead.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.FileRead.spec (GF := GF) (hG := hG) := fun f => by
  iintro %Φ HAU
  wp_func_call
  unfold FileRead.impl
  wp_pures
  wp_bind (ExternalOp _ _ _)
  iapply wp_FileReadOp_atomic
  imod HAU with ⟨%dq, %c, Hf, Hclose⟩
  imodintro
  iexists dq, c
  iframe Hf
  iintro Hf
  imod Hclose $$ Hf with HΦ
  imodintro
  wp_apply wp_string_to_bytes c with %s ⟨Hs, Hcap⟩
  iapply HΦ $$ Hs Hcap

end proof

end Perennial
