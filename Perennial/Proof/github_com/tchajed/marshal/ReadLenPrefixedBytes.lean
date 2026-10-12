/-
The proof of `github.com/tchajed/marshal.ReadLenPrefixedBytes`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.ReadLenPrefixedBytes
public import Perennial.Spec.github_com.tchajed.marshal.ReadInt
public import Perennial.Spec.github_com.tchajed.marshal.ReadBytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.ReadLenPrefixedBytes.wp_proof
    (wp_ReadInt : github_com.tchajed.marshal.ReadInt.spec (GF := GF) (hG := hG))
    (wp_ReadBytes : github_com.tchajed.marshal.ReadBytes.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.ReadLenPrefixedBytes.spec (GF := GF) (hG := hG) := fun s q len head tail Hlen => by
  wp_start as Hs
  wp_auto
  rw [List.append_assoc]
  wp_apply wp_ReadInt (head ++ tail) s q len $$ [$Hs] as %s1 Hs
  wp_apply wp_ReadBytes s1 q len head tail Hlen $$ [$Hs] as %b %s2 ⟨Hb, Hs⟩
  iapply HΦ
  iframe

end proof

end Perennial
