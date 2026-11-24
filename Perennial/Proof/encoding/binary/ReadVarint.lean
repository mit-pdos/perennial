/-
The proof of `encoding/binary.ReadVarint`.
-/
module

public import Perennial.Spec.encoding.binary.ReadVarint
public import Perennial.Spec.encoding.binary.ReadUvarint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open encoding.binary in
theorem encoding.binary.ReadVarint.wp_proof
    (wp_ReadUvarint : encoding.binary.ReadUvarint.spec (GF := GF) (hG := hG)) :
    encoding.binary.ReadVarint.spec (GF := GF) (hG := hG) := fun ri S E r0 eof ueof ovf => by
  wp_start as ⟨#Hr, #Heof, #Hueof, #Hovf, HS⟩
  wp_auto
  wp_apply wp_ReadUvarint ri S E r0 eof ueof ovf $$ [$Hpkg2 $Hr $Heof $Hueof $Hovf $HS]
    as %ux %err ⟨%V, HS, #Hres⟩
  try wp_auto
  simp only [← decide_not]
  wp_if_destruct
  · -- `ux&1 != 0`: `x = ^x`
    try wp_auto
    iapply HΦ
    iexists V, ux
    iframe HS Hres
    ipureintro
    rw [ite_eq_right Hif]
  · try wp_auto
    iapply HΦ
    iexists V, ux
    iframe HS Hres
    ipureintro
    rw [ite_eq_left (by simpa using Hif)]

end proof

end Perennial
