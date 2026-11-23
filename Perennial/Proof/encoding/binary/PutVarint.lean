/-
The proof of `encoding/binary.PutVarint`.
-/
module

public import Perennial.Spec.encoding.binary.PutVarint
public import Perennial.Spec.encoding.binary.PutUvarint

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
theorem encoding.binary.PutVarint.wp_proof
    (wp_PutUvarint : encoding.binary.PutUvarint.spec (GF := GF) (hG := hG)) :
    encoding.binary.PutVarint.spec (GF := GF) (hG := hG) := fun buf xs x hn => by
  wp_start as Hb
  wp_auto
  wp_if_destruct
  · -- `x < 0`: `ux = ^(uint64(x) << 1)`
    have hz := zigzag_go x
    simp only [show sint.Z x < 0 by word, ↓reduceIte] at hz
    rw [← hz] at hn ⊢
    wp_apply wp_PutUvarint buf xs _ hn $$ [$Hb] as Hb
    iapply HΦ $$ Hb
  · have hz := zigzag_go x
    simp only [show ¬ sint.Z x < 0 by word, ↓reduceIte] at hz
    rw [← hz] at hn ⊢
    wp_apply wp_PutUvarint buf xs _ hn $$ [$Hb] as Hb
    iapply HΦ $$ Hb

end proof

end Perennial
