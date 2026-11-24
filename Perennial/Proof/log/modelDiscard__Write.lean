/-
The proof of `log.modelDiscard.Write` (an addition of the Go model of `log`).
-/
module

public import Perennial.Spec.log.modelDiscard__Write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.modelDiscard.Write.wp_proof :
    log.modelDiscard.Write.spec (GF := GF) (hG := hG) := by
  intro d sl bs dq
  wp_start as Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  rw [show sl.len = W64 (bs.length : Int) by word]
  iapply HΦ
  iexact Hsl

end proof

end Perennial
