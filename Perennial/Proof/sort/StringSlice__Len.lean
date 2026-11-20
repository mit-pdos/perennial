/-
The proof of `sort.StringSlice.Len`.
-/
module

public import Perennial.Spec.sort.StringSlice__Len

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.StringSlice.Len.wp_proof :
    sort.StringSlice.Len.spec (GF := GF) (hG := hG) := by
  intro x xs dq
  wp_start as Hx
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hx
  rw [show x.len = W64 (xs.length : Int) by word]
  iapply HΦ; iexact Hx

end proof

end Perennial
