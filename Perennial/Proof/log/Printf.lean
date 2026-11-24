/-
The proof of `log.Printf` (its Go model, `goose/model/overlay/log`): `fmt.Fprintf` into the model's
`modelDiscard`, or nothing.
-/
module

public import Perennial.Spec.log.Printf
public import Perennial.Spec.log.modelDiscard__Write
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.fmt.Fprintf
public import Perennial.Proof.fmt.Args

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.Printf.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_Fprintf : fmt.Fprintf.spec (GF := GF) (hG := hG))
    (wp_Write : log.modelDiscard.Write.spec (GF := GF) (hG := hG)) :
    log.Printf.spec (GF := GF) (hG := hG) := by
  intro msg arg xs dq Hxs
  wp_start as Hsl
  wp_auto
  wp_apply wp_Choose as %c -
  cases c
  · wp_auto
    iapply HΦ
    iexact Hsl
  · wp_auto
    wp_apply (wp_Fprintf _ msg arg xs dq iprop(True) (fun _ _ _ => iprop(True))) $$ [Hsl]
      as %n %err ⟨Hsl, -⟩
    · iframe
      isplitr
      · iapply (fmt.argsOk_of_argsWf Hxs)
      isplitr
      · itrivial
      iexists _
      isplitr
      · ipureintro; rfl
      unfold fmt.writeSpec
      iintro %sl %s %Φ' - Hs HΦ'
      iapply wp_Write _ sl s (DFrac.own 1) $$ Hs
      inext
      iintro Hs
      iapply HΦ' $$ Hs
      itrivial
    wp_auto
    iapply HΦ
    iexact Hsl

end proof

end Perennial
