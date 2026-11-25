/-
The proof of `log.Println` (its Go model, `goose/model/overlay/log`): `fmt.Fprintln` into the
model's `modelDiscard`, or nothing.
-/
module

public import Perennial.Spec.log.Println
public import Perennial.Spec.log.modelDiscard__Write
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.fmt.Fprintln

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

theorem log.Println.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_Fprintln : fmt.Fprintln.spec (GF := GF) (hG := hG))
    (wp_Write : log.modelDiscard.Write.spec (GF := GF) (hG := hG)) :
    log.Println.spec (GF := GF) (hG := hG) := by
  intro arg xs dq Hxs
  wp_start as Hsl
  wp_auto
  wp_apply wp_Choose as %c -
  cases c
  · wp_auto
    iapply HΦ
    iexact Hsl
  · wp_auto
    wp_apply (wp_Fprintln _ arg xs dq iprop(True) iprop(True) (fun _ _ _ => iprop(True))) $$ [Hsl]
      as %n %err ⟨Hsl, -, -⟩
    · iframe
      isplitr
      · iapply (fmt.printArgsOk_of_argsWf iprop(True) Hxs)
      isplitr
      · itrivial
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
    iapply HΦ
    iexact Hsl

end proof

end Perennial
