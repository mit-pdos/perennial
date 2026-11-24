/-
The proof of `fmt.Fprintf` (the Go model of `goose/model/overlay/fmt`): a printer from `newPrinter`,
the model printer's `doPrintf` (`Perennial/Proof/fmt/DoPrintf.lean`) into its buffer, the writer's
`writeSpec` lent the buffer, and `pp.free`.
-/
module

public import Perennial.Spec.fmt.Fprintf
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.buffer__writeString
public import Perennial.Spec.fmt.pp__free

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Fprintf.wp_proof
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    fmt.Fprintf.spec (GF := GF) (hG := hG) := by
  intro w format args_sl xs dq P Q
  wp_start as ⟨Hsl, Hok, HP, %ii, %Hw, HW⟩
  subst Hw
  wp_auto
  wp_apply wp_newPrinter as %p Hp
  have hdo := fmt.wp_doPrintf wp_ChooseUint64 format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hok] as %s %wsl %unk ⟨Hsl, %Hs, -⟩
  try wp_auto
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  wp_apply wp_writeString $$ Hb as Hb
  unfold fmt.bufferOwn
  icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
  iunfold fmt.writeSpec at HW
  iapply HW $$ HP Hbs
  inext
  iintro %n %err Hbs HQ
  wp_auto
  wp_apply wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
    isplitr
    · ipureintro; exact hnn
    iexists F, wid, prec, x'
    iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  exact Hs

end proof

end Perennial
