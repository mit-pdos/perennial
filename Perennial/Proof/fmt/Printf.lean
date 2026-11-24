/-
The proof of `fmt.Printf` (trusted, `Perennial/TrustedCode/fmt.lean`): the translated model
`printfFormat` (a printer from `newPrinter`, the model printer's `doPrintf`
(`Perennial/Proof/fmt/DoPrintf.lean`) appending to its buffer, and `pp.free`), then an arbitrary
count and either `nil` or an `errors.New` of an arbitrary string.
-/
module

public import Perennial.Spec.fmt.Printf
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.arbitraryString
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.buffer__writeString
public import Perennial.Spec.fmt.pp__free
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64

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

theorem fmt.Printf.wp_proof
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    fmt.Printf.spec (GF := GF) (hG := hG) := fun format args_sl xs dq => by
  wp_start as ⟨Hsl, Hok⟩
  -- `Printf.impl` (trusted) calls the translated model `printfFormat`
  try rw [show (go!"fmt.printfFormat" : GoString) = fmt.printfFormat from rfl]
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_newPrinter as %p Hp
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  have hdo := fmt.wp_doPrintf wp_Choose wp_ChooseUint64 wp_writeString (p.[fmt.pp, go!"buf"]) []
    format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hb $Hsl $Hok] as %wsl %unk ⟨%s, Hb, Hsl, -, -⟩
  try wp_auto
  wp_apply wp_free p ([] ++ s) $$ [Hb Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
    isplitr
    · ipureintro; exact hnn
    iexists F, wid, prec, x'
    iframe
  try wp_auto
  wp_apply wp_ArbitraryInt as %n -
  wp_apply wp_ArbitraryInt as %b -
  wp_if_destruct
  · iapply HΦ
    iframe
  · wp_apply fmt.wp_arbitraryString as %junk -
    wp_apply errors.wp_New_errorString_cell as %x -
    iapply HΦ
    iframe

end proof

end Perennial
