/-
The proof of `fmt.Sprintf`.
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.pp__doPrintf
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

theorem fmt.Sprintf.wp_proof
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_doPrintf : fmt.pp.doPrintf.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG)) :
    fmt.Sprintf.spec (GF := GF) (hG := hG) := fun format ps args_sl xs args dq hf hfits => by
  wp_start as ⟨Hsl, Hargs⟩
  wp_auto
  wp_apply wp_newPrinter as %p ⟨%x, Hp⟩
  wp_apply wp_doPrintf p [] format ps args_sl xs args dq hf hfits $$ [Hp Hsl Hargs]
    as ⟨%out, %hout, Hp, Hsl, Hargs⟩
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter
    iexists noFlags, W64 0, W64 0, x
    iexact Hp
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
  icases Hp with ⟨%F, %wid, %prec, %x', ⟨%sl, Hb, Hbs, Hcap⟩, Hrest⟩
  wp_auto
  wp_apply wp_bytes_to_string sl ([] ++ out) (DFrac.own 1) $$ Hbs as Hbs
  wp_apply wp_free p ([] ++ out) $$ [Hb Hbs Hcap Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
    iexists F, wid, prec, x'
    iframe
  iapply HΦ
  iframe
  ipureintro
  simpa using hout

end proof

end Perennial
