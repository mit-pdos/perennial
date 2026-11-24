/-
The proof of `fmt.newPrinter`.
-/
module

public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.fmt__init
public import Perennial.Proof.fmt.InitLemmas
public import Perennial.Spec.sync.Pool__Get

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

theorem fmt.newPrinter.wp_proof
    (wp_Get : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (wp_init : fmt.fmt.init.spec (GF := GF) (hG := hG)) :
    fmt.newPrinter.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave ⟨%f, %hf, #Hpool⟩ := fmt.isPkgInit_ppFree $$ Hpkg
  wp_auto
  wp_apply wp_Get $$ [] as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | %hnil)
  rotate_left
  · exact absurd hnil.1 hf
  unfold fmt.ppFreeElem
  icases Hx with ⟨%l, %v, %hx, Hl, Hbuf, Hbcap, Hw, Hwcap⟩
  subst hx
  ihave %hnn := typedPointsto_not_null $$ Hl
  iStructNamed Hl
  ihave %hfnn := typedPointsto_not_null $$ fmt
  wp_auto
  wp_apply wp_init $$ fmt as ⟨Hfmt, Hib⟩
  iapply HΦ
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
  isplitr
  · ipureintro; exact ⟨hnn, hfnn⟩
  iexists noFlags, W64 0, W64 0, v.arg'
  iframe

end proof

end Perennial
