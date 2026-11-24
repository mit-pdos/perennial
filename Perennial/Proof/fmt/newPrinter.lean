/-
The proof of `fmt.newPrinter`.
-/
module

public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.fmt__init
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
  have hacc : isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢ fmt.isInit (GF := GF) := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.fmt
  ihave #Hi := hacc $$ Hpkg
  unfold fmt.isInit
  icases Hi with ⟨%f, %hf, #Hpool⟩
  wp_auto
  wp_apply wp_Get $$ [] as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | %hnil)
  rotate_left
  · exact absurd hnil.1 hf
  unfold fmt.ppFreeElem
  icases Hx with ⟨%l, %v, %hx, Hl, Hbuf, Hbcap, Hw, Hwcap⟩
  subst hx
  iStructNamed Hl
  wp_auto
  wp_apply wp_init $$ fmt as ⟨Hfmt, Hib⟩
  iapply HΦ
  iexists v.arg'
  unfold fmt.isPrinterA fmt.bufferOwn
  iframe

end proof

end Perennial
