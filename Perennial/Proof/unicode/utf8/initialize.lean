/-
The proof of `unicode.utf8.initialize'`.
-/
module

public import Perennial.Spec.unicode.utf8.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

/-- `acceptRanges`' literal: the keyed entries over the zero value. -/
theorem unicode.utf8.acceptRangesVal_eq :
    unicode.utf8.acceptRangesVal = array.mk 16
      ((((((List.replicate 16 (zero_val unicode.utf8.acceptRange)).set 0 ⟨W8 128, W8 191⟩).set 1
        ⟨W8 160, W8 191⟩).set 2 ⟨W8 128, W8 159⟩).set 3 ⟨W8 144, W8 191⟩).set 4
        ⟨W8 128, W8 143⟩) := by
  rfl

set_option maxRecDepth 100000 in
theorem unicode.utf8.initialize'.wp_proof :
    unicode.utf8.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  -- the stores of the tables end the initializer: keep an update to make their cells persistent
  -- afterwards
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoArray acceptRange 16) acceptRanges
    (go.ArrayType 16 acceptRange.ty) with H2
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) first (go.ArrayType 256 go.uint8) with H1
  ipersist H1
  ipersist H2
  iframe Hown
  is_pkg_init_finish
  isplitr
  · itrivial
  imodintro
  isplitl []
  · imodintro; itrivial
  imodintro
  rw [unicode.utf8.isInit, unicode.utf8.acceptRangesVal_eq]
  unfold unicode.utf8.firstVal
  isplitl [H1]
  · iexact H1
  · iexact H2
