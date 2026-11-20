/-
The proof of `strings.initialize'`.
-/
module

public import Perennial.Spec.strings.initialize
public import Perennial.Spec.internal.stringslite.initialize
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.initialize'.wp_proof
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG)) :
    strings.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) with H
  wp_apply wp_stringslite_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsl⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
