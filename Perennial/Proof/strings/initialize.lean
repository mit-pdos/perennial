/-
The proof of `strings.initialize'`.
-/
module

public import Perennial.Spec.strings.initialize
public import Perennial.Spec.internal.stringslite.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Spec.internal.abi.initialize
public import Perennial.Spec.internal.bytealg.initialize
public import Perennial.Spec.unicode.utf8.initialize
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
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_abi_initialize : internal.abi.initialize'.spec (GF := GF) (hG := hG))
    (wp_bytealg_initialize : internal.bytealg.initialize'.spec (GF := GF) (hG := hG))
    (wp_utf8_initialize : unicode.utf8.initialize'.spec (GF := GF) (hG := hG)) :
    strings.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) with H
  wp_apply wp_sync_initialize _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsy⟩
  wp_apply wp_io_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_stringslite_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hsl⟩
  wp_apply wp_utf8_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hu8⟩
  wp_apply wp_bytealg_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hba⟩
  wp_apply wp_abi_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Habi⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
