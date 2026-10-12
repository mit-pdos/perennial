/-
The proof of `strings.initialize'`.
-/
module

public import Perennial.Spec.strings.initialize
public import Perennial.Spec.internal.stringslite.initialize
public import Perennial.Spec.«unsafe».initialize
public import Perennial.Spec.unicode.utf8.initialize
public import Perennial.Spec.internal.bytealg.initialize
public import Perennial.Spec.internal.abi.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.initialize'.wp_proof
    (wp_stringslite_initialize : internal.stringslite.initialize'.spec (GF := GF) (hG := hG))
    (wp_unsafe_initialize : «unsafe».initialize'.spec (GF := GF) (hG := hG))
    (wp_utf8_initialize : unicode.utf8.initialize'.spec (GF := GF) (hG := hG))
    (wp_bytealg_initialize : internal.bytealg.initialize'.spec (GF := GF) (hG := hG))
    (wp_abi_initialize : internal.abi.initialize'.spec (GF := GF) (hG := hG)) :
    strings.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) with H
  wp_apply wp_stringslite_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hstringslite⟩
  wp_apply wp_unsafe_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hunsafe⟩
  wp_apply wp_utf8_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hutf8⟩
  wp_apply wp_bytealg_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hbytealg⟩
  wp_apply wp_abi_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Habi⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
