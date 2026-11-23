/-
The proof of `crypto.initialize'`.
-/
module

public import Perennial.Spec.crypto.initialize
public import Perennial.Spec.hash.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Spec.strconv.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem crypto.initialize'.wp_proof
    (wp_hash_initialize : hash.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_strconv_initialize : strconv.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) _ (go.SliceType _) as _
  wp_apply wp_GlobalAlloc (V := GoSlice) _ (go.SliceType _) as _
  wp_apply wp_strconv_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hstrconv⟩
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_hash_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hhash⟩
  wp_apply wp_slice_literal (V := w8) (t := go.uint8) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨_, _⟩
  wp_auto
  wp_apply wp_slice_make2 (V := GoFunc) as %sl ⟨_, _⟩
  · ipureintro; decide
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
