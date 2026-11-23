/-
The proof of `crypto/internal/boring.initialize'`.
-/
module

public import Perennial.Spec.crypto.internal.boring.initialize
public import Perennial.Spec.crypto.internal.boring.sig.initialize
public import Perennial.Spec.hash.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.Assumptions]

theorem crypto.internal.boring.initialize'.wp_proof
    (wp_sig_initialize : crypto.internal.boring.sig.initialize'.spec (GF := GF) (hG := hG))
    (wp_hash_initialize : hash.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.internal.boring.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_hash_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hhash⟩
  wp_apply wp_sig_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsig⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
