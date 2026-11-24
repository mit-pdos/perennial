/-
The proof of `crypto/internal/fips140only.initialize'`.
-/
module

public import Perennial.Spec.crypto.internal.fips140only.initialize
public import Perennial.Spec.crypto.fips140.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.fips140only.Assumptions]

theorem crypto.internal.fips140only.initialize'.wp_proof
    (wp_fips140_initialize : crypto.fips140.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.internal.fips140only.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_fips140_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hf⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
