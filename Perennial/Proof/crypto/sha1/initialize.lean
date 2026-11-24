/-
The proof of `crypto/sha1.initialize'`.
-/
module

public import Perennial.Spec.crypto.sha1.initialize
public import Perennial.Spec.crypto.internal.boring.initialize
public import Perennial.Spec.crypto.internal.fips140only.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.hash.initialize
public import Perennial.Spec.internal.byteorder.initialize
public import Perennial.Spec.math.bits.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

theorem crypto.sha1.initialize'.wp_proof
    (wp_boring_initialize : crypto.internal.boring.initialize'.spec (GF := GF) (hG := hG))
    (wp_fips140only_initialize : crypto.internal.fips140only.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_hash_initialize : hash.initialize'.spec (GF := GF) (hG := hG))
    (wp_byteorder_initialize : internal.byteorder.initialize'.spec (GF := GF) (hG := hG))
    (wp_bits_initialize : math.bits.initialize'.spec (GF := GF) (hG := hG)) :
    crypto.sha1.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_bits_initialize _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hbits⟩
  wp_apply wp_byteorder_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hbyteorder⟩
  wp_apply wp_hash_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hhash⟩
  wp_apply wp_errors_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_fips140only_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hfips⟩
  wp_apply wp_boring_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hboring⟩
  -- `init`: the trusted no-op (TrustedCode/crypto/sha1.lean)
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
