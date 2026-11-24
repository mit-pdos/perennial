/-
The proof of `crypto/fips140.initialize'`.
-/
module

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
variable [package_sem : crypto.fips140.Assumptions]

theorem crypto.fips140.initialize'.wp_proof :
    crypto.fips140.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  -- `enabled`: its trusted initializer allocates it and stores the read of the setting
  wp_call
  wp_apply_core wp_GlobalAlloc (V := Bool) _ go.bool
  iintro He
  wp_pures
  wp_apply wp_ArbitraryInt as %x -
  wp_join (Q := fun v => iprop(⌜∃ b : Bool, v = #b ∧ (b = true → godebugFips140 = go!"only")⌝))
    at (if: _ then _ else _) with []
  · wp_if_destruct
    · ipureintro; exact ⟨_, rfl, fun h => by simpa using h⟩
    · ipureintro; exact ⟨false, rfl, fun h => by cases h⟩
  iintro %Hv
  obtain ⟨b, hb, Hb⟩ := Hv
  subst hb
  wp_pures
  wp_store
  ipersist He
  wp_auto
  iframe Hown
  is_pkg_init_finish
  isplitr
  · itrivial
  imodintro
  unfold crypto.fips140.isInit crypto.fips140.enabled
  iexists _
  iframe He
  ipureintro
  exact Hb

end proof

end Perennial
