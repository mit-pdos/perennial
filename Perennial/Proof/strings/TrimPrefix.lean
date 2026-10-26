/-
The proof of `strings.TrimPrefix`.
-/
module

public import Perennial.Spec.strings.TrimPrefix
public import Perennial.Spec.strings.HasPrefix
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

/-- Proved from the model of `TrimPrefix` (`Perennial/TrustedCode/strings.lean`). -/
theorem strings.TrimPrefix.wp_proof
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    strings.TrimPrefix.spec (GF := GF) (hG := hG) := by
  intro s pfx
  wp_start as #Hinit
  wp_auto
  -- the model calls `HasPrefix` by its name (the trusted code is below `Code.strings`)
  rw [show (go!"strings.HasPrefix" : GoString) = HasPrefix from rfl]
  wp_apply wp_HasPrefix
  unfold trimPrefix
  by_cases h : pfx <+: s
  · simp only [h, decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, Hcap⟩
    ihave %Hlen := ownSlice_len $$ Hsl
    ihave %Hwf := ownSlice_wf $$ Hsl
    have Hp : pfx.length ≤ s.length := h.length_le
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp'
    have Hk : 0 ≤ sint.Z (W64 pfx.length) ∧ sint.Z (W64 pfx.length) ≤ sint.Z sl.len := by word
    rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
    icases (ownSlice_split_all (W64 pfx.length) sl _ s Hk).1 $$ Hsl with ⟨-, Hsl⟩
    rw [show sint.nat (W64 pfx.length) = pfx.length by word]
    wp_apply wp_bytes_to_string $$ Hsl as -
    iapply HΦ; itrivial
  · simp only [h, decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
