/-
The proof of `internal.stringslite.HasPrefix`.
-/
module

public import Perennial.Spec.internal.stringslite.HasPrefix
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

theorem internal.stringslite.HasPrefix.wp_proof :
    internal.stringslite.HasPrefix.spec (GF := GF) (hG := hG) := fun s pfx => by
  wp_start
  wp_auto
  -- the Go variable `prefix` is a keyword in cases patterns
  irename «prefix» => Hpfx
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    wp_auto
    rw [show sint.nat (W64 pfx.length) - 0 = pfx.length by word, List.drop_zero]
    have H := internal.bytealg.slice_eq_iff_occ s pfx 0
    rw [List.drop_zero] at H
    rw [show decide (s.take pfx.length = pfx) = decide (pfx <+: s) from decide_eq_decide.2 H]
    iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => by have := h.length_le; word)]
    iapply HΦ; itrivial

end proof

end Perennial
