/-
The proof of `internal.stringslite.Clone`.
-/
module

public import Perennial.Spec.internal.stringslite.Clone
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

theorem internal.stringslite.Clone.wp_proof :
    internal.stringslite.Clone.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  wp_if_destruct
  · have hs : s = [] := List.length_eq_zero_iff.mp (by word)
    subst hs
    iapply HΦ; itrivial
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_apply wp_slice_make2 (V := w8) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; word
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_copy (V := w8) $$ [Hb Hsl] as %n ⟨%Hn, Hb, -⟩
  · iframe
  wp_auto
  have e : s.take (List.replicate (sint.nat (W64 s.length)) (zero_val w8)).length ++
      (List.replicate (sint.nat (W64 s.length)) (zero_val w8)).drop s.length = s := by
    rw [List.length_replicate, show sint.nat (W64 s.length) = s.length by word,
      List.take_length, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
  rw [e]
  wp_apply wp_bytes_to_string $$ Hb as -
  iapply HΦ; itrivial

end proof

end Perennial
