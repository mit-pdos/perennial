/-
The proof of `MultiReader`.
-/
module

public import Perennial.Spec.io.MultiReader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem io.MultiReader.wp_proof :
    io.MultiReader.spec (GF := GF) (hG := hG) :=
  fun sl dq cs eof => by
  wp_start as ⟨Hsl, HS⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_apply wp_slice_make2 (V := GoInterface) $$ [] as %b ⟨Hb, -⟩
  · ipureintro; exact Hlen.2
  wp_apply wp_slice_copy (V := GoInterface) $$ [Hb Hsl] as %n ⟨%Hn, Hb, Hsl⟩
  · iframe
  have e : (List.replicate (sint.nat sl.len) (zero_val GoInterface)).length =
      (List.map io.ReaderC.iface cs).length := by simp [Hlen.1]
  have e2 : List.drop (List.map io.ReaderC.iface cs).length
      (List.replicate (sint.nat sl.len) (zero_val GoInterface)) = [] := by
    rw [← e]; exact List.drop_length
  rw [e, List.take_length, e2, List.append_nil]
  wp_auto
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iframe Hsl
  unfold io.mrState
  iexists [], cs, b, []
  iframe Hl Hb
  isplitr
  · ipureintro; simp
  isplitr
  · iapply io.mrDone_nil
  iapply io.mrCur_init $$ HS

end proof

end Perennial
