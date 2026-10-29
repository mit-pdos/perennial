/-
The proof of `writeLeaf`: a leaf header over the first 16 bytes, then `writeInodeToPage`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.wp_proof
    (wp_pageAt : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.spec (GF := GF) (hG := hG))
    (wp_writeInodeToPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.spec (GF := GF) (hG := hG) := by
  intro buf s ms N
  wp_start as ⟨#Hin, Hb, %H⟩
  obtain ⟨Hlen, HN, Hfit, HR⟩ := H
  ihave %Hbd := bytesPointsto_bounds _ _ _ (by intro h; have := congrArg List.length h; simp at this; omega) $$ Hb
  simp only [List.length_replicate] at Hbd
  wp_auto
  have hNZ : sint.Z buf.len = N := by rw [Hlen]; exact sint_Z_W64_nat _ HN
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbd.1, by decide, ?_⟩; rw [hNZ, show sint.Z (W64 0) = 0 from rfl]; omega
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  rw [show List.replicate N (0 : w8) = List.replicate 16 0 ++ List.replicate (N - 16) 0 by
    rw [List.replicate_append_replicate]; congr 1; omega]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hb⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) Hbd.1).1 $$ Hh with Hh
  wp_auto
  unfold inodesOwn
  icases Hin with ⟨%xs, #Hs, #Hxs⟩
  ihave %Hl1 := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hs
  have hsZ : sint.Z s.len = ms.length := sint_Z_eq_of_sint_nat _ _ (Hl1 ▸ Hl2.1) Hl2.2
  ihave Hh := typedPointsto_of_eq _ _ (leafHeader ms) _ $$ [Hh]
  · iframe Hh
    ipureintro
    simp only [leafHeader, hsZ]
    rfl
  rw [List.length_replicate]
  wp_apply wp_writeInodeToPage s ms buf.ptr (leafHeader ms) (N - 16) $$ [Hh Hb] as %w ⟨Hh, Hb⟩
  · iframe Hh Hb
    isplitl
    · unfold inodesOwn; iexists xs; iframe Hs Hxs
    · ipureintro; refine ⟨Hbd.1, Hfit, by omega⟩
  have hleaf : pageIsLeaf (leafHeader ms) = true := by
    simp [pageIsLeaf, leafHeader]
  rw [hleaf]
  iapply HΦ
  icases (typedPointsto_bytes (V := Page) _ _ _ Hbd.1).1 $$ Hh with Hh
  rw [List.append_assoc]
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length, show N - 16 - (pageBody true ms).length =
    N - 16 - (pageBody true ms).length from rfl]
  iframe

end proof

end Perennial
