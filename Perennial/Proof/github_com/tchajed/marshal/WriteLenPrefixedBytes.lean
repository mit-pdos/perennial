/-
The proof of `github.com/tchajed/marshal.WriteLenPrefixedBytes`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.WriteLenPrefixedBytes
public import Perennial.Spec.github_com.tchajed.marshal.WriteInt
public import Perennial.Spec.github_com.tchajed.marshal.WriteBytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.WriteLenPrefixedBytes.wp_proof
    (wp_WriteInt : github_com.tchajed.marshal.WriteInt.spec (GF := GF) (hG := hG))
    (wp_WriteBytes : github_com.tchajed.marshal.WriteBytes.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.WriteLenPrefixedBytes.spec (GF := GF) (hG := hG) := fun s vs data_sl q data Hbound => by
  wp_start as ⟨Hs, Hdata, Hscap⟩
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hdata
  wp_auto
  wp_apply wp_WriteInt s data_sl.len vs Hbound $$ [$Hs $Hscap] as %s' ⟨Hs', Hscap⟩
  wp_apply wp_WriteBytes s' _ data_sl q data $$ [$Hs' $Hdata $Hscap] as %s'0 ⟨Hs, Hscap, Hdata⟩
  iapply HΦ
  have : W64 (data.length : Int) = data_sl.len := by
    rw [Hdlen.1]; simp only [sint.nat, W64]
    rw [Int.toNat_of_nonneg Hdlen.2]; exact BitVec.ofInt_toInt
  rw [this, List.append_assoc]
  iframe

end proof

end Perennial
