/-
The proof of `github.com/tchajed/marshal.ReadInt32`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.ReadInt32
public import Perennial.Spec.encoding.binary.littleEndian__Uint32
public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.ReadInt32.wp_proof
    (wp_littleEndian_Uint32 : encoding.binary.littleEndian.Uint32.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.ReadInt32.spec (GF := GF) (hG := hG) := fun tail s dq x => by
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint32_of wp_littleEndian_Uint32 s (u32Le x) dq tail
    (u32Le_length x) $$ [$Hs] as Hs
  rw [u32Le_to_word]
  simp only [List.length_append, u32Le_length] at Hlen
  have h4 : sint.Z (W64 4) = 4 := by decide
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    rw [h4]; simp only [sint.nat, sint.Z] at *; omega, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  icases ownSlice_split_app (W64 4) s dq (u32Le x) tail (by rw [u32Le_length]; decide)
    (by decide) (by simp [u32Le_length, Hlen]) Hwf.1 $$ Hs with ⟨_, Hs⟩
  iexact Hs

end proof

end Perennial
