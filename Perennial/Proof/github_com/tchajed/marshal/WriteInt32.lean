/-
The proof of `github.com/tchajed/marshal.WriteInt32`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.WriteInt32
public import Perennial.Spec.github_com.tchajed.marshal.reserve
public import Perennial.Spec.encoding.binary.littleEndian__PutUint32
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.WriteInt32.wp_proof
    (wp_reserve : github_com.tchajed.marshal.reserve.spec (GF := GF) (hG := hG))
    (wp_littleEndian_PutUint32 : encoding.binary.littleEndian.PutUint32.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.WriteInt32.spec (GF := GF) (hG := hG) := fun s x vs Hbound => by
  wp_start as ⟨Hs, Hcap⟩
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_reserve s (W64 4) vs Hbound $$ [$Hs $Hcap] as %s2 ⟨%Hroom, Hs, Hcap⟩
  ihave %Hsz := ownSlice_len _ _ _ $$ Hs
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  have hr := room4 _ _ Hroom Hcapwf
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega, hr.2⟩)]
  icases ownSlice_slice_into_capacity (W64 0) (s2.len + W64 4) s2 vs $$ [Hs Hcap] with
    ⟨%vs_cap, -, Hb3, Hb3cap⟩
  · iframe; ipureintro; omega
  simp only [List.drop_zero, show sint.nat (W64 0) = 0 from rfl] at *
  generalize hB : slice.slice s2 w8 (W64 0) (s2.len + W64 4) = B
  ihave %HBwf := ownSliceCap_wf _ _ $$ Hb3cap
  ihave %Hb3len := ownSlice_len _ _ _ $$ Hb3
  have hBlen : B.len = s2.len + W64 4 := by
    rw [← hB]; show s2.len + W64 4 - W64 0 = _; simp
  rw [hBlen, hr.1] at Hb3len
  rw [hBlen] at HBwf
  have hvc : vs_cap.length = 4 := by
    have h1 := hr.1; simp only [List.length_append, sint.nat, sint.Z] at *; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hcapwf.1, by rw [hBlen]; omega, by rw [hBlen]; exact HBwf.2⟩)]
  icases ownSlice_split_app s2.len B (DFrac.own 1) vs vs_cap Hsz.1.symm Hcapwf.1
    (by rw [hBlen]; simp only [List.length_append, sint.nat] at *; omega)
    (by rw [hBlen]; omega) $$ Hb3 with ⟨H0, Hput⟩
  rw [← List.append_nil vs_cap]
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_PutUint32_of wp_littleEndian_PutUint32 _ vs_cap [] x hvc $$ [$Hput]
    as Hput
  iapply HΦ
  iframe Hb3cap
  iapply (ownSlice_trivial_slice B _ _).2
  iapply ownSlice_combine s2.len B (DFrac.own 1) vs (u32Le x) (W64 0) B.len
    ⟨by rw [Hsz.1]; simp only [sint.nat, show (W64 0).toInt = 0 from rfl]; omega, by decide, Hcapwf.1, by rw [hBlen]; omega⟩
    $$ H0
  rw [List.append_nil]
  iexact Hput

end proof

end Perennial
