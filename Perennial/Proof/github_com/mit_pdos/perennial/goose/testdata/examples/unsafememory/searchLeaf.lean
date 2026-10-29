/-
The proof of `searchLeaf`: a binary search whose bounds stay around the number of smaller keys.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.searchLeaf
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElements
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__key
public import Perennial.Spec.bytes.Compare

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.searchLeaf.wp_proof
    (wp_leafPageElements : Page.leafPageElements.spec (GF := GF) (hG := hG))
    (wp_leafKey : leafPageElement.key.spec (GF := GF) (hG := hG))
    (wp_Compare : bytes.Compare.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.searchLeaf.spec (GF := GF) (hG := hG) := by
  intro p hdr ms tail key k dk r
  wp_start as ⟨#Hp, #Hb, Hk, %H⟩
  obtain ⟨Hpos, Hcount, ⟨Hn16, Hfit, Hkeys⟩, Hr, Hlt⟩ := H
  have hnn : p ≠ null := by intro h; subst h; simp [null] at Hpos
  have hcZ : uint.Z hdr.count' = ms.length := by
    rw [Hcount]; simp only [uint.Z]; word
  ihave %Hbd := bytesPointsto_bounds_imp _ _ _ $$ Hb
  icases (typedPointsto_bytes (V := Page) _ _ _ Hpos).1 $$ Hp with Hpb
  ihave %Hpbd := bytesPointsto_bounds _ _ _ (ByteEncoding.encode_ne_nil hdr (by decide)) $$ Hpb
  rw [ByteEncoding.encode_length] at Hpbd
  have hbody := pageBody_length true ms
  wp_auto
  wp_apply wp_leafPageElements $$ [] as -
  · iframe Hp; ipureintro; refine ⟨Hpos, ?_⟩; rw [hcZ]
    by_cases hn0 : ms.length = 0
    · simp only [hn0]; omega
    · have := (Hbd (by intro h; have := congrArg List.length h; simp [hbody] at this; omega)).2
      simp only [Loc.add, List.length_append] at this; omega
  have hn0 : (hdr.count' = W16 0) ↔ ms.length = 0 := by
    constructor
    · intro h; have := hcZ; rw [h] at this; simp [uint.Z] at this; omega
    · intro h; rw [Hcount, h]; rfl
  generalize hes : (if hdr.count' = W16 0 then slice.nil
    else slice.mk (p +ₗ 16) (W64 (uint.Z hdr.count')) (W64 (uint.Z hdr.count'))) = es
  have hesLen : sint.Z es.len = ms.length := by
    rw [← hes]
    split
    · rename_i h; rw [hn0.1 h]; rfl
    · rw [hcZ]; exact sint_Z_W64_nat _ (by omega)
  have hesPtr : 0 < ms.length → es = slice.mk (p +ₗ 16) (W64 (ms.length : Int)) (W64 (ms.length : Int)) := by
    intro h; rw [← hes, if_neg (fun h' => by have := hn0.1 h'; omega), hcZ]
  ihave HI : (∃ lo hi : w64,
      "lo" ∷ lo_ptr ↦ lo ∗
      "hi" ∷ hi_ptr ↦ hi ∗
      "HΦ" ∷ (key ↦*{dk} k -∗ Φ #(W64 (r : Int))) ∗
      "Hk" ∷ key ↦*{dk} k ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val w64 ∗
      "key" ∷ key_ptr ↦ key ∗
      "elems" ∷ elems_ptr ↦ es ∗
      "%Hlh" ∷ ⌜0 ≤ sint.Z lo ∧ sint.Z lo ≤ r ∧ r ≤ sint.Z hi ∧ sint.Z hi ≤ ms.length⌝ : IProp GF)
      $$ [lo hi HΦ Hk «$res0» key elems]
  · iexists (W64 0), es.len
    iframe
    ipureintro; rw [hesLen]; exact ⟨by decide, by simp, by omega, by omega⟩
  wp_for HI
  have hlt : sint.Z lo = lo.toInt := rfl
  have hht : sint.Z hi = hi.toInt := rfl
  wp_if_destruct
  · -- an iteration
    have hloW : lo = W64 ((sint.nat lo : Nat) : Int) := w64_of_sint_nat _ _ rfl Hlh.1
    have hhiW : hi = W64 ((sint.nat hi : Nat) : Int) := w64_of_sint_nat _ _ rfl (by omega)
    have hloN : sint.Z lo = (sint.nat lo : Int) := by simp only [sint.nat]; omega
    have hhiN : sint.Z hi = (sint.nat hi : Int) := by simp only [sint.nat]; omega
    have hmid := mid_eq (sint.nat lo) (sint.nat hi) (by omega) (by omega)
    rw [← hloW, ← hhiW] at hmid
    rw [hmid]
    generalize hmN : sint.nat lo + (sint.nat hi - sint.nat lo) / 2 = mN at *
    have hmZ : sint.Z (W64 (mN : Int)) = mN := sint_Z_W64_nat _ (by omega)
    have hmlt : mN < ms.length := by omega
    have hmpos : 0 < ms.length := by omega
    rw [hmZ, hesLen, hesPtr hmpos]
    simp only [show 0 ≤ (mN : Int) ∧ (mN : Int) < ms.length from ⟨by omega, by omega⟩,
      _root_.and_self, ↓reduceIte]
    have hidx : sliceIndexRef leafPageElement (mN : Int)
        (slice.mk (p +ₗ 16) (W64 (ms.length : Int)) (W64 (ms.length : Int))) =
        p +ₗ (16 + 16 * (mN : Int)) := by
      simp only [sliceIndexRef]
      rw [arrayIndexRef_plain_eq _ leafPageElement.layout _ _ (by simp only [Loc.add]; omega)
        (by omega), loc_add_assoc]
      congr 1; omega
    rw [hidx]
    obtain ⟨m, hm⟩ : ∃ m, ms[mN]? = some m := ⟨_, List.getElem?_eq_getElem hmlt⟩
    have hle := dataOff_le' ms mN m hm
    have hge := dataOff_ge ms mN
    have hb := (Hbd (by
      intro h; have := congrArg List.length h; simp [hbody] at this; omega)).2
    simp only [Loc.add, List.length_append] at hb
    have hlt' : mN < (leafElems ms).length := by rw [leafElems_length]; exact hmlt
    have he := pageBody_leaf_elem ms tail mN hmlt
    ihave He := bytesPointsto_sub (p +ₗ 16) (pageBody true ms ++ tail)
      (encode ((leafElems ms)[mN]'hlt')) (16 * mN)
      (by rw [ByteEncoding.encode_length, List.length_append, hbody]; omega)
      (by rw [ByteEncoding.encode_length]; exact he) $$ Hb
    icases (bytesPointsto_typed (V := leafPageElement)
      ((p +ₗ 16) +ₗ ((16 * mN : Nat) : Int)) DFrac.discard _ (ByteEncoding.encode_length _)
      (by simp only [Loc.add]; omega)).1 $$ He with He
    rw [ByteEncoding.decode_encode, leafElems_getElem' ms mN m hm hlt', loc_add_assoc,
      show (16 : Int) + ((16 * mN : Nat) : Int) = 16 + 16 * (mN : Int) by omega] at *
    have hpos : uint.Z (W32 ((dataOff ms mN - (16 + 16 * mN) : Nat) : Int)) =
        ((dataOff ms mN - (16 + 16 * mN) : Nat) : Int) := by
      simp only [uint.Z]; word
    have hkz : uint.Z (W32 (m.key.length : Int)) = m.key.length := by simp only [uint.Z]; word
    have haddr : p +ₗ (16 + 16 * (mN : Int)) +ₗ (((dataOff ms mN - (16 + 16 * mN) : Nat) : Int)) =
        p +ₗ (dataOff ms mN : Int) := by
      rw [loc_add_assoc]; congr 1; omega
    wp_apply wp_leafKey $$ [He] as -
    · iframe He; ipureintro; simp only [hpos, hkz, Loc.add]; omega
    simp only [hpos, hkz, haddr]
    ihave Hkm := bytesPointsto_sub (p +ₗ 16) (pageBody true ms ++ tail) m.key
      (dataOff ms mN - 16) (by rw [List.length_append, hbody]; omega)
      (pageBody_key true ms tail _ m hm) $$ Hb
    rw [loc_add_assoc, show (16 : Int) + ((dataOff ms mN - 16 : Nat) : Int) =
      (dataOff ms mN : Int) by omega]
    icases (bytesPointsto_ownSlice _ _ _ (by simp only [Loc.add]; omega) (by omega)).1 $$ Hkm
      with Hkm
    wp_apply (wp_Compare _ key DFrac.discard dk m.key k) $$ [Hk] as ⟨-, Hk⟩
    · isplitr
      · iexact Hkm
      · iexact Hk
    have hmeq : ms[mN]'hmlt = m := by
      rw [List.getElem?_eq_getElem hmlt] at hm; exact Option.some.inj hm
    have hiff := Hlt mN hmlt
    rw [hmeq] at hiff
    have hm1 : sint.Z (W64 ((mN : Nat) : Int) + W64 1) = (mN : Int) + 1 := by
      rw [show W64 ((mN : Nat) : Int) + W64 1 = W64 ((mN + 1 : Nat) : Int) by push_cast; word]
      exact sint_Z_W64_nat _ (by omega)
    wp_if_destruct
    · -- the key is smaller: search above `mid`
      rw [compareResult_lt] at Hif
      have := hiff.1 Hif
      wp_for_post
      iexists (W64 ((mN : Nat) : Int) + W64 1), hi
      iframe
      ipureintro; rw [hm1]; omega
    · -- the key is not smaller: search below `mid`
      rw [compareResult_lt] at Hif
      have : ¬ mN < r := fun h => Hif (hiff.2 h)
      wp_for_post
      iexists lo, W64 ((mN : Nat) : Int)
      iframe
      ipureintro; rw [hmZ]; omega
  · -- the search is done: `lo = r`
    have hlr : sint.Z lo = r := by omega
    have : lo = W64 (r : Int) := w64_of_sint_nat _ _ (by simp only [sint.nat]; omega) Hlh.1
    rw [this]
    iapply HΦ
    iexact Hk

end proof

end Perennial
