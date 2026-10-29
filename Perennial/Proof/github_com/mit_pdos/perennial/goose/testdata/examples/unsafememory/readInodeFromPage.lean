/-
The proof of `readInodeFromPage`: each iteration reads one element and slices its key and value out of the page.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__branchPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__key
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__value
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.branchPageElement__key

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

set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.wp_proof
    (wp_leafPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.spec (GF := GF) (hG := hG))
    (wp_branchPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.branchPageElement.spec (GF := GF) (hG := hG))
    (wp_leafKey : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.key.spec (GF := GF) (hG := hG))
    (wp_leafValue : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.value.spec (GF := GF) (hG := hG))
    (wp_branchKey : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.branchPageElement.key.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.spec (GF := GF) (hG := hG) := by
  intro p hdr ms tail
  wp_start as ⟨#Hp, #Hb, %H⟩
  obtain ⟨Hpos, Hcount, Hn16, Hfit, Hkeys⟩ := H
  have hnn : p ≠ null := by intro h; subst h; simp [null] at Hpos
  icases typedPointsto_split _ _ _ $$ Hp with Hp'
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp' with ⟨Hid, Hflags, Hcnt, Hoverflow, -⟩
  ihave %Hbd := bytesPointsto_in_bounds_imp _ _ _ $$ Hb
  have hcZ : uint.Z hdr.count' = ms.length := by
    rw [Hcount]; simp only [uint.Z]; word
  simp only [leafPageFlag]
  wp_auto
  wp_apply wp_slice_make2 (V := inode) $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; rw [hcZ]; simp only [sint.Z]; word
  have hnZ : sint.nat (W64 (uint.Z hdr.count')) = ms.length := by
    rw [hcZ]; show (sint.Z (W64 (ms.length : Int))).toNat = _
    rw [sint_Z_W64_nat _ (by omega)]; omega
  rw [hnZ]
  ihave HI : (∃ (i : w64) (xs : List inode),
      "i" ∷ i_ptr ↦ i ∗
      "inodes" ∷ inodes_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* (xs ++ List.replicate (ms.length - sint.nat i) (zero_val inode)) ∗
      "Hxs" ∷ ([∗list] x;m ∈ xs;(readBack (pageIsLeaf hdr) ms).take (sint.nat i), inodeOwn x m) ∗
      "HΦ" ∷ (∀ s, inodesOwn s (readBack (pageIsLeaf hdr) ms) -∗ Φ #s) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val GoSlice ∗
      "p" ∷ p_ptr ↦ p ∗
      "isLeaf" ∷ isLeaf_ptr ↦ pageIsLeaf hdr ∗
      "%Hxl" ∷ ⌜xs.length = sint.nat i⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ ms.length⌝ : IProp GF) $$ [i inodes Hsl HΦ «$res0» p isLeaf]
  · iexists (W64 0), []
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.take_zero, List.nil_append, Nat.sub_zero,
      show pageIsLeaf hdr = !decide (hdr.flags' &&& W16 2 = W16 0) by simp [pageIsLeaf]]
    iframe
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    · ipureintro; exact ⟨rfl, by decide, by simp⟩
  wp_for HI
  have hcW : sint.Z (W64 (uint.Z hdr.count')) = ms.length := by
    rw [hcZ]; exact sint_Z_W64_nat _ (by omega)
  have hit : sint.Z i = i.toInt := rfl
  by_cases hexit : sint.Z i < ms.length
  · wp_if_destruct
    · -- an iteration
      rw [hcW] at Hif
      have hiZ : sint.Z i = (sint.nat i : Int) := by
        simp only [sint.nat]; rw [Int.toNat_of_nonneg Hi.1]
      have hin : sint.nat i < ms.length := by omega
      obtain ⟨m, hm⟩ : ∃ m, ms[sint.nat i]? = some m := ⟨_, List.getElem?_eq_getElem hin⟩
      have hle := dataOff_le' ms (sint.nat i) m hm
      have hge := dataOff_ge ms (sint.nat i)
      have hbody := pageBody_length (pageIsLeaf hdr) ms
      have hbody' := pageBody_length true ms
      have hb := (Hbd (by
        intro h; have := congrArg List.length h; simp [hbody] at this; omega)).2
      simp only [Loc.add, List.length_append] at hb
      have hiW : uint.Z (W16 (sint.Z i)) = sint.nat i := by
        rw [hiZ]; simp only [uint.Z]; word
      cases hL : pageIsLeaf hdr
      · -- a branch page
        wp_auto
        wp_apply wp_branchPageElement
        · ipureintro; rw [hiW]; refine ⟨Hpos, ?_⟩; omega
        rw [hiW]
        have hlt : sint.nat i < (branchElems ms).length := by rw [branchElems_length]; exact hin
        have he := pageBody_branch_elem ms tail (sint.nat i) hin
        ihave He := bytesPointsto_sub (p +ₗ 16) (pageBody false ms ++ tail)
          (encode ((branchElems ms)[sint.nat i]'hlt)) (16 * sint.nat i)
          (by rw [ByteEncoding.encode_length, List.length_append, pageBody_length]; omega)
          (by rw [ByteEncoding.encode_length]; exact he) $$ Hb
        icases (bytesPointsto_typed (V := branchPageElement)
          ((p +ₗ 16) +ₗ ((16 * sint.nat i : Nat) : Int)) DFrac.discard _ (ByteEncoding.encode_length _)
          (by simp only [Loc.add]; omega)).1 $$ He with He
        rw [ByteEncoding.decode_encode, branchElems_getElem' ms (sint.nat i) m hm hlt, loc_add_assoc,
          show (16 : Int) + ((16 * sint.nat i : Nat) : Int) = 16 + 16 * (sint.nat i : Int) by omega]
        icases typedPointsto_split _ _ _ $$ He with He'
        simp only [TypedPointsto.typedPointstoDef]
        icases He' with ⟨Hep, Hek, Hpg, -⟩
        wp_auto
        have hpos : uint.Z (W32 ((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int)) =
            ((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int) := by
          simp only [uint.Z]; word
        have hkz : uint.Z (W32 (m.key.length : Int)) = m.key.length := by simp only [uint.Z]; word
        have hvz : uint.Z (W32 (m.value.length : Int)) = m.value.length := by simp only [uint.Z]; word
        have haddr : p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ
            (((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int)) =
            p +ₗ (dataOff ms (sint.nat i) : Int) := by
          rw [loc_add_assoc]; congr 1; omega
        wp_apply wp_branchKey $$ [He] as He
        · iframe He; ipureintro; simp only [hpos, hkz, Loc.add]; omega
        simp only [hpos, hkz, haddr]
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        have hslZ : sint.Z sl.len = ms.length := by
          rw [List.length_append, List.length_replicate, Hxl] at Hsll
          have e1 : sint.Z sl.len = sl.len.toInt := rfl
          have e2 := Hsll.2
          simp only [sint.nat] at Hsll e2; omega
        simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi.1, by omega⟩]
        wp_apply wp_store_slice_index $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; simp only [List.length_append, List.length_replicate]; omega
        -- the key aliases the page
        ihave Hk := bytesPointsto_sub (p +ₗ 16) (pageBody false ms ++ tail) m.key
          (dataOff ms (sint.nat i) - 16) (by rw [List.length_append, pageBody_length]; omega)
          (pageBody_key false ms tail _ m hm) $$ Hb
        rw [loc_add_assoc, show (16 : Int) + ((dataOff ms (sint.nat i) - 16 : Nat) : Int) =
          (dataOff ms (sint.nat i) : Int) by omega]
        icases (bytesPointsto_ownSlice _ _ _ (by simp only [Loc.add]; omega) (by omega)).1 $$ Hk
          with Hk
        wp_pures
        wp_for_post
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
          show (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1
          have : sint.Z (i + W64 1) = sint.Z i + 1 := by word
          omega
        iexists (i + W64 1), xs ++ [inode.mk 0 m.pgid
          (slice.mk (p +ₗ (dataOff ms (sint.nat i) : Int)) (W64 (m.key.length : Int))
            (W64 (m.key.length : Int))) slice.nil]
        rw [hi1, take_succ_of_getElem? _ _ _ (readBack_branch_getElem? ms _ m hm),
          show (sint.Z i).toNat = xs.length by rw [Hxl],
          set_append_replicate _ _ _ _ (by omega), ← Hxl,
          show ms.length - xs.length - 1 = ms.length - (xs.length + 1) by omega]
        iframe i inodes Hsl HΦ «$res0» p isLeaf
        isplitl [Hk Hxs]
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hxs
          unfold inodeOwn
          dsimp only
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitl [Hk]
          · iexact Hk
          · iapply ownSlice_nil
        · ipureintro; simp only [List.length_append, List.length_singleton]
          refine ⟨by trivial, by word, by word⟩
      · -- a leaf page
        wp_auto
        wp_apply wp_leafPageElement
        · ipureintro; rw [hiW]; refine ⟨Hpos, ?_⟩; omega
        rw [hiW]
        have hlt : sint.nat i < (leafElems ms).length := by rw [leafElems_length]; exact hin
        have he := pageBody_leaf_elem ms tail (sint.nat i) hin
        ihave He := bytesPointsto_sub (p +ₗ 16) (pageBody true ms ++ tail)
          (encode ((leafElems ms)[sint.nat i]'hlt)) (16 * sint.nat i)
          (by rw [ByteEncoding.encode_length, List.length_append, hbody']; omega)
          (by rw [ByteEncoding.encode_length]; exact he) $$ Hb
        icases (bytesPointsto_typed (V := leafPageElement)
          ((p +ₗ 16) +ₗ ((16 * sint.nat i : Nat) : Int)) DFrac.discard _ (ByteEncoding.encode_length _)
          (by simp only [Loc.add]; omega)).1 $$ He with He
        rw [ByteEncoding.decode_encode, leafElems_getElem' ms (sint.nat i) m hm hlt, loc_add_assoc,
          show (16 : Int) + ((16 * sint.nat i : Nat) : Int) = 16 + 16 * (sint.nat i : Int) by omega]
        icases typedPointsto_split _ _ _ $$ He with He'
        simp only [TypedPointsto.typedPointstoDef]
        icases He' with ⟨Hef, Hep, Hek, Hev, -⟩
        wp_auto
        have hpos : uint.Z (W32 ((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int)) =
            ((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int) := by
          simp only [uint.Z]; word
        have hkz : uint.Z (W32 (m.key.length : Int)) = m.key.length := by simp only [uint.Z]; word
        have hvz : uint.Z (W32 (m.value.length : Int)) = m.value.length := by simp only [uint.Z]; word
        have haddr : p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ
            (((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int)) =
            p +ₗ (dataOff ms (sint.nat i) : Int) := by
          rw [loc_add_assoc]; congr 1; omega
        wp_apply wp_leafKey $$ [He] as He
        · iframe He; ipureintro; simp only [hpos, hkz, Loc.add]; omega
        wp_apply wp_leafValue $$ [He] as He
        · iframe He; ipureintro; simp only [hpos, hkz, hvz, Loc.add]; omega
        have haddr2 : p +ₗ (16 + 16 * (sint.nat i : Int)) +ₗ
            (((dataOff ms (sint.nat i) - (16 + 16 * sint.nat i) : Nat) : Int) + (m.key.length : Int)) =
            p +ₗ ((dataOff ms (sint.nat i) + m.key.length : Nat) : Int) := by
          rw [loc_add_assoc]; congr 1; omega
        simp only [hpos, hkz, hvz, haddr, haddr2]
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        have hslZ : sint.Z sl.len = ms.length := by
          rw [List.length_append, List.length_replicate, Hxl] at Hsll
          have e1 : sint.Z sl.len = sl.len.toInt := rfl
          have e2 := Hsll.2
          simp only [sint.nat] at Hsll e2; omega
        simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi.1, by omega⟩]
        wp_apply wp_store_slice_index $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; simp only [List.length_append, List.length_replicate]; omega
        -- the key and the value alias the page
        ihave Hk := bytesPointsto_sub (p +ₗ 16) (pageBody true ms ++ tail) m.key
          (dataOff ms (sint.nat i) - 16) (by rw [List.length_append, hbody']; omega)
          (pageBody_key true ms tail _ m hm) $$ Hb
        ihave Hv := bytesPointsto_sub (p +ₗ 16) (pageBody true ms ++ tail) m.value
          (dataOff ms (sint.nat i) - 16 + m.key.length) (by rw [List.length_append, hbody']; omega)
          (pageBody_value true ms tail _ m hm) $$ Hb
        rw [loc_add_assoc, show (16 : Int) + ((dataOff ms (sint.nat i) - 16 : Nat) : Int) =
          (dataOff ms (sint.nat i) : Int) by omega]
        rw [loc_add_assoc, show (16 : Int) + ((dataOff ms (sint.nat i) - 16 + m.key.length : Nat) : Int) =
          ((dataOff ms (sint.nat i) + m.key.length : Nat) : Int) by omega]
        icases (bytesPointsto_ownSlice _ _ _ (by simp only [Loc.add]; omega) (by omega)).1 $$ Hk
          with Hk
        icases (bytesPointsto_ownSlice _ _ _ (by simp only [Loc.add]; omega) (by omega)).1 $$ Hv
          with Hv
        wp_pures
        wp_for_post
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
          show (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1
          have : sint.Z (i + W64 1) = sint.Z i + 1 := by word
          omega
        iexists (i + W64 1), xs ++ [inode.mk m.flags 0
          (slice.mk (p +ₗ (dataOff ms (sint.nat i) : Int)) (W64 (m.key.length : Int))
            (W64 (m.key.length : Int)))
          (slice.mk (p +ₗ ((dataOff ms (sint.nat i) + m.key.length : Nat) : Int))
            (W64 (m.value.length : Int)) (W64 (m.value.length : Int)))]
        rw [hi1, take_succ_of_getElem? _ _ _ (readBack_leaf_getElem? ms _ m hm),
          show (sint.Z i).toNat = xs.length by rw [Hxl],
          set_append_replicate _ _ _ _ (by omega), ← Hxl,
          show ms.length - xs.length - 1 = ms.length - (xs.length + 1) by omega]
        iframe i inodes Hsl HΦ «$res0» p isLeaf
        isplitl [Hk Hv Hxs]
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hxs
          unfold inodeOwn
          dsimp only
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitl [Hk]
          · iexact Hk
          · iexact Hv
        · ipureintro; simp only [List.length_append, List.length_singleton]
          refine ⟨by trivial, by word, by word⟩
    · rw [hcW] at Hif; exact absurd hexit Hif
  · rw [hcW, show decide (sint.Z i < (ms.length : Int)) = false from decide_eq_false hexit]
    simp only [Bool.false_eq_true, ite_false]
    ipersist Hsl
    wp_auto
    · -- the loop is done
      have hin : sint.nat i = ms.length := by simp only [sint.nat]; omega
      rw [hin, Nat.sub_self, List.replicate_zero, List.append_nil,
        List.take_of_length_le (by rw [readBack_length]; exact Nat.le_refl _)]
      iapply HΦ
      unfold inodesOwn
      iexists xs
      iframe Hxs
      iexact Hsl

end proof

end Perennial
