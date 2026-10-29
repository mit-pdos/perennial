/-
The proof of `writeInodeToPage`: each iteration fills one element over zeros and one inode's data.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__pageElementSize
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__branchPageElement

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.wp_proof
    (wp_unsafeByteSlice : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice.spec (GF := GF) (hG := hG))
    (wp_pageElementSize : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.pageElementSize.spec (GF := GF) (hG := hG))
    (wp_leafPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.spec (GF := GF) (hG := hG))
    (wp_branchPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.branchPageElement.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.spec (GF := GF) (hG := hG) := by
  intro s ms p hdr R
  wp_start as ⟨#Hin, Hp, Hb, %H⟩
  obtain ⟨Hpos, ⟨Hn16, Hfit, Hkeys⟩, HR⟩ := H
  have hnn : p ≠ null := by intro h; subst h; simp [null] at Hpos
  unfold inodesOwn
  icases Hin with ⟨%xs, #Hs, #Hxs⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply wp_pageElementSize $$ [Hp] as Hp
  · iframe; ipureintro; exact hnn
  simp only [leafPageFlag]
  wp_auto
  rename_i k_ptr
  irename : k_ptr ↦ (zero_val w64) => Hk
  -- the bytes after the header: the elements, then the data area
  have hbody := pageBody_length true ms
  have hEle : List.replicate R (0 : w8) = List.replicate (16 * ms.length) 0 ++
      List.replicate (R - 16 * ms.length) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  ihave %Hbd := bytesPointsto_bounds_imp _ _ _ $$ Hb
  have hbound : 0 < R → p.addr + 16 + R ≤ maxAddr := by
    intro hR0
    have := (Hbd (by simp; omega)).2
    simp only [Loc.add, List.length_replicate] at this; omega
  rw [hEle]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨HE, HD⟩
  rw [List.length_replicate, loc_add_assoc]
  have hlenW : s.len = W64 (ms.length : Int) := by
    have h1 := Hslen.1
    have h2 := Hslen.2
    rw [Hlen] at h1
    simp only [sint.nat, sint.Z] at h1 h2
    apply BitVec.eq_of_toInt_eq
    rw [show (W64 (ms.length : Int)).toInt = ms.length from sint_Z_W64_nat _ (by omega)]
    omega
  ihave HI : (∃ (j kv : w64) (it : inode),
      "i" ∷ i_ptr ↦ j ∗
      "Hk" ∷ k_ptr ↦ kv ∗
      "item" ∷ item_ptr ↦ it ∗
      "off" ∷ off_ptr ↦ W64 (dataOff ms (sint.nat j) : Int) ∗
      "Hp" ∷ p ↦ hdr ∗
      "HE" ∷ bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (elemsPrefix (pageIsLeaf hdr) ms (sint.nat j) ++
          List.replicate (16 * (ms.length - sint.nat j)) 0) ∗
      "HD" ∷ bytesPointsto (p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int))) (DFrac.own 1)
        (dataBytes (ms.take (sint.nat j)) ++
          List.replicate (R - 16 * ms.length - (dataBytes (ms.take (sint.nat j))).length) 0) ∗
      "HΦ" ∷ (∀ w : w32, p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1)
          (pageBody (pageIsLeaf hdr) ms ++ List.replicate (R - (pageBody true ms).length) 0) -∗
        Φ #w) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val w32 ∗
      "p" ∷ p_ptr ↦ p ∗
      "isLeaf" ∷ isLeaf_ptr ↦ pageIsLeaf hdr ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ms.length⌝ : IProp GF) $$ [i Hk item off Hp HE HD HΦ «$res0» p isLeaf]
  · iexists (W64 0), _, _
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, elemsPrefix_zero, List.take_zero, show dataBytes [] = [] from rfl, List.nil_append,
      List.nil_append, List.length_nil, Nat.sub_zero, Nat.sub_zero]
    rw [show W64 (dataOff ms 0 : Int) = W64 16 + W64 16 * s.len by
      rw [hlenW]; simp only [dataOff, List.take_zero, show dataBytes [] = [] from rfl,
        List.length_nil, Nat.add_zero]; word,
      show pageIsLeaf hdr = !decide (hdr.flags' &&& W16 2 = W16 0) by simp [pageIsLeaf]]
    iframe
    ipureintro; refine ⟨by decide, ?_⟩; simp
  wp_for HI
  have hsZ : sint.Z s.len = ms.length := by rw [hlenW]; exact sint_Z_W64_nat _ (by omega)
  have hjt : sint.Z j = j.toInt := rfl
  wp_if_destruct
  · -- an iteration
    rw [hsZ] at Hif
    have hjZ : sint.Z j = (sint.nat j : Int) := by
      simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
    have hjn : sint.nat j < ms.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xs[sint.nat j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hm : ms[sint.nat j]? = some ms[sint.nat j] := List.getElem?_eq_getElem hjn
    have hle := dataOff_le ms (sint.nat j) hjn
    have hsucc := dataOff_succ ms (sint.nat j) hjn
    have hdsucc := dataBytes_take_succ ms (sint.nat j) hjn
    have hkne := Hkeys _ (List.getElem_mem hjn)
    generalize ms[sint.nat j] = m at hm hle hsucc hdsucc hkne
    ihave Hx := BigSepL2.bigSepL2_lookup hx hm $$ Hxs
    unfold inodeOwn
    icases Hx with ⟨%Hxfp, #Hkey, #Hval⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hkey
    ihave %Hvl := ownSlice_len _ _ _ $$ Hval
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len from ⟨Hj.1, by omega⟩, _root_.and_self,
      ite_true]
    wp_apply wp_load_slice_index s (sint.Z j) xs DFrac.discard x Hj.1 as -
    · isplitr
      · iexact Hs
      · ipureintro; rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact hx
    -- the inode's key and value lengths
    have hkW : x.key'.len = W64 (m.key.length : Int) := w64_of_sint_nat _ _ Hkl.1 Hkl.2
    have hvW : x.value'.len = W64 (m.value.length : Int) := w64_of_sint_nat _ _ Hvl.1 Hvl.2
    have hkv : m.kv.length = m.key.length + m.value.length := by simp [InodeM.kv]
    have hR0 : 0 < R := by omega
    have hb := hbound hR0
    have hszW : x.key'.len + x.value'.len = W64 (m.kv.length : Int) := by
      rw [hkW, hvW, hkv]; push_cast; word
    have hoffZ : sint.Z (W64 (dataOff ms (sint.nat j) : Int)) = dataOff ms (sint.nat j) :=
      sint_Z_W64_nat _ (by omega)
    have hszZ : sint.Z (W64 (m.kv.length : Int)) = m.kv.length := sint_Z_W64_nat _ (by omega)
    rw [hszW]
    wp_apply wp_unsafeByteSlice
    · ipureintro; rw [hoffZ, hszZ]; simp only [Loc.add]; refine ⟨by omega, by omega, by decide, ?_⟩
      rw [show sint.Z (W64 0) = 0 from rfl]; omega
    rw [hoffZ, show sint.Z (W64 0) = 0 from rfl, loc_add_0,
      show W64 (m.kv.length : Int) - W64 0 = W64 (m.kv.length : Int) by simp]
    wp_apply wp_pageElementSize $$ [Hp] as Hp
    · iframe; ipureintro; exact hnn
    cases hL : pageIsLeaf hdr
    · -- a branch element
      wp_auto
      have hjW : uint.Z (W16 (sint.Z j)) = sint.nat j := by
        rw [hjZ]; simp only [uint.Z]; word
      wp_apply wp_branchPageElement
      · ipureintro; rw [hjW]; refine ⟨Hpos, ?_⟩; omega
      rw [hjW]
      icases bytesPointsto_view_at (V := branchPageElement) (p +ₗ 16) _ _ (16 * sint.nat j)
        (p +ₗ (16 + 16 * (sint.nat j : Int))) (by rw [loc_add_assoc]; congr 1)
        (by
          rw [List.length_append, List.length_replicate, elemsPrefix_length _ _ _ (by omega)]
          have : sint.nat j + 1 ≤ ms.length := hjn
          rw [Nat.mul_sub]; omega) (by simp [Loc.add]; omega) $$ HE
        with ⟨Hel, HE⟩
      wp_auto
      have hlt : sint.nat j < (branchElems ms).length := by rw [branchElems_length]; exact hjn
      ispecialize HE $$ %((branchElems ms)[sint.nat j]'hlt)
      ihave HE := HE $$ [Hel]
      · iapply typedPointsto_of_eq
        iframe Hel
        ipureintro
        rw [branchElems_getElem' ms (sint.nat j) m hm hlt]
        simp only [branchPageElement.mk.injEq]
        refine ⟨?_, ?_, Hxfp.2⟩
        · have hd0 : 16 + 16 * ms.length ≤ dataOff ms (sint.nat j) := by simp [dataOff]
          have hjW64 : j = W64 ((sint.nat j : Nat) : Int) := w64_of_sint_nat j _ rfl Hj.1
          generalize dataOff ms (sint.nat j) = a at *
          generalize sint.nat j = b at *
          rw [hjW64]
          have hb : 16 + 16 * b ≤ a := by omega
          have ha : a < 2 ^ 32 := by omega
          rw [show (((a - (16 + 16 * b) : Nat)) : Int) = (a : Int) - 16 - 16 * (b : Int) by omega]
          word
        · rw [hkW, sint_Z_W64_nat _ (by omega)]
      rw [elemsPrefix_step_branch ms (sint.nat j) hjn]
      -- the data area: the inode's bytes are zeros before the copies
      have hDl := dataBytes_length_le ms (sint.nat j + 1)
      rw [hdsucc, List.length_append] at hDl
      have hrep : List.replicate (R - 16 * ms.length - (dataBytes (List.take (sint.nat j) ms)).length)
          (0 : w8) = List.replicate m.kv.length 0 ++ List.replicate
            (R - 16 * ms.length - (dataBytes (List.take (sint.nat j + 1) ms)).length) 0 := by
        rw [List.replicate_append_replicate, hdsucc, List.length_append]; congr 1; omega
      rw [hrep]
      icases (bytesPointsto_app _ _ _ _).1 $$ HD with ⟨HD1, HD2⟩
      icases (bytesPointsto_app _ _ _ _).1 $$ HD2 with ⟨Hb, HD3⟩
      have haddr : p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int)) +ₗ
          ((dataBytes (List.take (sint.nat j) ms)).length : Int) =
          p +ₗ (dataOff ms (sint.nat j) : Int) := by
        rw [loc_add_assoc]; congr 1
      rw [haddr, List.length_replicate]
      icases (bytesPointsto_ownSlice _ _ _ (by simp [Loc.add]; omega) (by simp; omega)).1 $$ Hb
        with Hb
      rw [List.length_replicate]
      wp_apply wp_slice_copy _ _ _ m.key DFrac.discard $$ [Hb] as %n ⟨%Hn, Hb, -⟩
      · isplitl [Hb]
        · iexact Hb
        · iexact Hkey
      have hkl : m.key.length ≤ m.kv.length := by simp [InodeM.kv]
      rw [List.length_replicate, List.drop_replicate,
        List.take_of_length_le hkl] at *
      have hkpos : 0 < m.key.length := List.length_pos_iff.2 hkne
      have hnW : n = W64 (m.key.length : Int) := by
        have h1 : sint.nat n = m.key.length := by rw [Hn]; omega
        have h2 : 0 ≤ sint.Z n := by
          have : (sint.Z n).toNat = m.key.length := h1
          omega
        exact w64_of_sint_nat _ _ h1.symm h2
      subst hnW
      have hklZ : sint.Z (W64 (m.key.length : Int)) = m.key.length := sint_Z_W64_nat _ (by omega)
      wp_auto
      have hvl : m.value.length = m.kv.length - m.key.length := by
        simp [InodeM.kv]
      simp only [hklZ, hszZ, show 0 ≤ (m.key.length : Int) ∧ (m.key.length : Int) ≤ m.kv.length ∧
        (m.kv.length : Int) ≤ m.kv.length from ⟨by omega, by omega, by omega⟩]
      wp_auto
      have hsplit : 0 ≤ sint.Z (W64 (m.key.length : Int)) ∧ sint.Z (W64 (m.key.length : Int)) ≤
          sint.Z (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 (m.kv.length : Int))
            (W64 (m.kv.length : Int))).len := by
        constructor
        · rw [hklZ]; omega
        · change sint.Z (W64 (m.key.length : Int)) ≤ sint.Z (W64 (m.kv.length : Int))
          rw [hklZ, hszZ]; omega
      icases (ownSlice_split_all (W64 (m.key.length : Int)) _ _ _ hsplit).1 $$ Hb with ⟨Hb1, Hb2⟩
      have hkn : sint.nat (W64 (m.key.length : Int)) = m.key.length := by
        simp only [sint.nat, hklZ]; omega
      have hkvk : m.kv = m.key ++ m.value := rfl
      rw [hkn, List.take_left' rfl, List.drop_left' rfl,
        show (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 (m.kv.length : Int))
          (W64 (m.kv.length : Int))).len = W64 (m.kv.length : Int) from rfl]
      wp_apply wp_slice_copy _ _ _ m.value DFrac.discard $$ [Hb2] as %n2 ⟨-, Hb2, -⟩
      · isplitl [Hb2]
        · iexact Hb2
        · iexact Hval
      rw [List.length_replicate, ← hvl, List.take_of_length_le (Nat.le_refl _), List.drop_replicate,
        Nat.sub_self, List.replicate_zero, List.append_nil]
      icases (ownSlice_split_all (V := w8) (W64 (m.key.length : Int)) _ _ m.kv hsplit).2 $$ [Hb1 Hb2]
        with Hb
      · rw [hkn, hkvk, List.take_left' rfl, List.drop_left' rfl]
        iframe
      icases (bytesPointsto_ownSlice (p +ₗ (dataOff ms (sint.nat j) : Int)) _ m.kv
        (by simp [Loc.add]; omega) (by omega)).2 $$ Hb with Hb
      ihave HD : bytesPointsto (p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int))) (DFrac.own 1)
          (dataBytes (ms.take (sint.nat j + 1)) ++ List.replicate
            (R - 16 * ms.length - (dataBytes (List.take (sint.nat j + 1) ms)).length) 0)
          $$ [HD1 Hb HD3]
      · rw [hdsucc, List.append_assoc]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe HD1
        rw [haddr]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
        omega
      iexists (j + W64 1), j, x
      rw [hj1, hsucc, show W64 (dataOff ms (sint.nat j) : Int) + W64 (m.kv.length : Int) =
        W64 ((dataOff ms (sint.nat j) + m.kv.length : Nat) : Int) by push_cast; word]
      iframe
      ipureintro
      constructor <;> word
    · -- a leaf element
      wp_auto
      have hjW : uint.Z (W16 (sint.Z j)) = sint.nat j := by
        rw [hjZ]; simp only [uint.Z]; word
      wp_apply wp_leafPageElement
      · ipureintro; rw [hjW]; refine ⟨Hpos, ?_⟩; omega
      rw [hjW]
      icases bytesPointsto_view_at (V := leafPageElement) (p +ₗ 16) _ _ (16 * sint.nat j)
        (p +ₗ (16 + 16 * (sint.nat j : Int))) (by rw [loc_add_assoc]; congr 1)
        (by
          rw [List.length_append, List.length_replicate, elemsPrefix_length _ _ _ (by omega)]
          have : sint.nat j + 1 ≤ ms.length := hjn
          rw [Nat.mul_sub]; omega) (by simp [Loc.add]; omega) $$ HE
        with ⟨Hel, HE⟩
      wp_auto
      have hlt : sint.nat j < (leafElems ms).length := by rw [leafElems_length]; exact hjn
      ispecialize HE $$ %((leafElems ms)[sint.nat j]'hlt)
      ihave HE := HE $$ [Hel]
      · iapply typedPointsto_of_eq
        iframe Hel
        ipureintro
        rw [leafElems_getElem' ms (sint.nat j) m hm hlt]
        simp only [leafPageElement.mk.injEq]
        refine ⟨Hxfp.1, ?_, ?_, ?_⟩
        · have hd0 : 16 + 16 * ms.length ≤ dataOff ms (sint.nat j) := by simp [dataOff]
          have hjW64 : j = W64 ((sint.nat j : Nat) : Int) := w64_of_sint_nat j _ rfl Hj.1
          generalize dataOff ms (sint.nat j) = a at *
          generalize sint.nat j = b at *
          rw [hjW64]
          have hb : 16 + 16 * b ≤ a := by omega
          have ha : a < 2 ^ 32 := by omega
          rw [show (((a - (16 + 16 * b) : Nat)) : Int) = (a : Int) - 16 - 16 * (b : Int) by omega]
          word
        · rw [hkW, sint_Z_W64_nat _ (by omega)]
        · rw [hvW, sint_Z_W64_nat _ (by omega)]
      rw [elemsPrefix_step_leaf ms (sint.nat j) hjn]
      -- the data area: the inode's bytes are zeros before the copies
      have hDl := dataBytes_length_le ms (sint.nat j + 1)
      rw [hdsucc, List.length_append] at hDl
      have hrep : List.replicate (R - 16 * ms.length - (dataBytes (List.take (sint.nat j) ms)).length)
          (0 : w8) = List.replicate m.kv.length 0 ++ List.replicate
            (R - 16 * ms.length - (dataBytes (List.take (sint.nat j + 1) ms)).length) 0 := by
        rw [List.replicate_append_replicate, hdsucc, List.length_append]; congr 1; omega
      rw [hrep]
      icases (bytesPointsto_app _ _ _ _).1 $$ HD with ⟨HD1, HD2⟩
      icases (bytesPointsto_app _ _ _ _).1 $$ HD2 with ⟨Hb, HD3⟩
      have haddr : p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int)) +ₗ
          ((dataBytes (List.take (sint.nat j) ms)).length : Int) =
          p +ₗ (dataOff ms (sint.nat j) : Int) := by
        rw [loc_add_assoc]; congr 1
      rw [haddr, List.length_replicate]
      icases (bytesPointsto_ownSlice _ _ _ (by simp [Loc.add]; omega) (by simp; omega)).1 $$ Hb
        with Hb
      rw [List.length_replicate]
      wp_apply wp_slice_copy _ _ _ m.key DFrac.discard $$ [Hb] as %n ⟨%Hn, Hb, -⟩
      · isplitl [Hb]
        · iexact Hb
        · iexact Hkey
      have hkl : m.key.length ≤ m.kv.length := by simp [InodeM.kv]
      rw [List.length_replicate, List.drop_replicate,
        List.take_of_length_le hkl] at *
      have hkpos : 0 < m.key.length := List.length_pos_iff.2 hkne
      have hnW : n = W64 (m.key.length : Int) := by
        have h1 : sint.nat n = m.key.length := by rw [Hn]; omega
        have h2 : 0 ≤ sint.Z n := by
          have : (sint.Z n).toNat = m.key.length := h1
          omega
        exact w64_of_sint_nat _ _ h1.symm h2
      subst hnW
      have hklZ : sint.Z (W64 (m.key.length : Int)) = m.key.length := sint_Z_W64_nat _ (by omega)
      wp_auto
      have hvl : m.value.length = m.kv.length - m.key.length := by
        simp [InodeM.kv]
      simp only [hklZ, hszZ, show 0 ≤ (m.key.length : Int) ∧ (m.key.length : Int) ≤ m.kv.length ∧
        (m.kv.length : Int) ≤ m.kv.length from ⟨by omega, by omega, by omega⟩]
      wp_auto
      have hsplit : 0 ≤ sint.Z (W64 (m.key.length : Int)) ∧ sint.Z (W64 (m.key.length : Int)) ≤
          sint.Z (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 (m.kv.length : Int))
            (W64 (m.kv.length : Int))).len := by
        constructor
        · rw [hklZ]; omega
        · change sint.Z (W64 (m.key.length : Int)) ≤ sint.Z (W64 (m.kv.length : Int))
          rw [hklZ, hszZ]; omega
      icases (ownSlice_split_all (W64 (m.key.length : Int)) _ _ _ hsplit).1 $$ Hb with ⟨Hb1, Hb2⟩
      have hkn : sint.nat (W64 (m.key.length : Int)) = m.key.length := by
        simp only [sint.nat, hklZ]; omega
      have hkvk : m.kv = m.key ++ m.value := rfl
      rw [hkn, List.take_left' rfl, List.drop_left' rfl,
        show (slice.mk (p +ₗ (dataOff ms (sint.nat j) : Int)) (W64 (m.kv.length : Int))
          (W64 (m.kv.length : Int))).len = W64 (m.kv.length : Int) from rfl]
      wp_apply wp_slice_copy _ _ _ m.value DFrac.discard $$ [Hb2] as %n2 ⟨-, Hb2, -⟩
      · isplitl [Hb2]
        · iexact Hb2
        · iexact Hval
      rw [List.length_replicate, ← hvl, List.take_of_length_le (Nat.le_refl _), List.drop_replicate,
        Nat.sub_self, List.replicate_zero, List.append_nil]
      icases (ownSlice_split_all (V := w8) (W64 (m.key.length : Int)) _ _ m.kv hsplit).2 $$ [Hb1 Hb2]
        with Hb
      · rw [hkn, hkvk, List.take_left' rfl, List.drop_left' rfl]
        iframe
      icases (bytesPointsto_ownSlice (p +ₗ (dataOff ms (sint.nat j) : Int)) _ m.kv
        (by simp [Loc.add]; omega) (by omega)).2 $$ Hb with Hb
      ihave HD : bytesPointsto (p +ₗ ((16 : Int) + ((16 * ms.length : Nat) : Int))) (DFrac.own 1)
          (dataBytes (ms.take (sint.nat j + 1)) ++ List.replicate
            (R - 16 * ms.length - (dataBytes (List.take (sint.nat j + 1) ms)).length) 0)
          $$ [HD1 Hb HD3]
      · rw [hdsucc, List.append_assoc]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe HD1
        rw [haddr]
        iapply (bytesPointsto_app _ _ _ _).2
        iframe
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
        omega
      iexists (j + W64 1), j, x
      rw [hj1, hsucc, show W64 (dataOff ms (sint.nat j) : Int) + W64 (m.kv.length : Int) =
        W64 ((dataOff ms (sint.nat j) + m.kv.length : Nat) : Int) by push_cast; word]
      iframe
      ipureintro
      constructor <;> word
  · -- the loop is done: the elements and the data area are written
    have hjn : sint.nat j = ms.length := by
      rw [hsZ] at Hif; simp only [sint.nat]; omega
    rw [hjn, elemsPrefix_full, Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil,
      List.take_of_length_le (Nat.le_refl _)]
    iapply HΦ
    iframe Hp
    have he := elemBytes_length (pageIsLeaf hdr) ms
    rw [pageBody, List.append_assoc,
      show R - (pageBody true ms).length = R - 16 * ms.length - (dataBytes ms).length by
        rw [hbody]; omega]
    iapply (bytesPointsto_app _ _ _ _).2
    rw [he, loc_add_assoc]
    iframe

end proof

end Perennial
