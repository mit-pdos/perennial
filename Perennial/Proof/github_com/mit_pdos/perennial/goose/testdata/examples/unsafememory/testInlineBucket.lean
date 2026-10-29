/-
The proof of `testInlineBucket`: an inline bucket stored as the value of a leaf page, at every
offset `32 + keyLen` (aligned or not), opens to its header and inodes, writable or not.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testInlineBucket
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__value
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual
public import Perennial.Spec.bytes.Equal

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
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testInlineBucket.wp_proof
    (wp_leafInodes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.spec (GF := GF) (hG := hG))
    (wp_writeInlineBucket : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket.spec (GF := GF) (hG := hG))
    (wp_writeLeaf : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.spec (GF := GF) (hG := hG))
    (wp_leafPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.spec (GF := GF) (hG := hG))
    (wp_leafValue : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.value.spec (GF := GF) (hG := hG))
    (wp_Equal : bytes.Equal.spec (GF := GF) (hG := hG))
    (wp_openInlineBucket : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket.spec (GF := GF) (hG := hG))
    (wp_readInodeFromPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.spec (GF := GF) (hG := hG))
    (wp_inodesEqual : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testInlineBucket.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro #Hpkg HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_leafInodes as %s #Hin
  wp_apply wp_writeInlineBucket _ _ _ s leafModel $$ [«$a0»] as %value ⟨-, Hv⟩
  · iframe; iframe Hin; ipureintro; exact leafModel_fits
  ipersist Hv
  generalize hVB : encode (⟨0, W64 42⟩ : InBucket) ++ encode (leafHeader leafModel) ++
    pageBody true leafModel = VB
  have hVBl : VB.length = 100 := by
    rw [← hVB]; simp only [List.length_append, ByteEncoding.encode_length, leafModel_body_length]
  ihave HI : (∃ k : w64,
      "keyLen" ∷ keyLen_ptr ↦ k ∗
      "HΦ" ∷ Φ #true ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
      "inner" ∷ inner_ptr ↦ s ∗
      "value" ∷ value_ptr ↦ value ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ 9⌝ : IProp GF) $$ [keyLen HΦ «$res0» inner value]
  · iexists (W64 1)
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · -- an iteration
    rw [show sint.Z (W64 8) = 8 from rfl] at Hif
    have hkn : sint.Z k = (sint.nat k : Int) := by
      have : sint.nat k = (sint.Z k).toNat := rfl
      omega
    have hk1 : 1 ≤ sint.nat k := by omega
    have hk8 : sint.nat k ≤ 8 := by omega
    generalize hn : sint.nat k = n at *
    wp_apply wp_slice_make2 (V := w8) $$ [] as %key ⟨Hkey, -⟩
    · ipureintro; omega
    rw [hn, show (zero_val w8 : w8) = 0 from rfl]
    ihave %Hkl := ownSlice_len _ _ _ $$ Hkey
    have hkZ : sint.Z key.len = n := sint_Z_eq_of_sint_nat _ _ (by simpa using Hkl.1) Hkl.2
    rename_i ip'
    irename : ip' ↦ (zero_val w64) => Hi'
    -- the loop filling the key
    ihave HJ : (∃ j iv : w64,
        "i" ∷ i_ptr ↦ j ∗
        "Hi'" ∷ ip' ↦ iv ∗
        "Hkey" ∷ key ↦* (List.replicate (sint.nat j) (W8 107) ++ List.replicate (n - sint.nat j) 0) ∗
        "key" ∷ key_ptr ↦ key ∗
        "keyLen" ∷ keyLen_ptr ↦ k ∗
        "HΦ" ∷ Φ #true ∗
        "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
        "inner" ∷ inner_ptr ↦ s ∗
        "value" ∷ value_ptr ↦ value ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ n⌝ : IProp GF) $$ [i Hi' Hkey key keyLen HΦ «$res0» inner value]
    · iexists (W64 0), _
      rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero, List.nil_append, Nat.sub_zero]
      iframe
      ipureintro; refine ⟨by decide, ?_⟩; show (0 : Int) ≤ n; omega
    wp_for HJ
    wp_if_destruct
    · -- an iteration
      rw [hkZ] at Hif
      have hjZ : sint.Z j = (sint.nat j : Int) := by
        have : sint.nat j = (sint.Z j).toNat := rfl
        omega
      have hjn : sint.nat j < n := by omega
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z key.len := ⟨Hj.1, by omega⟩
      have hlen : (List.replicate (sint.nat j) (W8 107) ++ List.replicate (n - sint.nat j) (0 : w8)).length = n := by
        simp; omega
      simp only [hb, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index key (sint.Z j) _ (DFrac.own 1) (0 : w8) Hj.1 $$ [Hkey] as Hkey
      · iframe Hkey
        ipureintro
        rw [show (sint.Z j).toNat = sint.nat j from rfl, List.getElem?_append_right (by simp),
          List.length_replicate, Nat.sub_self, List.getElem?_replicate]
        simp; omega
      simp only [hb, _root_.and_self, ite_true]
      wp_apply wp_store_slice_index key (sint.Z j) _ (W8 107) $$ [Hkey] as Hkey
      · iframe Hkey; ipureintro; rw [hlen]; omega
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
        omega
      iexists (j + W64 1), j
      rw [hj1, show (sint.Z j).toNat = (List.replicate (sint.nat j) (W8 107)).length by simp,
        set_append_replicate _ _ _ _ (by omega), List.replicate_succ',
        show n - sint.nat j - 1 = n - (sint.nat j + 1) by omega]
      iframe
      ipureintro
      constructor <;> word
    -- the key is filled
    have hjn : sint.nat j = n := by
      rw [hkZ] at Hif; have : sint.nat j = (sint.Z j).toNat := rfl; omega
    rw [hjn, Nat.sub_self, List.replicate_zero, List.append_nil]
    ipersist Hkey
    wp_apply wp_slice_make2 (V := w8) $$ [] as %outer ⟨Hout, -⟩
    · ipureintro; decide
    ihave %Hol := ownSlice_len _ _ _ $$ Hout
    ihave %Hop := ownSlice_ptr_pos _ _ _ (by
      intro h; have := congrArg List.length h; rw [List.length_replicate] at this
      exact absurd this (by decide)) $$ Hout
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hop $$ Hout
      with ⟨Hout, -⟩
    rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
    rw [List.length_replicate] at Hol
    ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by
      intro h; have := congrArg List.length h; rw [List.length_replicate] at this
      exact absurd this (by decide)) $$ Hout
    simp only [List.length_replicate] at Hbd
    have houtW : outer.len = W64 (4096 : Nat) := w64_of_sint_nat _ _ Hol.1 Hol.2
    wp_apply wp_slice_literal (V := inode) [⟨W32 1, 0, key, value⟩]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hs, -⟩
    ipersist Hs
    have hbody : (pageBody true [⟨W32 1, 0, List.replicate n (W8 107), VB⟩]).length = 116 + n := by
      rw [pageBody_length]; simp [dataBytes, InodeM.kv, hVBl]; omega
    have hfit : pageFits [⟨W32 1, 0, List.replicate n (W8 107), VB⟩] := by
      refine ⟨by simp, by rw [hbody]; omega, ?_⟩
      intro m hm; simp at hm; subst hm; simp; omega
    wp_apply wp_writeLeaf outer _ [⟨W32 1, 0, List.replicate n (W8 107), VB⟩] 4096 $$ [Hout] as Hout
    · iframe Hout
      isplitl
      · unfold inodesOwn
        iexists _
        iframe Hs
        iapply BigSepL2.bigSepL2_cons.2
        isplitr
        · unfold inodeOwn; iframe Hkey Hv; ipureintro; exact ⟨rfl, rfl⟩
        iapply BigSepL2.bigSepL2_nil.2
        itrivial
      · ipureintro; exact ⟨houtW, by decide, hfit, by rw [hbody]; omega⟩
    generalize hm : (⟨W32 1, 0, List.replicate n (W8 107), VB⟩ : InodeM) = m at *
    imod bytesPointsto_persist _ _ _ $$ Hout with #Hout
    rw [List.append_assoc]
    icases (bytesPointsto_app _ _ _ _).1 $$ Hout with ⟨#Hhdr, #Hpg⟩
    rw [ByteEncoding.encode_length]
    generalize hB : pageBody true [m] ++ List.replicate (4096 - 16 - (pageBody true [m]).length) 0 = B
    have hBl : B.length = 4096 - 16 := by rw [← hB]; simp [hbody]; omega
    -- `p.leafPageElement(0)`
    wp_apply wp_leafPageElement
    · ipureintro; refine ⟨Hop, ?_⟩; rw [show uint.Z (W16 0) = 0 from rfl]; omega
    rw [show uint.Z (W16 0) = 0 from rfl, show (16 : Int) + 16 * 0 = ((16 : Nat) : Int) from rfl]
    have helem : (leafElems [m])[0]'(by simp [leafElems_length]) = ⟨W32 1, W32 16, W32 (n : Int), W32 100⟩ := by
      rw [← hm]; simp [leafElems, dataOff, dataBytes, hVBl]
    have he := pageBody_leaf_elem [m] (List.replicate (4096 - 16 - (pageBody true [m]).length) 0) 0
      (by simp)
    rw [hB, helem, Nat.mul_zero] at he
    ihave #Hel := bytesPointsto_sub _ B (encode (⟨W32 1, W32 16, W32 (n : Int), W32 100⟩ : leafPageElement)) 0
      (by rw [ByteEncoding.encode_length, hBl]; omega) he $$ Hpg
    have hp16 : 0 < (outer.ptr +ₗ ((16 : Nat) : Int)).addr := by simp [Loc.add]; omega
    rw [show ((0 : Nat) : Int) = 0 from rfl, loc_add_0]
    icases (bytesPointsto_typed (V := leafPageElement) _ _ _ (ByteEncoding.encode_length _) hp16).1
      $$ Hel with #Hel
    rw [ByteEncoding.decode_encode]
    have hnZ : uint.Z (W32 (n : Int)) = n := by simp only [uint.Z]; word
    wp_apply wp_leafValue $$ [Hel] as -
    · iframe Hel; ipureintro; refine ⟨hp16, ?_⟩
      rw [hnZ, show uint.Z (W32 16) = 16 from rfl, show uint.Z (W32 100) = 100 from rfl]
      simp only [Loc.add] at *; omega
    rw [hnZ, show uint.Z (W32 16) = 16 from rfl, show uint.Z (W32 100) = 100 from rfl]
    -- the value's bytes
    have hmk : m.key.length = n := by rw [← hm]; simp
    have hmv : m.value = VB := by rw [← hm]
    have hd0 : dataOff [m] 0 = 32 := by simp [dataOff, dataBytes]
    have hv := pageBody_value true [m] (List.replicate (4096 - 16 - (pageBody true [m]).length) 0) 0 m rfl
    rw [hB, hd0, hmk, hmv, hVBl] at hv
    ihave #Hvb := bytesPointsto_sub _ B VB (32 - 16 + n) (by rw [hVBl, hBl]; omega) (by rw [hVBl]; exact hv)
      $$ Hpg
    rw [show (((32 - 16 + n : Nat)) : Int) = 16 + (n : Int) by omega]
    icases (bytesPointsto_ownSlice _ _ VB (by simp [Loc.add]; omega) (by omega)).1 $$ Hvb with #Hvs
    rw [hVBl, show ((100 : Nat) : Int) = 100 from rfl]
    have hVB' : VB = encode (⟨0, W64 42⟩ : InBucket) ++
        (encode (leafHeader leafModel) ++ pageBody true leafModel) := by
      rw [← hVB, List.append_assoc]
    have hRne : encode (leafHeader leafModel) ++ pageBody true leafModel ≠ [] := by
      simp [ByteEncoding.encode_ne_nil _ (show 0 < 16 by decide)]
    wp_apply wp_Equal _ value DFrac.discard DFrac.discard VB VB $$ [] as -
    · iframe Hvs Hv
    -- `openInlineBucket(v, true)`
    wp_apply wp_openInlineBucket _ ⟨0, W64 42⟩ _ true $$ [] as %b %ip ⟨Hb, #Hip, %Hipp⟩
    · rw [hVB'] at *; iframe Hvs; ipureintro; exact hRne
    have hrb : readBack (pageIsLeaf (leafHeader leafModel)) leafModel = leafModel := by
      rw [pageIsLeaf_leafHeader]; simp [readBack, leafModel]
    icases (bytesPointsto_app _ _ _ _).1 $$ Hip with ⟨#Hh, #Hpb⟩
    icases (bytesPointsto_typed (V := Page) _ _ _ (ByteEncoding.encode_length _) Hipp).1 $$ Hh with #Hh
    rw [ByteEncoding.decode_encode, ByteEncoding.encode_length,
      show ((16 : Nat) : Int) = (16 : Int) from rfl]
    wp_apply wp_readInodeFromPage ip (leafHeader leafModel) leafModel [] as %out #Hout
    · rw [pageIsLeaf_leafHeader, List.append_nil]
      iframe Hh Hpb; ipureintro; exact ⟨Hipp, rfl, leafModel_fits⟩
    wp_apply wp_inodesEqual out s _ leafModel as -
    · iframe Hout Hin
    rw [hrb, decide_eq_true rfl]
    wp_auto
    -- `openInlineBucket(v, false)`: `b.sequence = 43` did not write through `v`
    wp_apply wp_openInlineBucket _ ⟨0, W64 42⟩ _ false $$ [] as %b2 %ip2 ⟨Hb2, #Hip2, %Hipp2⟩
    · rw [hVB'] at *; iframe Hvs; ipureintro; exact hRne
    simp only
    icases typedPointsto_split _ _ _ $$ Hb2 with Hb2
    simp only [TypedPointsto.typedPointstoDef]
    icases Hb2 with ⟨#Hroot, #Hseq, -⟩
    wp_auto
    icases (bytesPointsto_app _ _ _ _).1 $$ Hip2 with ⟨#Hh2, #Hpb2⟩
    icases (bytesPointsto_typed (V := Page) _ _ _ (ByteEncoding.encode_length _) Hipp2).1 $$ Hh2
      with #Hh2
    rw [ByteEncoding.decode_encode, ByteEncoding.encode_length,
      show ((16 : Nat) : Int) = (16 : Int) from rfl]
    wp_apply wp_readInodeFromPage ip2 (leafHeader leafModel) leafModel [] as %out2 #Hout2
    · rw [pageIsLeaf_leafHeader, List.append_nil]
      iframe Hh2 Hpb2; ipureintro; exact ⟨Hipp2, rfl, leafModel_fits⟩
    wp_apply wp_inodesEqual out2 s _ leafModel as -
    · iframe Hout2 Hin
    rw [hrb, decide_eq_true rfl]
    wp_auto
    wp_for_post
    iexists (k + W64 1)
    iframe
    ipureintro
    constructor <;> word
    done
  · -- the end of the loop
    iexact HΦ

end proof

end Perennial
