/-
The proof of `inodesEqual`: the loop compares the inodes one by one.
-/
module

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.wp_proof
    (wp_Equal : bytes.Equal.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.spec (GF := GF) (hG := hG) := by
  intro a b ma mb
  wp_start as ⟨Ha, Hb⟩
  simp only [inodesOwn]
  icases Ha with ⟨%xa, #Hsa, #Hxa⟩
  icases Hb with ⟨%xb, #Hsb, #Hxb⟩
  ihave %Hla := BigSepL2.bigSepL2_length $$ Hxa
  ihave %Hlb := BigSepL2.bigSepL2_length $$ Hxb
  ihave %Hsla := ownSlice_len _ _ _ $$ Hsa
  ihave %Hslb := ownSlice_len _ _ _ $$ Hsb
  wp_auto
  have hna : sint.Z a.len = ma.length :=
    sint_Z_eq_of_sint_nat _ _ (Hla ▸ Hsla.1) Hsla.2
  have hnb : sint.Z b.len = mb.length :=
    sint_Z_eq_of_sint_nat _ _ (Hlb ▸ Hslb.1) Hslb.2
  wp_if_destruct
  · -- equal lengths: the loop
    have hlen : ma.length = mb.length := by
      have := congrArg sint.Z Hif; rw [hna, hnb] at this; omega
    rename_i k_ptr
    irename : k_ptr ↦ (zero_val w64) => Hk
    ihave HI : (∃ j kv : w64,
        "i" ∷ i_ptr ↦ j ∗
        "Hk" ∷ k_ptr ↦ kv ∗
        "HΦ" ∷ (True -∗ Φ #(decide (ma = mb))) ∗
        "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
        "a" ∷ a_ptr ↦ a ∗
        "b" ∷ b_ptr ↦ b ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ma.length ∧
          ma.take (sint.nat j) = mb.take (sint.nat j)⌝ : IProp GF) $$ [i Hk HΦ «$res0» a b]
    · iexists (W64 0), _
      iframe
      ipureintro; refine ⟨by decide, by simp, by simp [sint.nat]⟩
    wp_for HI
    have hjt : sint.Z j = j.toInt := rfl
    wp_if_destruct
    · -- an iteration
      rw [hna] at Hif
      have hjZ : sint.Z j = (sint.nat j : Int) := by
        simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
      have hjn : sint.nat j < ma.length := by omega
      obtain ⟨xa1, hxa1⟩ : ∃ x, xa[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨xb1, hxb1⟩ : ∃ x, xb[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ma1, hma1⟩ : ∃ m, ma[sint.nat j]? = some m := ⟨_, List.getElem?_eq_getElem hjn⟩
      obtain ⟨mb1, hmb1⟩ : ∃ m, mb[sint.nat j]? = some m := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave Hia := BigSepL2.bigSepL2_lookup hxa1 hma1 $$ Hxa
      ihave Hib := BigSepL2.bigSepL2_lookup hxb1 hmb1 $$ Hxb
      unfold inodeOwn
      icases Hia with ⟨%Hfa, #Hka, #Hva⟩
      icases Hib with ⟨%Hfb, #Hkb, #Hvb⟩
      icases ownSlice_elem_acc (sint.Z j) xa1 a _ xa Hj.1 hxa1 $$ Hsa with ⟨#Hea, -⟩
      icases ownSlice_elem_acc (sint.Z j) xb1 b _ xb Hj.1 hxb1 $$ Hsb with ⟨#Heb, -⟩
      icases typedPointsto_split _ _ _ $$ Hea with Hea'
      icases typedPointsto_split _ _ _ $$ Heb with Heb'
      simp only [TypedPointsto.typedPointstoDef]
      icases Hea' with ⟨Hfla, Hpga, Hkya, Hvla, -⟩
      icases Heb' with ⟨Hflb, Hpgb, Hkyb, Hvlb, -⟩
      have hb1 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z a.len := ⟨Hj.1, by omega⟩
      have hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z b.len := ⟨Hj.1, by omega⟩
      simp only [hb1, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index a (sint.Z j) xa DFrac.discard xa1 Hj.1 as -
      · isplitr
        · iexact Hsa
        · ipureintro; exact hxa1
      repeat (first | (simp only [hb1]; wp_auto) | (simp only [hb2]; wp_auto) | wp_auto)
      have hdiff : ∀ (P : Prop), (P → ma1 ≠ mb1) → P → decide (ma = mb) = false := by
        intro P hP hp; exact decide_eq_false (ne_of_getElem?_ne hma1 hmb1 (hP hp))
      wp_if_destruct
      · -- the flags agree
        have hfl := Hif
        repeat (first | (simp only [hb1]; wp_auto) | (simp only [hb2]; wp_auto) | wp_auto)
        wp_if_destruct
        · -- the page ids agree
          have hpg := Hif
          repeat (first | (simp only [hb1]; wp_auto) | (simp only [hb2]; wp_auto) | wp_auto)
          wp_apply (wp_Equal xa1.key' xb1.key' DFrac.discard DFrac.discard ma1.key mb1.key) as ⟨-, -⟩
          · isplitr
            · iexact Hka
            · iexact Hkb
          wp_if_destruct
          · -- the keys agree
            have hky := Hif
            repeat (first | (simp only [hb1]; wp_auto) | (simp only [hb2]; wp_auto) | wp_auto)
            wp_apply (wp_Equal xa1.value' xb1.value' DFrac.discard DFrac.discard ma1.value mb1.value)
              as ⟨-, -⟩
            · isplitr
              · iexact Hva
              · iexact Hvb
            wp_if_destruct
            · -- the values agree: the inodes are the same
              have hvl := Hif
              have e1 : ma1.flags = mb1.flags := by rw [← Hfa.1, ← Hfb.1]; exact hfl
              have e2 : ma1.pgid = mb1.pgid := by rw [← Hfa.2, ← Hfb.2]; exact hpg
              have heq : ma1 = mb1 := by
                cases ma1; cases mb1
                simp only at e1 e2 hky hvl
                simp only [e1, e2, hky, hvl]
              wp_for_post
              iexists (j + W64 1), j
              iframe
              ipureintro
              have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
                show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
                have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
                omega
              refine ⟨by word, by word, ?_⟩
              rw [hj1, take_succ_of_getElem? _ _ _ hma1, take_succ_of_getElem? _ _ _ hmb1, Hj.2.2, heq]
            · -- the values differ
              wp_for_post
              rw [hdiff _ (fun h e => h (by rw [e])) Hif]
              iapply HΦ
              itrivial
          · -- the keys differ
            wp_for_post
            rw [hdiff _ (fun h e => h (by rw [e])) Hif]
            iapply HΦ
            itrivial
        · -- the page ids differ
          wp_for_post
          rw [hdiff _ (fun h e => h (by rw [Hfa.2, Hfb.2, e])) Hif]
          iapply HΦ
          itrivial
      · -- the flags differ
        wp_for_post
        rw [hdiff _ (fun h e => h (by rw [Hfa.1, Hfb.1, e])) Hif]
        iapply HΦ
        itrivial
    · -- every inode agrees
      have hjn : sint.nat j = ma.length := by
        have := Hj.2.1; simp only [sint.nat]; omega
      have hd : decide (ma = mb) = true := by
        have h := Hj.2.2
        rw [hjn, List.take_of_length_le (Nat.le_refl _), hlen,
          List.take_of_length_le (Nat.le_refl _)] at h
        exact decide_eq_true h
      rw [hd]
      iapply HΦ
      itrivial
  · -- different lengths
    have : ¬ ma = mb := by
      intro h; apply Hif; apply BitVec.eq_of_toInt_eq
      show sint.Z a.len = sint.Z b.len
      rw [hna, hnb, h]
    rw [decide_eq_false this]
    iapply HΦ
    itrivial

end proof

end Perennial
