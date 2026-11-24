/-
The proof of `encoding/binary.ReadUvarint`.
-/
module

public import Perennial.Spec.encoding.binary.ReadUvarint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open encoding.binary in
theorem encoding.binary.ReadUvarint.wp_proof :
    encoding.binary.ReadUvarint.spec (GF := GF) (hG := hG) := fun ri S E r0 eof ueof ovf => by
  wp_start as ⟨#Hr, #Heof, #Hueof, #Hovf, HS⟩
  -- `EOF`'s value is a `*errorString`
  ihave HEOF := io.eof_of_init $$ Hpkg2
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  wp_auto
  -- the loop has read `V`, continuation bytes, and accumulated their value in `x`
  ihave HL : (∃ (iv xv sv : w64) (V : List w8),
      "i" ∷ i_ptr ↦ iv ∗ "x" ∷ x_ptr ↦ xv ∗ "s" ∷ s_ptr ↦ sv ∗
      "HS" ∷ S (r0 ++ V) ∗
      "%Hinv" ∷ ⌜sint.Z iv = V.length ∧ V.length ≤ 10 ∧ contBytes V ∧
        (V.length < 10 → xv = W64 (uvarintDec V)) ∧ sv = W64 (7 * V.length)⌝ : IProp GF)
      $$ [i x s HS]
  · iexists W64 0, W64 0, W64 0, []
    simp only [List.append_nil]
    iframe
    ipureintro
    refine ⟨rfl, by simp, by simp [contBytes], fun _ => rfl, rfl⟩
  wp_for HL
  obtain ⟨hiv, hl10, hcont, hx, rfl⟩ := Hinv
  wp_if_destruct
  · have hlt : V.length < 10 := by
      have : sint.Z (W64 10) = 10 := rfl
      omega
    wp_apply io.wp_byteReader_ReadByte ri S E (r0 ++ V) $$ [$Hr $HS]
      as %c %err (⟨%Hnil, HS⟩ | ⟨%Hne, #HE, %Hty, HS⟩)
    · subst Hnil
      wp_auto
      wp_if_destruct
      · -- the last byte
        have hc : c.toNat < 128 := by
          have : uint.Z (W8 128) = 128 := rfl
          simp only [uint.Z] at Hif this; omega
        try wp_auto
        wp_if_destruct
        · -- the tenth byte
          have hV9 : V.length = 9 := by
            have : sint.Z (W64 9) = 9 := rfl
            omega
          try wp_auto
          wp_if_destruct
          · -- above `1`: `errOverflow` (`varint.go:142-143`)
            wp_for_post
            iapply HΦ
            iexists V ++ [c]
            rw [← List.append_assoc]
            iframe HS
            unfold uvarintRes
            iright; ileft
            ipureintro
            refine ⟨rfl, V, c, rfl, hV9, hcont, ?_⟩
            have : uint.Z (W8 1) = 1 := rfl
            simp only [uint.Z] at Hif this; omega
          · -- at most `1`: the value (`varint.go:145`)
            wp_for_post
            iapply HΦ
            iexists V ++ [c]
            rw [← List.append_assoc]
            iframe HS
            unfold uvarintRes
            ileft
            ipureintro
            have hc1 : c.toNat ≤ 1 := by
              have : uint.Z (W8 1) = 1 := rfl
              simp only [uint.Z] at Hif this; omega
            refine ⟨rfl, ⟨V, c, rfl, hcont, hc, by omega, fun _ => hc1⟩, ?_⟩
            rw [hx hlt]
            exact uvarint_last_val V c hc (by omega) (fun _ => hc1)
        · -- the value (`varint.go:145`)
          have hV9 : V.length ≠ 9 := by
            intro h; apply Hif; rw [h] at hiv
            apply BitVec.eq_of_toInt_eq; exact hiv
          wp_for_post
          iapply HΦ
          iexists V ++ [c]
          rw [← List.append_assoc]
          iframe HS
          unfold uvarintRes
          ileft
          ipureintro
          refine ⟨rfl, ⟨V, c, rfl, hcont, hc, by omega, fun h => absurd h hV9⟩, ?_⟩
          rw [hx hlt]
          exact uvarint_last_val V c hc (by omega) (fun h => absurd h hV9)
      · -- a continuation byte (`varint.go:147-148`)
        have hc : 128 ≤ c.toNat := by
          have : uint.Z (W8 128) = 128 := rfl
          simp only [uint.Z] at Hif this; omega
        try wp_auto
        wp_for_post
        iframe
        iexists iv + W64 1, _, _, V ++ [c]
        rw [← List.append_assoc]
        iframe
        ipureintro
        have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
        refine ⟨by rw [hiv1, hiv]; simp, by simp; omega, ?_, ?_, ?_⟩
        · intro b hb
          rcases List.mem_append.1 hb with hb | hb
          · exact hcont b hb
          · simp at hb; subst hb; exact hc
        · intro hl
          simp only [List.length_append, List.length_singleton] at hl
          rw [hx hlt]
          exact uvarint_acc V c (by omega)
        · have h7 : ∀ x : Int, 0 ≤ x → x ≤ 9 → W64 (7 * x) + W64 7 = W64 (7 * (x + 1)) := by
            intros; word
          rw [List.length_append, List.length_singleton, h7 _ (by omega) (by omega)]
          push_cast; rfl
    · -- the reader's error (`varint.go:135-139`)
      obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok ei => exact ⟨ei, rfl⟩
      wp_auto
      wp_if_destruct
      · -- `i > 0`: compare `err` with `EOF`
        have hne : V ≠ [] := by
          intro h; subst h; simp at hiv; have : sint.Z (W64 0) = 0 := rfl; omega
        try wp_auto
        by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l, hl⟩ := Hty ei _ rfl hty
          obtain ⟨ty, v⟩ := ei
          simp only at hty hl
          subst hty hl
          simp only [interface.mkOk, ↓reduceIte]
          wp_auto
          wp_if_destruct
          · -- `EOF`: `ErrUnexpectedEOF`
            try wp_auto
            wp_for_post
            iapply HΦ
            iexists V
            iframe HS
            unfold uvarintRes
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            refine ⟨hlt, hcont, by simp, fun _ => rfl, fun h => absurd ⟨?_, hne⟩ h⟩
            simp only [Hif]
          · try wp_auto
            wp_for_post
            iapply HΦ
            iexists V
            iframe HS
            unfold uvarintRes
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            refine ⟨hlt, hcont, by simp, fun h => absurd ?_ Hif, fun _ => rfl⟩
            obtain ⟨h1, -⟩ := h
            simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h1
            exact go.intoVal_inj h1.2
        · simp only [interface.mkOk, hty, ↓reduceIte]
          try wp_auto
          wp_for_post
          iapply HΦ
          iexists V
          iframe HS
          unfold uvarintRes
          iright; iright
          iexists (GoInterface.ok ei)
          iframe HE
          ipureintro
          refine ⟨hlt, hcont, by simp, fun h => absurd ?_ hty, fun _ => rfl⟩
          obtain ⟨h1, -⟩ := h
          simp only [GoInterface.ok.injEq] at h1
          rw [h1]
      · -- `i == 0`: the reader's error as is
        have hnil : V = [] := by
          apply List.eq_nil_of_length_eq_zero
          have : sint.Z (W64 0) = 0 := rfl
          omega
        try wp_auto
        wp_for_post
        iapply HΦ
        iexists V
        iframe HS
        unfold uvarintRes
        iright; iright
        iexists (GoInterface.ok ei)
        iframe HE
        ipureintro
        exact ⟨hlt, hcont, by simp, fun h => absurd hnil h.2, fun _ => rfl⟩
  · -- ten continuation bytes: `errOverflow` (`varint.go:150`)
    have h10 : V.length = 10 := by
      have : sint.Z (W64 10) = 10 := rfl
      omega
    iapply HΦ
    iexists V
    iframe HS
    unfold uvarintRes
    iright; ileft
    ipureintro
    refine ⟨rfl, ?_⟩
    rcases List.eq_nil_or_concat V with h | ⟨V', c, rfl⟩
    · subst h; simp at h10
    · simp only [List.concat_eq_append, List.length_append, List.length_singleton] at h10 hcont ⊢
      refine ⟨V', c, rfl, by omega, fun b hb => hcont b (by simp [hb]), ?_⟩
      have := hcont c (by simp)
      omega

end proof

end Perennial
