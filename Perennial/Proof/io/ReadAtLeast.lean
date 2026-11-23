/-
The proof of `io.ReadAtLeast`.
-/
module

public import Perennial.Spec.io.ReadAtLeast

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem io.ReadAtLeast.wp_proof :
    io.ReadAtLeast.spec (GF := GF) (hG := hG) := by
  intro ri Pre S E r0 p xs min eof ueof sb
  wp_start as ⟨#Hr, #Heof, #Hueof, #Hsb, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave %Hwf := ownSlice_wf $$ Hp
  -- `EOF`'s value is a `*errorString`
  ihave HEOF := io.eof_of_init $$ Hpkg
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  wp_auto
  wp_if_destruct
  · -- `len(buf) < min`: `ErrShortBuffer`
    iapply HΦ
    iexists []
    simp only [List.nil_append, List.drop_zero, List.append_nil, List.length_nil]
    iframe Hp HS
    isplit
    · ipureintro; exact ⟨by word, by omega⟩
    unfold io.readAtLeastRes
    ileft; ipureintro
    exact ⟨by word, rfl, rfl⟩
  have Hmin : sint.Z min ≤ (xs.length : Int) := by word
  ihave HI : (∃ (n : w64) (ev : GoInterface) (ys : List w8),
      "n" ∷ n_ptr ↦ n ∗ "err" ∷ err_ptr ↦ ev ∗
      "Hp" ∷ p ↦* (ys ++ xs.drop ys.length) ∗ "HS" ∷ S (r0 ++ ys) ∗
      "#Herr" ∷ io.errAt E (r0 ++ ys) ev ∗ "%Hty" ∷ ⌜io.ptrTyped ev⌝ ∗
      "%Hys" ∷ ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ : IProp GF) $$ [n err Hp HS]
  · iexists _, _, []
    simp only [List.nil_append, List.drop_zero, List.append_nil, List.length_nil]
    iframe
    isplit
    · unfold io.errAt; ileft; ipureintro; rfl
    ipureintro
    exact ⟨io.ptrTyped_nil, by simp only [zero_val, ZeroVal.zeroValDef]; word, by omega⟩
  wp_for HI
  wp_if_destruct
  · -- `n < min`
    rcases ev with ei | _
    rotate_left
    · -- `err == nil`: another `Read` of `buf[n:]`
      wp_auto
      simp only [decide_eq_true_eq, ↓reduceIte]
      wp_auto
      have Hb : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z p.len ∧ sint.Z p.len ≤ sint.Z p.cap := by
        refine ⟨by omega, by omega, ?_⟩; exact Hwf.2
      simp only [Hb, _root_.and_self, ↓reduceIte]
      ihave %Hlen' := ownSlice_len $$ Hp
      icases (ownSlice_split_all n p _ _ ⟨by omega, by omega⟩).1 $$ Hp with ⟨Hp1, Hp2⟩
      have Htk : (ys ++ xs.drop ys.length).take (sint.nat n) = ys := by
        rw [show sint.nat n = ys.length by word, List.take_left]
      have Hdr : (ys ++ xs.drop ys.length).drop (sint.nat n) = xs.drop ys.length := by
        rw [show sint.nat n = ys.length by word, List.drop_left]
      rw [Htk, Hdr]
      wp_auto
      wp_apply io.wp_reader_Read ri Pre S E (r0 ++ ys) _ (xs.drop ys.length)
          (by rw [List.length_drop]; exact Hpre ys (by omega)) $$ [Hp2 HS]
        as %nn %err' ⟨%zs, %Hzs, Hp2, HS, #Herr', %Hty'⟩
      · iframe Hr HS Hp2
      wp_for_post
      iframe
      iexists _, _, ys ++ zs
      rw [show r0 ++ (ys ++ zs) = r0 ++ ys ++ zs from (List.append_assoc _ _ _).symm]
      iframe
      iframe Herr'
      have Hzl : zs.length ≤ xs.length - ys.length := by
        rw [List.length_drop] at Hzs; exact Hzs.2
      isplitl [Hp1 Hp2]
      · have e := ownSlice_combine (GF := GF) (V := w8) n p (DFrac.own 1) ys (zs ++ (xs.drop ys.length).drop zs.length)
          (W64 0) p.len ⟨by word, by decide, by word, by word⟩
        rw [List.length_append, ← List.drop_drop]
        rw [← List.append_assoc] at e
        iapply ownSlice_trivial_slice_2
        iapply e $$ Hp1 Hp2
      ipureintro
      simp only [List.length_append]
      refine ⟨Hty', ?_, ?_⟩
      · have h2 : (xs.length : Int) = sint.Z p.len := by
          have h := Hlen.1; have h' := Hlen.2; rw [h]; word
        have : (ys.length + zs.length : Int) < 2 ^ 63 := by
          have : sint.Z p.len < 2 ^ 63 := by word
          omega
        word
      · omega
    · -- `err != nil`: the loop ends
      wp_auto
      simp only [decide_eq_true_eq, ↓reduceIte]
      rw [ite_eq_right (by intro h; have := go.intoVal_inj h; simp at this)]
      try wp_auto
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · -- `n > 0`: compare `err` with `EOF`
        try wp_auto
        by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l, hl⟩ := Hty ei _ rfl hty
          obtain ⟨ty, v⟩ := ei
          simp only at hty hl
          subst hty hl
          simp only [interface.mkOk, ↓reduceIte]
          wp_auto
          wp_if_destruct
          · iapply HΦ
            iexists ys
            iframe Hp HS
            isplit
            · ipureintro; exact Hys
            unfold io.readAtLeastRes io.errAt
            icases Herr with (%Hnil | #HE)
            · exfalso; cases Hnil
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            have hne : ys ≠ [] := by
              intro h; subst h; simp at Hys; word
            refine ⟨Hmin, by word, by simp, fun _ => rfl, fun h => absurd ⟨?_, hne⟩ h⟩
            simp only [Hif]
          · iapply HΦ
            iexists ys
            iframe Hp HS
            isplit
            · ipureintro; exact Hys
            unfold io.readAtLeastRes io.errAt
            icases Herr with (%Hnil | #HE)
            · exfalso; cases Hnil
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            refine ⟨Hmin, by word, by simp, fun h => absurd ?_ Hif, fun _ => rfl⟩
            obtain ⟨h1, -⟩ := h
            simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h1
            exact go.intoVal_inj h1.2
        · simp only [interface.mkOk, hty, ↓reduceIte]
          wp_auto
          iapply HΦ
          iexists ys
          iframe Hp HS
          isplit
          · ipureintro; exact Hys
          unfold io.readAtLeastRes io.errAt
          icases Herr with (%Hnil | #HE)
          · exfalso; cases Hnil
          iright; iright
          iexists (GoInterface.ok ei)
          iframe HE
          ipureintro
          refine ⟨Hmin, by word, by simp, fun h => absurd ?_ hty, fun _ => rfl⟩
          obtain ⟨h1, -⟩ := h
          simp only [GoInterface.ok.injEq] at h1
          rw [h1]
      · -- `n == 0`
        iapply HΦ
        iexists ys
        iframe Hp HS
        isplit
        · ipureintro; exact Hys
        unfold io.readAtLeastRes io.errAt
        icases Herr with (%Hnil | #HE)
        · exfalso; cases Hnil
        iright; iright
        iexists (GoInterface.ok ei)
        iframe HE
        ipureintro
        have hnil : ys = [] := by
          apply List.eq_nil_of_length_eq_zero; word
        refine ⟨Hmin, by word, by simp, fun h => absurd hnil h.2, fun _ => rfl⟩
  · -- `n >= min`: `nil`
    try simp only [decide_eq_true_eq, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · iapply HΦ
      iexists ys
      iframe Hp HS
      isplit
      · ipureintro; exact Hys
      unfold io.readAtLeastRes
      iright; ileft
      ipureintro
      exact ⟨Hmin, by word, rfl⟩
    · exfalso; word

end proof

end Perennial
