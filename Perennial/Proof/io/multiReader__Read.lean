/-
The proof of `multiReader__Read`.
-/
module

public import Perennial.Spec.io.multiReader__Read

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

theorem io.multiReader.Read.wp_proof :
    io.multiReader.Read.spec (GF := GF) (hG := hG) :=
  fun Out cs eof l r p xs hOut hty => by
  wp_start as ⟨#Heof, #Hrs, HS, Hp⟩
  ihave HEOF := io.eof_of_init $$ Hpkg
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  unfold io.mrState
  icases HS with ⟨%done, %rem, %sl, %cur, %Hcs, Hl, Hsl, #Hdone, Hcur⟩
  wp_auto
  ihave HI : (∃ (done : List (io.ReaderC GF × List w8)) (rem : List (io.ReaderC GF))
      (sl : GoSlice) (cur c0 : List w8) (nv : w64) (ev : GoInterface),
      "Hl" ∷ l ↦ ({ readers' := sl } : io.multiReader) ∗ "Hsl" ∷ sl ↦* rem.map io.ReaderC.iface ∗
      "#Hdone" ∷ io.mrDone done (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof) ∗
      "Hcur" ∷ io.mrCur rem cur ∗ "Hp" ∷ p ↦* c0 ∗ "n" ∷ n_ptr ↦ nv ∗ "err" ∷ err_ptr ↦ ev ∗
      "%Hinv" ∷ ⌜cs = done.map Prod.fst ++ rem ∧ r = (done.map Prod.snd).flatten ++ cur ∧
        Out xs [] c0⌝ : IProp GF) $$ [Hl Hsl Hcur Hp n err]
  · iexists done, rem, sl, cur, xs, _, _
    iframe Hl Hsl Hdone Hcur Hp n err
    ipureintro; exact ⟨Hcs.1, Hcs.2, hOut.refl xs⟩
  iclear Hdone
  wp_for HI
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hwf := ownSlice_wf $$ Hsl
  obtain ⟨Hcs1, Hr1, Hc0⟩ := Hinv
  have hl : (rem.length : Int) = sint.Z sl.len := by
    have := Hlen.1; have := Hlen.2
    simp only [List.length_map] at *; unfold sint.nat at *; unfold sint.Z at *; omega
  rcases rem with _ | ⟨c, rest⟩
  · -- every reader has returned `EOF`: `0, EOF`
    have h0 : sint.Z sl.len = 0 := by simp at hl; omega
    wp_if_destruct
    · exfalso; rw [h0] at Hif; simp at Hif
    iapply HΦ
    iexists [], c0
    rw [io.mrCur_nil]
    icases Hcur with %hcur
    subst hcur
    simp only [List.append_nil, List.length_nil]
    iframe Hp
    isplitr
    · ipureintro; exact ⟨by simp, by simp, Hc0⟩
    isplitl [Hl Hsl]
    · iexists done, [], sl, []
      iframe Hl Hsl Hdone
      isplitr
      · ipureintro; exact ⟨Hcs1, by simp [Hr1]⟩
      rw [io.mrCur_nil]; ipureintro; rfl
    isplitl
    · unfold io.errAt; iright; imodintro
      unfold io.mrErr; iright
      iexists done
      iframe Hdone
      ipureintro; exact ⟨rfl, by simpa using Hcs1, by simp [Hr1]⟩
    · ipureintro
      intro ii T h1 h2
      simp only [interface.mkOk, GoInterface.ok.injEq] at h1
      subst h1
      exact ⟨xeof, rfl⟩
  have hpos : 0 < sint.Z sl.len := by simp at hl; omega
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; word
  have hmem : c ∈ cs := by rw [Hcs1]; simp
  have htyc := hty c hmem
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := ⟨by word, hpos⟩
  wp_join with [mr Hl Hsl]
  · simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ _ c.iface (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    simp only [htyc, ↓reduceIte, _root_.decide_false]
    wp_auto
    wp_join_done
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ _ c.iface (by word) $$ [Hsl] as Hsl
  · iframe; ipureintro; rfl
  ihave #Hc := Hrs $$ %c %hmem
  rw [io.mrCur_cons]
  icases Hcur with ⟨HSc, Hrest⟩
  unfold io.readerOkOut
  wp_apply Hc $$ %cur %p %c0 [HSc Hp] as %nn %err' ⟨%ys, %c1, %Hys, Hp, HSc, #Herr, %Hty⟩
  · iframe
  have hyl : ys.length ≤ xs.length := by
    have := hOut.len xs c0 Hc0; omega
  have hOutc : Out xs ys c1 := hOut.comp _ _ _ _ Hc0 Hys.2.2
  by_cases hE : err' = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof
  · subst hE
    simp only [interface.mkOk, ↓reduceIte]
    wp_auto
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index (V := GoInterface) sl (sint.Z (W64 0)) _ _ $$ [Hsl] as Hsl
    · iframe; ipureintro; simp
    ihave %Hwf' := ownSlice_wf $$ Hsl
    have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len := ⟨by word, by word⟩
    icases (ownSlice_split_all (W64 1) sl _ _ hb1).1 $$ Hsl with ⟨-, Hsl⟩
    have hdrop : List.drop (sint.nat (W64 1))
        ((List.map io.ReaderC.iface (c :: rest)).set 0
          (interface.mkOk io.eofReader.ty #(io.eofReader.mk))) = rest.map io.ReaderC.iface := by
      rfl
    rw [hdrop]
    have hb2 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap :=
      ⟨hb1.1, hb1.2, Hwf.2⟩
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave %Hlen' := ownSlice_len $$ Hsl
    iunfold io.errAt at Herr
    icases Herr with (%h | #HE)
    · exfalso; cases h
    ihave #Hdone' := io.mrDone_snoc done c (cur ++ ys) _ $$ [Hdone HE]
    · iframe Hdone HE
    have Hcs' : cs = List.map Prod.fst (done ++ [(c, cur ++ ys)]) ++ rest := by simp [Hcs1]
    have Hr' : r ++ ys = (List.map Prod.snd (done ++ [(c, cur ++ ys)])).flatten ++ [] := by
      simp [Hr1]
    ihave Hcur' := io.mrCur_init rest $$ Hrest
    wp_if_destruct
    · -- `n > 0`: return it, with `EOF` only if no reader is left
      have hpt : io.ptrTyped (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof) := by
        intro ii T h1 h2
        simp only [interface.mkOk, GoInterface.ok.injEq] at h1
        subst h1
        exact ⟨xeof, rfl⟩
      wp_if_destruct
      · -- readers remain: `nil`
        wp_for_post
        iapply HΦ
        iexists ys, c1
        iframe Hp
        isplitr
        · ipureintro; exact ⟨Hys.1, hyl, hOutc⟩
        isplitl [Hl Hsl Hcur']
        · iexists _, rest, _, []
          iframe Hl Hsl Hdone' Hcur'
          ipureintro; exact ⟨Hcs', Hr'⟩
        isplitl
        · unfold io.errAt; ileft; ipureintro; rfl
        · ipureintro; exact io.ptrTyped_nil
      · -- the last reader: `EOF`
        have hrest : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          have h1 : sint.Z (sl.len - W64 1) = sint.Z sl.len - 1 := by word
          have h2 : sint.Z (W64 0) = 0 := by word
          simp only [List.length_cons] at hl
          omega
        subst hrest
        wp_for_post
        iapply HΦ
        iexists ys, c1
        iframe Hp
        isplitr
        · ipureintro; exact ⟨Hys.1, hyl, hOutc⟩
        isplitl [Hl Hsl Hcur']
        · iexists _, [], _, []
          iframe Hl Hsl Hdone' Hcur'
          ipureintro; exact ⟨Hcs', Hr'⟩
        isplitl
        · unfold io.errAt; iright; imodintro
          unfold io.mrErr; iright
          iexists (done ++ [(c, cur ++ ys)])
          iframe Hdone'
          ipureintro; exact ⟨rfl, by simpa using Hcs', by simpa using Hr'⟩
        · ipureintro; exact hpt
    · -- `0, EOF`: the next reader
      have hys0 : ys = [] := by
        apply List.eq_nil_of_length_eq_zero; have := Hys.1; word
      subst hys0
      wp_for_post
      iframe
      iexists _, rest, _, [], c1, _, _
      iframe Hl Hsl Hdone' Hcur' Hp n err
      ipureintro
      exact ⟨Hcs', by simpa using Hr', hOutc⟩
  · -- an error other than `EOF` (or `nil`): returned as is
    ihave Hpost : (∃ (done : List (io.ReaderC GF × List w8)) (rem : List (io.ReaderC GF))
        (sl : GoSlice) (cur : List w8),
        ⌜cs = done.map Prod.fst ++ rem ∧ r ++ ys = (done.map Prod.snd).flatten ++ cur⌝ ∗
        l ↦ ({ readers' := sl } : io.multiReader) ∗ sl ↦* rem.map io.ReaderC.iface ∗
        io.mrDone done (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof) ∗
        io.mrCur rem cur : IProp GF) $$ [Hl Hsl HSc Hrest]
    · iexists done, c :: rest, sl, cur ++ ys
      rw [io.mrCur_cons]
      iframe Hl Hsl HSc Hrest Hdone
      ipureintro; exact ⟨Hcs1, by simp [Hr1]⟩
    ihave #Herr' : io.errAt (io.mrErr cs (interface.mkOk (go.GoType.PointerType errors.errorString.ty)
        #xeof)) (r ++ ys) err' $$ []
    · iunfold io.errAt at Herr
      unfold io.errAt
      icases Herr with (%h | #HE)
      · ileft; ipureintro; exact h
      · iright; imodintro
        unfold io.mrErr; ileft
        iexists done, c, rest, cur ++ ys
        iframe Hdone HE
        ipureintro; exact ⟨hE, Hcs1, by simp [Hr1]⟩
    have hne : ∀ (ety : go.GoType) (v : val), err' = GoInterface.ok ⟨ety, v⟩ →
        ety = go.GoType.PointerType errors.errorString.ty → ∃ l', v = #l' ∧ l' ≠ xeof := by
      intro ety v h1 h2
      obtain ⟨l', hl'⟩ := Hty ⟨ety, v⟩ errors.errorString.ty h1 h2
      subst h1 h2
      refine ⟨l', hl', ?_⟩
      rintro rfl
      simp only at hl'
      apply hE; rw [hl']
    rcases err' with ⟨⟨ety, ev'⟩⟩ | _
    · by_cases hety : ety = go.GoType.PointerType errors.errorString.ty
      · obtain ⟨l', hv, hl'⟩ := hne ety ev' rfl hety
        subst hety hv
        simp only [interface.mkOk, ↓reduceIte]
        wp_auto
        all_goals (try simp only [hl', _root_.decide_false])
        all_goals (try wp_auto)
        all_goals (try simp only [hl', _root_.decide_false])
        all_goals (try wp_auto)
        all_goals (try wp_if_destruct)
        all_goals (try simp only [hl', _root_.decide_false])
        all_goals (try wp_auto)
        all_goals (try simp only [hl', _root_.decide_false])
        all_goals (try wp_auto)
        all_goals (try simp only [hl', _root_.decide_false])
        all_goals (try wp_auto)
        all_goals
          wp_for_post
          iapply HΦ
          iexists ys, c1
          iframe Hp Hpost Herr'
          ipureintro
          exact ⟨⟨Hys.1, hyl, hOutc⟩, Hty⟩
      · simp only [interface.mkOk, hety]
        wp_auto
        all_goals (try simp only [hety, ↓reduceIte])
        all_goals (try wp_auto)
        all_goals (try simp only [hety, ↓reduceIte])
        all_goals (try wp_auto)
        all_goals (try wp_if_destruct)
        all_goals (try simp only [hety, ↓reduceIte])
        all_goals (try wp_auto)
        all_goals (try simp only [hety, ↓reduceIte])
        all_goals (try wp_auto)
        all_goals (try simp only [hety, ↓reduceIte])
        all_goals (try wp_auto)
        all_goals
          wp_for_post
          iapply HΦ
          iexists ys, c1
          iframe Hp Hpost Herr'
          ipureintro
          exact ⟨⟨Hys.1, hyl, hOutc⟩, Hty⟩
    · simp only [interface.mkOk]
      wp_auto
      wp_if_destruct
      all_goals (try wp_auto)
      all_goals
        wp_for_post
        iapply HΦ
        iexists ys, c1
        iframe Hp Hpost Herr'
        ipureintro
        exact ⟨⟨Hys.1, hyl, hOutc⟩, Hty⟩

end proof

end Perennial
