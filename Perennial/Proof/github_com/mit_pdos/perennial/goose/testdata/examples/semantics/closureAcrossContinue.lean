/-
The proof of `closureAcrossContinue` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.closureAcrossContinue

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section defs
variable [GooseExts] [GoGlobalContext]

/-- The closure `func() uint64 { return i }` over the iteration variable at `q`. -/
def github_com.mit_pdos.perennial.goose.testdata.examples.semantics.closureAcrossContinue.clo
    (q : Loc) : GoFunc :=
  func.mk BAnon BAnon gl(let: "$res0" := (GoAlloc go.uint64) ((GoZeroVal go.uint64) #()) in
    exceptionDo (let: "$r0" := ![go.uint64] #q in do: "$res0" <-[go.uint64] "$r0" ;;; return: #()) ;;
    ![go.uint64] "$res0")

end defs


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.closureAcrossContinue.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.closureAcrossContinue.spec (GF := GF) (hG := hG) := by
  have clo_val : ∀ q : Loc, (#(clo q) : val) =
      glv(λ: <>, let: "$res0" := (GoAlloc go.uint64) ((GoZeroVal go.uint64) #()) in
        exceptionDo (let: "$r0" := ![go.uint64] #q in do: "$res0" <-[go.uint64] "$r0" ;;; return: #()) ;;
        ![go.uint64] "$res0") := by
    intro q; rw [go.intoVal_unfold GoFunc]; rfl
  wp_start
  wp_auto
  ihave HI : (∃ (p : Loc) (i : w64) (sl : GoSlice) (fvs : List GoFunc),
      "Hcell" ∷ «$iter_i_ptr» ↦ p ∗
      "Hp" ∷ p ↦ i ∗
      "fs" ∷ fs_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* fvs ∗
      "Hcap" ∷ ownSliceCap GoFunc sl (DFrac.own 1) ∗
      "%Hi" ∷ ⌜uint.Z i ≤ 4⌝ ∗
      "Hf" ∷ (⌜uint.Z i ≤ 1 ∧ fvs = []⌝ ∨
        (∃ q1 : Loc, q1 ↦ W64 1 ∗ ⌜2 ≤ uint.Z i ∧ uint.Z i ≤ 3 ∧ fvs = [clo q1]⌝) ∨
        (∃ q1 q3 : Loc, q1 ↦ W64 1 ∗ q3 ↦ W64 3 ∗ ⌜uint.Z i = 4 ∧ fvs = [clo q1, clo q3]⌝))
      : IProp GF) $$ [«$iter_i» i fs]
  · iexists _, _, slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; decide
    · ileft; ipureintro; exact ⟨by decide, rfl⟩
  wp_for HI
  wp_if_destruct
  · wp_for
    wp_if_destruct
    · wp_apply wp_slice_literal (V := GoFunc) [clo p]
      rw [← clo_val p]
      wp_auto
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      try wp_auto
      wp_for_post
      wp_for_post
      iframe
      iexists i_ptr, i + W64 1, sl', fvs ++ [clo p]
      iframe
      isplitr
      · ipureintro; word
      icases Hf with (%Hf | ⟨%q1, Hq1, %Hf⟩ | ⟨%q1, %q3, Hq1, Hq3, %Hf⟩)
      · have : i = W64 1 := by word
        subst this
        iright; ileft
        iexists p
        rw [Hf.2]
        iframe
        ipureintro; exact ⟨by decide, by decide, rfl⟩
      · have : i = W64 3 := by word
        subst this
        iright; iright
        iexists q1, p
        iframe
        ipureintro; exact ⟨by decide, by rw [Hf.2.2]; rfl⟩
      · exfalso; word
    · wp_for_post
      wp_for_post
      iframe
      iexists i_ptr, i + W64 1, sl, fvs
      iframe
      isplitr
      · ipureintro; word
      icases Hf with (%Hf | ⟨%q1, Hq1, %Hf⟩ | ⟨%q1, %q3, Hq1, Hq3, %Hf⟩)
      · ileft; ipureintro; exact ⟨by word, Hf.2⟩
      · iright; ileft
        iexists q1
        iframe
        ipureintro; exact ⟨by word, by word, Hf.2.2⟩
      · exfalso; word
  · icases Hf with (%Hf | ⟨%q1, Hq1, %Hf⟩ | ⟨%q1, %q3, Hq1, Hq3, %Hf⟩)
    · exfalso; word
    · exfalso; word
    obtain ⟨-, rfl⟩ := Hf
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave HK : (∃ (k s : w64) (fv : GoFunc),
        "i" ∷ i_ptr ↦ k ∗
        "sum" ∷ sum_ptr ↦ s ∗
        "f" ∷ f_ptr ↦ fv ∗
        "%Hk" ∷ ⌜(k = W64 0 ∧ s = W64 0) ∨ (k = W64 1 ∧ s = W64 1) ∨ (k = W64 2 ∧ s = W64 4)⌝
        : IProp GF) $$ [i sum f]
    · iexists _, _, _
      iframe
      ipureintro; left; exact ⟨rfl, rfl⟩
    wp_for HK
    have hlen : sint.Z sl.len = 2 := by
      have := Hlen.1; simp only [List.length_cons, List.length_nil] at this; word
    rw [hlen]
    rcases Hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [show sint.Z (W64 0) < 2 by decide, _root_.decide_true, ite_true]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen]; decide⟩)]
      wp_apply wp_load_slice_index _ _ _ _ (clo q1) (by decide) $$ [Hsl] with Hsl
      · iframe; ipureintro; rfl
      rw [clo_val]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; right; left; exact ⟨rfl, rfl⟩
    · simp only [show sint.Z (W64 1) < 2 by decide, _root_.decide_true, ite_true]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen]; decide⟩)]
      wp_apply wp_load_slice_index _ _ _ _ (clo q3) (by decide) $$ [Hsl] with Hsl
      · iframe; ipureintro; rfl
      rw [clo_val]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; right; right; exact ⟨rfl, rfl⟩
    · simp only [show ¬ sint.Z (W64 2) < 2 by decide, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      wp_auto
      iapply HΦ
      iexact Hpre

end proof

end Perennial
