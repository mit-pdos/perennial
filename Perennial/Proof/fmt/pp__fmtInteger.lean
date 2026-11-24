/-
The proof of `fmt.(*pp).fmtInteger`.
-/
module

public import Perennial.Spec.fmt.pp__fmtInteger
public import Perennial.Spec.fmt.fmt__fmtInteger

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure
variable [GooseExts]

/-- The flags of `%verb` and `%0Nverb` are in `fmt.fmtInteger`'s precondition. -/
theorem fmt.dirFlags_int (zw : Option Nat) (hzw : fmt.ZeroWidthOk zw) :
    (fmt.dirFlags zw).sharp' = false ∧ (fmt.dirFlags zw).plus' = false ∧
    (fmt.dirFlags zw).space' = false ∧ (fmt.dirFlags zw).minus' = false ∧
    (fmt.dirFlags zw).precPresent' = false ∧ (fmt.dirFlags zw).sharpV' = false ∧
    ((fmt.dirFlags zw).widPresent' = true → (fmt.dirFlags zw).zero' = true ∧
      0 ≤ sint.Z (fmt.dirWid zw) ∧ sint.Z (fmt.dirWid zw) ≤ 1000000 ∧ W64 0 = W64 0) ∧
    (if (fmt.dirFlags zw).widPresent' then sint.nat (fmt.dirWid zw) else 0) = zw.getD 0 := by
  cases zw with
  | none => simp [fmt.dirFlags, fmt.noFlags]
  | some n =>
    obtain ⟨h1, h2⟩ := hzw
    have h : sint.Z (W64 (n : Int)) = n := by word
    have h' : sint.nat (W64 (n : Int)) = n := by word
    simp only [fmt.dirFlags, fmt.noFlags, fmt.dirWid, Option.getD_some, ↓reduceIte, true_implies,
      true_and, and_true, h, h']
    omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.fmtInteger.wp_proof
    (wp_fmtInteger : fmt.fmt.fmtInteger.spec (GF := GF) (hG := hG)) :
    fmt.pp.fmtInteger.spec (GF := GF) (hG := hG) :=
  fun p x bs zw v isSigned verb hverb hzw => by
  obtain ⟨hsh, hpl, hsp, hmi, hpp, hsV, hwid, hout⟩ := fmt.dirFlags_int zw hzw
  rcases hverb with rfl | rfl | rfl
  all_goals
    wp_start as Hp
    unfold fmt.isPrinterA
    icases Hp with ⟨Hb, Hf, Hib, Hrest⟩
    unfold fmt.fmtOwn
    icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
    wp_auto
  · rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) (fmt.dirFlags zw)
      (fmt.dirWid zw) (W64 0) bs v (W64 10) isSigned (W32 ((100 : Nat) : Int)) (Or.inl rfl) (by decide)
      hsh hpl hsp hmi hpp hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [hout, show (if fmt.verb_d = fmt.verb_x then 16 else 10) = uint.nat (W64 10) by decide]
    unfold fmt.fmtOwn
    iframe
  · rw [hsV]
    wp_auto
    rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) (fmt.dirFlags zw)
      (fmt.dirWid zw) (W64 0) bs v (W64 10) isSigned (W32 ((118 : Nat) : Int)) (Or.inl rfl) (by decide)
      hsh hpl hsp hmi hpp hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [hout, show (if fmt.verb_v = fmt.verb_x then 16 else 10) = uint.nat (W64 10) by decide]
    unfold fmt.fmtOwn
    iframe
  · rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) (fmt.dirFlags zw)
      (fmt.dirWid zw) (W64 0) bs v (W64 16) isSigned (W32 ((120 : Nat) : Int)) (Or.inr rfl) (by decide)
      hsh hpl hsp hmi hpp hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [hout, show (if fmt.verb_x = fmt.verb_x then 16 else 10) = uint.nat (W64 16) by decide]
    unfold fmt.fmtOwn
    iframe

end proof

end Perennial
