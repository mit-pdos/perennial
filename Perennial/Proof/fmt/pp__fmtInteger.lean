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

/-- The flags, width and precision of an integer directive (`Mod.IntOk`) are in
`fmt.fmtInteger`'s precondition, and its output is `Mod.intOut`. -/
theorem fmt.Mod_intOk [GooseExts] (md : fmt.Mod) (verb : w8) (h : md.IntOk verb) :
    md.flags.sharp' = false ∧ md.flags.plus' = false ∧ md.flags.space' = false ∧
    md.flags.minus' = false ∧ md.flags.sharpV' = false ∧
    (md.flags.precPresent' = true → md.flags.widPresent' = false ∧ md.wid = W64 0 ∧
      0 ≤ sint.Z md.precW ∧ sint.Z md.precW ≤ 1000000) ∧
    (md.flags.widPresent' = true → md.flags.zero' = true ∧ 0 ≤ sint.Z md.wid ∧
      sint.Z md.wid ≤ 1000000 ∧ md.precW = W64 0) ∧
    ∀ z : Int, (if md.flags.precPresent' then
        fmt.precPad (fmt.verbBase verb) (decide (verb = fmt.verb_X)) (sint.nat md.precW) z
      else fmt.widthPad (fmt.verbBase verb) (decide (verb = fmt.verb_X))
        (if md.flags.widPresent' then sint.nat md.wid else 0) z) = md.intOut verb z := by
  cases md with
  | width zw =>
    obtain ⟨-, hzw⟩ := h
    cases zw with
    | none =>
      simp [fmt.Mod.flags, fmt.dirFlags, fmt.noFlags, fmt.Mod.intOut, fmt.Mod.wid, fmt.Mod.precW]
    | some n =>
      obtain ⟨h1, h2⟩ := hzw
      have h : sint.Z (W64 (n : Int)) = n := by word
      have h' : sint.nat (W64 (n : Int)) = n := by word
      simp only [fmt.Mod.flags, fmt.Mod.wid, fmt.Mod.precW, fmt.Mod.intOut, fmt.dirFlags,
        fmt.noFlags, fmt.dirWid, Option.getD_some, ↓reduceIte, true_implies, true_and, and_true,
        h, h', Bool.false_eq_true, false_implies, implies_true]
      omega
  | prec p =>
    obtain ⟨-, hp⟩ := h
    have h : sint.Z (W64 (p : Int)) = p := by word
    have h' : sint.nat (W64 (p : Int)) = p := by word
    simp only [fmt.Mod.flags, fmt.Mod.wid, fmt.Mod.precW, fmt.Mod.intOut, fmt.noFlags,
      ↓reduceIte, true_implies, true_and, and_true, h, h', Bool.false_eq_true, false_implies,
      implies_true]
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
  fun p x bs md v isSigned verb hok => by
  obtain ⟨hsh, hpl, hsp, hmi, hsV, hprecP, hwid, hout⟩ := fmt.Mod_intOk md verb hok
  have hv : verb = fmt.verb_d ∨ verb = fmt.verb_v ∨ verb = fmt.verb_x ∨ verb = fmt.verb_X := by
    cases md with
    | width zw => rcases hok.1 with h | h | h <;> simp [h]
    | prec p => exact hok.1
  rcases hv with rfl | rfl | rfl | rfl
  all_goals
    wp_start as Hp
    unfold fmt.isPrinterA
    icases Hp with ⟨Hb, Hf, Hib, Hrest⟩
    unfold fmt.fmtOwn
    icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
    wp_auto
  · rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) md.flags md.wid md.precW
      bs v (W64 10) isSigned (W32 ((100 : Nat) : Int)) false (Or.inl rfl)
      (by decide) hsh hpl hsp hmi hprecP hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [← hout, show fmt.verbBase fmt.verb_d = uint.nat (W64 10) by decide,
      show decide (fmt.verb_d = fmt.verb_X) = false by decide]
    unfold fmt.fmtOwn
    iframe
  · rw [hsV]
    wp_auto
    rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) md.flags md.wid md.precW
      bs v (W64 10) isSigned (W32 ((118 : Nat) : Int)) false (Or.inl rfl)
      (by decide) hsh hpl hsp hmi hprecP hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [← hout, show fmt.verbBase fmt.verb_v = uint.nat (W64 10) by decide,
      show decide (fmt.verb_v = fmt.verb_X) = false by decide]
    unfold fmt.fmtOwn
    iframe
  · rw [show ldigits = #(fmt.hexDigits false) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) md.flags md.wid md.precW
      bs v (W64 16) isSigned (W32 ((120 : Nat) : Int)) false (Or.inr rfl)
      (by decide) hsh hpl hsp hmi hprecP hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [← hout, show fmt.verbBase fmt.verb_x = uint.nat (W64 16) by decide,
      show decide (fmt.verb_x = fmt.verb_X) = false by decide]
    unfold fmt.fmtOwn
    iframe
  · rw [show udigits = #(fmt.hexDigits true) from rfl]
    wp_apply wp_fmtInteger (p.[fmt.pp, go!"fmt"]) (p.[fmt.pp, go!"buf"]) md.flags md.wid md.precW
      bs v (W64 16) isSigned (W32 ((88 : Nat) : Int)) true (Or.inr rfl)
      (by decide) hsh hpl hsp hmi hprecP hwid $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
    · unfold fmt.fmtOwn; iframe
    iapply HΦ
    rw [← hout, show fmt.verbBase fmt.verb_X = uint.nat (W64 16) by decide,
      show decide (fmt.verb_X = fmt.verb_X) = true by decide]
    unfold fmt.fmtOwn
    iframe

end proof

end Perennial
