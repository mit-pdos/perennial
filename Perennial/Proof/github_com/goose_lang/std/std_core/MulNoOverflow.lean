/-
The proof of `github.com/goose-lang/std/std_core.MulNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.MulNoOverflow

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

theorem github_com.goose_lang.std.std_core.MulNoOverflow.wp_proof :
    github_com.goose_lang.std.std_core.MulNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start as _
  wp_auto
  wp_if_destruct
  · rw [decide_eq_true (by simp [uint.Z])]
    iapply HΦ; itrivial
  · have Hx := Hif
    wp_if_destruct
    · rw [decide_eq_true (by simp [uint.Z])]
      iapply HΦ; itrivial
    · rw [if_neg (show ¬ uint.Z y = 0 from fun h => Hif (by word))]
      wp_auto
      have hx : uint.Z x ≠ 0 := fun h => Hx (by word)
      have h : (uint.Z x ≤ uint.Z (W64 18446744073709551615 / y)) ↔
          (uint.Z (x * y) = uint.Z x * uint.Z y) := by
        have hy : uint.Z y ≠ 0 := fun h => Hif (by word)
        have hc := mul_overflow_check_correct x y hx hy
        rw [word.unsigned_mul, word.unsigned_divu, show uint.Z (W64 18446744073709551615) = 2 ^ 64 - 1 from rfl]
        have ha := uint_Z_nonneg x
        have hb := uint_Z_nonneg y
        generalize uint.Z x = a at *
        generalize uint.Z y = b at *
        have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
        generalize a * b = P at *
        generalize (2 ^ 64 - 1) / b = Q at *
        constructor
        · intro h1; exact Int.emod_eq_of_lt hab (by omega)
        · intro h1
          have : P < 2 ^ 64 := by
            have := Int.emod_lt_of_pos P (show (0:Int) < 2 ^ 64 by decide); omega
          omega
      rw [decide_eq_decide.mpr h]
      iapply HΦ; itrivial

end proof

end Perennial
