/-
The proof of `math.pow`: `Pow(1/x, -y)` (for `x = -Inf`) calls `pow` again, so the proof is by Löb
induction (`iloeb`), unfolding `Pow` at that call.
-/
module

public import Perennial.Spec.math.pow_
public import Perennial.Spec.math.IsNaN
public import Perennial.Spec.math.NaN
public import Perennial.Spec.math.Signbit
public import Perennial.Spec.math.isOddInt
public import Perennial.Spec.math.Inf
public import Perennial.Spec.math.IsInf
public import Perennial.Spec.math.Abs
public import Perennial.Spec.math.Sqrt
public import Perennial.Spec.math.Modf
public import Perennial.Spec.math.Exp
public import Perennial.Spec.math.Log
public import Perennial.Spec.math.Frexp
public import Perennial.Spec.math.Ldexp
public import Perennial.Golang.Theory.Float

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

/-- The Löb induction hypothesis of `math.pow.wp_proof`, under an opaque name so that the proof's
automation leaves it alone until the recursive call. -/
def math.powHide (P : IProp GF) : IProp GF := P

theorem math.powHide_intro {P Q : IProp GF} : (□ math.powHide P -∗ Q) ⊢ (□ P -∗ Q) := .rfl

theorem math.powHide_elim {P Q : IProp GF} : (□ P -∗ Q) ⊢ (□ math.powHide P -∗ Q) := .rfl

set_option hygiene false in
/-- The steps of `math.pow.wp_proof`: every call by its spec (and the recursive `Pow` by the
induction hypothesis), every float operation, every `if` split, the end of a loop iteration, and
the end of a case of the `switch` (the `wp_join` below). -/
local macro "pow_steps" : tactic => `(tactic| repeat' (first
    | wp_end
    | (wp_apply wp_IsNaN; (try wp_auto))
    | (wp_apply wp_NaN; (try wp_auto))
    | (wp_apply wp_Signbit as %_ -; (try wp_auto))
    | (wp_apply wp_isOddInt as %_ -; (try wp_auto))
    | (wp_apply wp_Inf as %_ -; (try wp_auto))
    | (wp_apply wp_IsInf as %_ -; (try wp_auto))
    | (wp_apply wp_Abs; (try wp_auto))
    | (wp_apply wp_Sqrt as %_ -; (try wp_auto))
    | (wp_apply wp_Modf as %_ %_ -; (try wp_auto))
    | (wp_apply wp_Exp as %_ -; (try wp_auto))
    | (wp_apply wp_Log as %_ -; (try wp_auto))
    | (wp_apply wp_Frexp as %_ %_ -; (try wp_auto))
    | (wp_apply wp_Ldexp as %_ -; (try wp_auto))
    | (wp_apply wp_float64_add as %_ -; (try wp_auto))
    | (wp_apply wp_float64_sub as %_ -; (try wp_auto))
    | (wp_apply wp_float64_mul as %_ -; (try wp_auto))
    | (wp_apply wp_float64_div as %_ -; (try wp_auto))
    | (wp_apply wp_float64_neg as %_ -; (try wp_auto))
    | (wp_apply wp_ArbitraryInt as %_ -; (try wp_auto))
    | (wp_func_call; irevert IH; iapply math.powHide_elim; (iintro #IH); wp_call; (try wp_auto); wp_apply IH as %_ -; (try wp_auto))
    | (wp_for_post; iframe; iexists _, _, _, _, _; iframe)
    | wp_for_post
    | (iexists _, _, _; iframe; done)
    | (isplitr; (ipureintro; rfl); iexists _, _, _; iframe; done)
    | (iexists _; iframe; (try (ipureintro; simp)); done)
    | wp_auto
    | wp_if_destruct
    | (wp_if_bool; wp_if_destruct)
    | (exfalso; exact Hif trivial)))

set_option maxHeartbeats 2000000 in
theorem math.pow.wp_proof
    (wp_IsNaN : math.IsNaN.spec (GF := GF) (hG := hG))
    (wp_NaN : math.NaN.spec (GF := GF) (hG := hG))
    (wp_Signbit : math.Signbit.spec (GF := GF) (hG := hG))
    (wp_isOddInt : math.isOddInt.spec (GF := GF) (hG := hG))
    (wp_Inf : math.Inf.spec (GF := GF) (hG := hG))
    (wp_IsInf : math.IsInf.spec (GF := GF) (hG := hG))
    (wp_Abs : math.Abs.spec (GF := GF) (hG := hG))
    (wp_Sqrt : math.Sqrt.spec (GF := GF) (hG := hG))
    (wp_Modf : math.Modf.spec (GF := GF) (hG := hG))
    (wp_Exp : math.Exp.spec (GF := GF) (hG := hG))
    (wp_Log : math.Log.spec (GF := GF) (hG := hG))
    (wp_Frexp : math.Frexp.spec (GF := GF) (hG := hG))
    (wp_Ldexp : math.Ldexp.spec (GF := GF) (hG := hG)) :
    math.pow.spec (GF := GF) (hG := hG) := fun x y => by
  iloeb as IH generalizing %x %y
  irevert IH
  iapply math.powHide_intro
  iintro #IH
  wp_start
  (try wp_auto)
  wp_if_bool
  -- the `switch` of special cases: each case returns or falls through, with `x` and `y` unchanged
  wp_join (Q := fun v => iprop(∃ r : w64, ⌜v = executeVal ∨ v = returnVal #()⌝ ∗
      x_ptr ↦ x ∗ y_ptr ↦ y ∗ «$res0_ptr» ↦ r)) with [x y «$res0»]
  rotate_right
  · iintro ⟨%r, %Hv, x, y, «$res0»⟩
    rcases Hv with Hv | Hv <;> subst Hv
    · (try wp_auto)
      wp_apply wp_Abs
      (try wp_auto)
      wp_apply wp_Modf as %yi0 %yf0 -
      (try wp_auto)
      wp_if_bool
      -- `if yf != 0 && x < 0 { return NaN() }`
      wp_join (Q := fun v => iprop(∃ r : w64, ⌜v = executeVal ∨ v = returnVal #()⌝ ∗
          x_ptr ↦ x ∗ y_ptr ↦ y ∗ yi_ptr ↦ yi0 ∗ yf_ptr ↦ yf0 ∗ «$res0_ptr» ↦ r)) with [x y yi yf «$res0»]
      rotate_right
      · iintro ⟨%r, %Hv, x, y, yi, yf, «$res0»⟩
        rcases Hv with Hv | Hv <;> subst Hv
        · (try wp_auto)
          wp_if_bool
          -- `if yi >= 1<<63 { switch ... }`: every case returns
          wp_join (Q := fun v => iprop(∃ r : w64, ⌜v = executeVal ∨ v = returnVal #()⌝ ∗
              x_ptr ↦ x ∗ y_ptr ↦ y ∗ yi_ptr ↦ yi0 ∗ yf_ptr ↦ yf0 ∗ «$res0_ptr» ↦ r)) with [x y yi yf «$res0»]
          rotate_right
          · iintro ⟨%r, %Hv, x, y, yi, yf, «$res0»⟩
            rcases Hv with Hv | Hv <;> subst Hv
            · (try wp_auto)
              wp_if_bool
              -- `if yf != 0 { ...; a1 = Exp(yf * Log(x)) }`
              wp_join iprop(∃ (a1 yf yi : w64), a1_ptr ↦ a1 ∗ yf_ptr ↦ yf ∗ yi_ptr ↦ yi ∗ x_ptr ↦ x) with [a1 yf yi x]
              rotate_right
              · iintro ⟨%a1v, %yfv, %yiv, a1, yf, yi, x⟩
                (try wp_auto)
                wp_apply wp_Frexp as %x1v %xev -
                (try wp_auto)
                wp_apply wp_ArbitraryInt as %iv -
                (try wp_auto)
                -- the loop `for i := int64(yi); i != 0; i >>= 1`
                ihave HI : (∃ (a1 ae x1 xe i : w64), "a1" ∷ a1_ptr ↦ a1 ∗ "ae" ∷ ae_ptr ↦ ae ∗
                    "x1" ∷ x1_ptr ↦ x1 ∗ "xe" ∷ xe_ptr ↦ xe ∗ "i" ∷ i_ptr ↦ i : IProp GF) $$ [a1 ae x1 xe i]
                · iexists _, _, _, _, _; iframe
                wp_for HI
                -- the condition `i != 0`
                by_cases Hi0 : i = W64 0
                · simp only [Hi0, decide_true, Bool.not_true]
                  pow_steps
                · simp only [Hi0, decide_false, Bool.not_false]
                  pow_steps
              all_goals pow_steps
            · (try wp_auto)
              wp_end
          all_goals pow_steps
        · (try wp_auto)
          wp_end
      all_goals pow_steps
    · (try wp_auto)
      wp_end
  all_goals pow_steps

end proof

end Perennial
