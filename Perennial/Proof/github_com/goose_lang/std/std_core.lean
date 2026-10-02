/-
Port of `new/proof/github_com/goose_lang/std/std_core.v`: specs for
`github.com/goose-lang/std/std_core` (overflow checks, `Shuffle`,
`Permutation`).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.github_com.goose_lang.std.std_core
import Perennial.GeneratedProof.github_com.goose_lang.std.std_core
import Perennial.Proof.github_com.goose_lang.primitive

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.goose_lang.std.std_core

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.github_com.goose_lang.std.std_core get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hprim⟩
  iframe Hown
  is_pkg_init_finish

theorem wp_SumNoOverflow (x y : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! SumNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x + y) = uint.Z x + uint.Z y)); True }} := by
  wp_start as _
  wp_auto
  have h : (uint.Z x ≤ uint.Z (x + y)) ↔ (uint.Z (x + y) = uint.Z x + uint.Z y) := by
    have := sum_overflow_check x y
    constructor <;> intro <;> word
  rw [decide_eq_decide.mpr h]
  iapply HΦ
  itrivial

theorem wp_SumAssumeNoOverflow (x y : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! SumAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x + y); ⌜uint.Z (x + y) = uint.Z x + uint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_SumNoOverflow
  wp_apply github_com.goose_lang.primitive.wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

theorem wp_MulNoOverflow (x y : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x * y) = uint.Z x * uint.Z y)); True }} := by
  wp_start as _
  wp_auto
  wp_if_destruct
  · rw [decide_eq_true (by simp [uint.Z])]
    iapply HΦ; itrivial
  · have Hx := Hif
    wp_if_destruct
    · rw [decide_eq_true (by simp [uint.Z])]
      iapply HΦ; itrivial
    · have hx : uint.Z x ≠ 0 := fun h => Hx (by word)
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

theorem wp_MulAssumeNoOverflow (x y : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core }}
      (App (App (Val (@! MulAssumeNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(x * y); ⌜uint.Z (x * y) = uint.Z x * uint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_MulNoOverflow
  wp_apply github_com.goose_lang.primitive.wp_Assume as %Hassume
  iapply HΦ
  ipureintro
  simpa using Hassume

end wps

end github_com.goose_lang.std.std_core

end Perennial
end
