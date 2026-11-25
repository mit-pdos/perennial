/-
`append`'s overflow assumption, `assumeSumNoOverflowSigned`, holds exactly when the sum does
not overflow (regression test, mit-pdos/perennial#641).

`append(s, x...)` (`Defn/Slice.lean`, `append_slice`) assumes `len(s) + len(x)` does not
overflow. The assumption used to hold only for `0 < y` or `y < 0` and strict bounds, so in
the model `append(s, x...)` with an empty `x` never returned (and nothing after it needed a
proof), nor did a sum equal to `max_int` or `min_int`. Each example below steps through the
assumption to `assume #true`; `wp_assume_true` applies only to a true condition.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

namespace Perennial
namespace AssumeSumNoOverflowTest

open Iris Iris.BI

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_assume_true (Φ : val → IProp GF) :
    Φ #() ⊢ WP (App (Val assume) (Val #true)) {{ Φ }} := by
  iintro HΦ
  iapply wp_assume
  iintro _
  iexact HΦ

/-- `len(s) + len(x)` with `len(x) = 0` (`append(s, x...)` with an empty `x`). -/
example (Φ : val → IProp GF) :
    Φ #() ⊢ WP (App (App (Val assumeSumNoOverflowSigned) (Val #(W64 5))) (Val #(W64 0))) {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_pures
  iapply wp_assume_true
  iexact HΦ

/-- `len(s) = 0` and `len(x) = 0`. -/
example (Φ : val → IProp GF) :
    Φ #() ⊢ WP (App (App (Val assumeSumNoOverflowSigned) (Val #(W64 0))) (Val #(W64 0))) {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_pures
  iapply wp_assume_true
  iexact HΦ

/-- A sum equal to `max_int` does not overflow. -/
example (Φ : val → IProp GF) :
    Φ #() ⊢ WP (App (App (Val assumeSumNoOverflowSigned) (Val #(W64 (2 ^ 63 - 2)))) (Val #(W64 1))) {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_pures
  iapply wp_assume_true
  iexact HΦ

/-- A sum equal to `min_int` does not overflow. -/
example (Φ : val → IProp GF) :
    Φ #() ⊢ WP (App (App (Val assumeSumNoOverflowSigned) (Val #(W64 (-2 ^ 63 + 1)))) (Val #(W64 (-1)))) {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_pures
  iapply wp_assume_true
  iexact HΦ

end

end AssumeSumNoOverflowTest
end Perennial
