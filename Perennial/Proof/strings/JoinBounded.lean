/-
`strings.Join` with its output-length premise discharged per element and by count: if every
element has at most `B` bytes and `n` elements with their separators fit, `n * (B + |sep|) <
joinMax`, the output is shorter than `joinMax` (`strings.Join.spec`'s premise).
-/
module

public import Perennial.Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The bound on `strings.Join`'s output length (`strings.Join.spec`: Go's `Join` panics when the
output's length overflows an `int`). -/
def strings.joinMax : Nat := 2 ^ 61

/-- The length of `sep.intercalate xs` is at most `n * (B + |sep|)` when each of the `n` elements
has at most `B` bytes. -/
theorem strings.length_intercalate_le {α : Type _} (sep : List α) (xs : List (List α)) (B : Nat)
    (h : ∀ x ∈ xs, x.length ≤ B) : (sep.intercalate xs).length ≤ xs.length * (B + sep.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases xs with
    | nil => simp; omega
    | cons y ys =>
      rw [List.intercalate_cons_cons]
      simp only [List.length_append, List.length_cons] at ih' ⊢
      rw [Nat.succ_mul]
      omega

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Join(elems, sep)` of `n` elements of at most `B` bytes each, with
`n * (B + |sep|) < joinMax`: the elements separated by `sep`. -/
theorem strings.Join_bounded_of (wp_Join : strings.Join.spec (GF := GF) (hG := hG)) :
    ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString) (B : Nat),
    (∀ x ∈ xs, x.length ≤ B) → xs.length * (B + sep.length) < strings.joinMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
      (App (App (Val (@! strings.Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }} := by
  intro elems xs dq sep B hB hn
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  iapply (wp_Join elems xs dq sep) $$ [Hs] HΦ
  iframe
  isplitr
  · iexact Hpkg
  ipureintro
  have := strings.length_intercalate_le sep xs B hB
  unfold strings.joinMax at hn
  omega

end wps

end Perennial
