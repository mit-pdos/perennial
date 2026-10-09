/-
`▷` over existentials with a finite witness type.

With transfinite step indices, `▷ (∃ x, Φ x) ⊢ ∃ x, ▷ Φ x` does not hold in
general (iris-lean's `later_exists` needs `[SIdxFinite SI]`), so the proof mode
cannot destruct a `▷ ∃`. For a finite witness type it does hold: `▷` commutes
with binary disjunction (`later_or_1`, for every step index). This file
registers that case for `Bool` as an `IntoExists` instance, so that e.g.
opening an invariant `∃ b : Bool, ...` destructs as with finite step indices.
-/
module

public import Iris

@[expose] public section

namespace Perennial
open Iris BI ProofMode

theorem later_exists_bool {PROP : Type _} [BI PROP] (Φ : Bool → PROP) :
    ▷ (∃ b, Φ b) ⊢ ∃ b, ▷ Φ b := by
  have h : (∃ b, Φ b) ⊢ Φ false ∨ Φ true :=
    exists_elim fun b => by cases b <;> first | exact or_intro_l | exact or_intro_r
  exact (later_mono h).trans (later_or_1.trans
    (or_elim (exists_intro (Ψ := fun b => iprop(▷ Φ b)) false)
      (exists_intro (Ψ := fun b => iprop(▷ Φ b)) true)))

/-- `▷` commutes with existentials over `α` (in every BI, for every step index). -/
class LaterExistsCommutes.{u, v} (α : Sort u) : Prop where
  later_exists : ∀ {PROP : Type v} [BI PROP] (Φ : α → PROP), ▷ (∃ x, Φ x) ⊢ ∃ x, ▷ Φ x

instance : LaterExistsCommutes.{1, v} Bool := ⟨fun Φ => later_exists_bool Φ⟩

instance (priority := high) intoExists_later_commutes.{u, w} {PROP : Type w} [BI PROP]
    {α : Sort u} (P : PROP) (Φ : α → PROP) [h : IntoExists P Φ]
    [hc : LaterExistsCommutes.{u, w} α] :
    IntoExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_exists := (later_mono h.1).trans (hc.later_exists Φ)

end Perennial
