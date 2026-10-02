/-
Port of `src/iris_lib/conflicting.v`.

Predicates `P0`, `P1` *conflict* if owning `P0 a0 v0` and `P1 a1 v1` together
implies `a0 ≠ a1` (think: exclusive points-to facts). Big separating
conjunctions over conflicting predicates have disjoint domains.

Differences from Rocq:
* `BiPureForall` is not needed (iris-lean proves `pure_forall` for every BI).
* Maps are any iris-lean `LawfulFiniteMap` (in particular `Perennial.gmap`).
* `Conflicting P` is a class of its own (with an instance from
  `ConflictsWith P P`) instead of a definitional alias, so that instance search
  does not loop.
-/
import Iris.BI
import Iris.BI.BigOp
import Iris.ProofMode
import Iris.Std.PartialMap

namespace Perennial

open Iris Iris.BI Iris.Std BigSepM PartialMap

variable {PROP : Type _} [BI PROP]

/-- Rocq `ConflictsWith`. -/
class ConflictsWith {L V : Type _} (P0 P1 : L → V → PROP) : Prop where
  conflicts_with : ∀ a0 v0 a1 v1, P0 a0 v0 ⊢ P1 a1 v1 -∗ ⌜a0 ≠ a1⌝

export ConflictsWith (conflicts_with)

theorem big_sepM_disjoint_pred {L V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M L]
    [BIAffine PROP] {P0 P1 : L → V → PROP} [ConflictsWith P0 P1] (m0 m1 : M V) :
    ([∗map] a ↦ v ∈ m0, P0 a v) ⊢ ([∗map] a ↦ v ∈ m1, P1 a v) -∗ ⌜m0 ##ₘ m1⌝ := by
  refine wand_intro ?_
  refine .trans ?_ pure_forall.2
  refine forall_intro fun i => ?_
  cases h0 : get? m0 i with
  | none => iintro _; ipureintro; simp
  | some v0 =>
    cases h1 : get? m1 i with
    | none => iintro _; ipureintro; simp
    | some v1 =>
      iintro ⟨H0, H1⟩
      ihave H0 := (bigSepM_lookup (Φ := P0) h0) $$ H0
      ihave H1 := (bigSepM_lookup (Φ := P1) h1) $$ H1
      ihave %Hne := (conflicts_with (P0 := P0) (P1 := P1) i v0 i v1) $$ H0 H1
      exact absurd rfl Hne

/-- Rocq `Conflicting`: `P` conflicts with itself. -/
class Conflicting {L V : Type _} (P : L → V → PROP) : Prop where
  conflicting : ∀ a0 v0 a1 v1, P a0 v0 ⊢ P a1 v1 -∗ ⌜a0 ≠ a1⌝

export Conflicting (conflicting)

theorem Conflicting.toConflictsWith {L V : Type _} {P : L → V → PROP} [Conflicting P] :
    ConflictsWith P P :=
  ⟨conflicting⟩

instance conflicting_conflicts_with {L V : Type _} (P : L → V → PROP) [H : ConflictsWith P P] :
    Conflicting P :=
  ⟨H.conflicts_with⟩

instance conflicting_sep_l {L V : Type _} (P Q : L → V → PROP) [Conflicting P] :
    Conflicting (fun l v => iprop(P l v ∗ Q l v)) where
  conflicting a0 v0 a1 v1 := by
    iintro ⟨HP1, _⟩ ⟨HP2, _⟩
    iapply (conflicting (P := P) a0 v0 a1 v1) $$ HP1 HP2

instance conflicting_sep_r {L V : Type _} (P Q : L → V → PROP) [Conflicting Q] :
    Conflicting (fun l v => iprop(P l v ∗ Q l v)) where
  conflicting a0 v0 a1 v1 := by
    iintro ⟨_, HQ1⟩ ⟨_, HQ2⟩
    iapply (conflicting (P := Q) a0 v0 a1 v1) $$ HQ1 HQ2

theorem conflicting_false {L V : Type _} (P : L → V → PROP) [Conflicting P] (a : L) (v0 v1 : V) :
    P a v0 ⊢ P a v1 -∗ False := by
  iintro H1 H2
  ihave %Hneq := (conflicting (P := P) a v0 a v1) $$ H1 H2
  exact absurd rfl Hneq

end Perennial
