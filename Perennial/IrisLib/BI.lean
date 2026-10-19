/-
Facts about iris-lean's propositions that it does not have: `Persistent` and `Timeless` of an
`if`; an existential of fractional predicates whose witnesses agree, and a predicate equivalent
to a fractional one, are `Fractional`.
-/
module

public import Iris

@[expose] public section

namespace Perennial
open Iris Iris.BI Iris.ProofMode

section bi
variable {PROP : Type _} [BI PROP]

instance ite_persistent (c : Prop) [Decidable c] (P Q : PROP) [Persistent P] [Persistent Q] :
    Persistent (if c then P else Q) := by
  split <;> infer_instance

instance ite_timeless (c : Prop) [Decidable c] (P Q : PROP) [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> infer_instance

/-- An existential of fractional predicates whose witnesses agree is fractional. -/
theorem fractional_exists_agree {X : Type _} (Φ : X → Qp → PROP) (hfrac : ∀ x, Fractional (Φ x))
    (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

/-- A predicate equivalent at every fraction to a fractional one is fractional. -/
theorem fractional_of_equiv {Φ Ψ : Qp → PROP} (h : ∀ q, Φ q ⊣⊢ Ψ q) [hΨ : Fractional Ψ] :
    Fractional Φ where
  fractional p q :=
    (h (p + q)).trans ((hΨ.fractional p q).trans (sep_congr (h p).symm (h q).symm))

end bi

end Perennial
