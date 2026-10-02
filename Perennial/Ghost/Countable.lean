/-
`Pos.Countable` instances for the types commonly stored in ghost state.

The ghost libraries (`ghost_var`, `ghost_map`, `mono_list`, `saved_pred`, ...)
store `Pos.Countable.encode a`; see `Perennial/Ghost/All.lean`. User types can get
an instance from an injection with `Pos.Countable.ofInjective`.
-/
import Iris

noncomputable section

namespace Perennial
open Iris

/-- Encode into `DiscreteO Pos` (the Leibniz OFE stored in ghost state). -/
def encodeO {A : Type} [Pos.Countable A] (a : A) : DiscreteO Pos := ⟨Pos.Countable.encode a⟩

theorem encodeO_inj {A : Type} [Pos.Countable A] {a b : A} (h : encodeO a = encodeO b) : a = b :=
  Pos.encode_inj (congrArg DiscreteO.car h)

@[simp] theorem encodeO_eq_iff {A : Type} [Pos.Countable A] {a b : A} :
    encodeO a = encodeO b ↔ a = b :=
  ⟨encodeO_inj, fun h => h ▸ rfl⟩

private theorem list_inj {α β : Type} [Pos.Countable β] {f : α → List β}
    (hf : f.Injective) : (fun a => Pos.Countable.encode (f a)).Injective :=
  fun _ _ h => hf (Pos.encode_inj h)

instance countableUnit : Pos.Countable Unit := .ofInjective (fun _ => Pos.Countable.encode (0 : Nat))
  (fun _ _ _ => rfl)

instance countableProd {A B : Type} [Pos.Countable A] [Pos.Countable B] : Pos.Countable (A × B) :=
  .ofInjective (fun p => Pos.Countable.encode [Pos.Countable.encode p.1, Pos.Countable.encode p.2])
    (fun ⟨a1, b1⟩ ⟨a2, b2⟩ h => by
      have h := Pos.encode_inj h
      simp only [List.cons.injEq, and_true] at h
      rw [Pos.encode_inj h.1, Pos.encode_inj h.2])

instance countableSum {A B : Type} [Pos.Countable A] [Pos.Countable B] : Pos.Countable (A ⊕ B) :=
  .ofInjective (fun
      | .inl a => Pos.Countable.encode [Pos.Countable.encode a]
      | .inr b => Pos.Countable.encode [Pos.Countable.encode b, Pos.Countable.encode b])
    (by
      rintro (a1|b1) (a2|b2) h <;> have h := Pos.encode_inj h <;> simp_all)

instance countableOption {A : Type} [Pos.Countable A] : Pos.Countable (Option A) :=
  .ofInjective (fun
      | none => Pos.Countable.encode ([] : List Pos)
      | some a => Pos.Countable.encode [Pos.Countable.encode a])
    (by
      rintro (_|a1) (_|a2) h
      · rfl
      · exact absurd (Pos.encode_inj h) (by simp)
      · exact absurd (Pos.encode_inj h) (by simp)
      · have h' : [Pos.Countable.encode a1] = [Pos.Countable.encode a2] := Pos.encode_inj h
        simp only [List.cons.injEq, and_true] at h'
        rw [Pos.encode_inj h'])

instance countableBitVec {n : Nat} : Pos.Countable (BitVec n) :=
  .ofInjective (fun x => Pos.Countable.encode x.toNat)
    (fun _ _ h => BitVec.eq_of_toNat_eq (Pos.encode_inj h))

instance countableFin {n : Nat} : Pos.Countable (Fin n) :=
  .ofInjective (fun x => Pos.Countable.encode x.val)
    (fun _ _ h => Fin.ext (Pos.encode_inj h))

open Classical in
instance countableProp : Pos.Countable Prop :=
  .ofInjective (fun P => Pos.Countable.encode (decide P))
    (fun P Q h => by
      have h := Pos.encode_inj h
      by_cases hP : P <;> by_cases hQ : Q <;> simp_all)

end Perennial
