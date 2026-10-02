/-
`Pos.Countable` instances for basic types, and generic trees.

The ghost libraries (`ghost_var`, `ghost_map`, `mono_list`, `saved_pred`, ...)
store `Pos.Countable.encode a`; see `Perennial/Ghost/All.lean`. User types can get
an instance from an injection with `Pos.Countable.ofInjective`.

`GenTree` (stdpp `gen_tree`) is a countable type of finitely-branching trees
with `Pos` leaves; a syntax type is shown countable by an injection into it (as
Rocq `lang.v` does for `val`/`expr`), see `Perennial/GooseLang/Countable.lean`.
-/
import Iris.Std.Positives
import Perennial.Std.GMap

noncomputable section

namespace Perennial

private theorem list_inj {α β : Type} [Pos.Countable β] {f : α → List β}
    (hf : f.Injective) : (fun a => Pos.Countable.encode (f a)).Injective :=
  fun _ _ h => hf (Pos.encode_inj h)

instance countableUnit : Pos.Countable Unit where
  encode _ := Pos.Countable.encode (0 : Nat)
  decode _ := some ()
  decode_encode _ := rfl

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

instance countableVector {A : Type} [Pos.Countable A] {n : Nat} : Pos.Countable (Vector A n) :=
  .ofInjective (fun v => Pos.Countable.encode v.toList)
    (fun _ _ h => Vector.toList_inj.mp (Pos.encode_inj h))

open Classical in
instance countableProp : Pos.Countable Prop :=
  .ofInjective (fun P => Pos.Countable.encode (decide P))
    (fun P Q h => by
      have h := Pos.encode_inj h
      by_cases hP : P <;> by_cases hQ : Q <;> simp_all)

/-- `Pos.Countable` for finite maps, through the (canonical) `toList`. -/
instance gmap_countable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V] :
    Pos.Countable (gmap K V) :=
  .ofInjective (fun m => Pos.Countable.encode m.toList)
    (fun m1 m2 h => by
      have h : m1.toList = m2.toList := Pos.encode_inj h
      apply gmap.map_eq
      intro k
      cases h1 : m1 !! k with
      | none =>
        cases h2 : m2 !! k with
        | none => rfl
        | some v =>
          have := (gmap.mem_toList m2 k v).mpr h2
          rw [← h, gmap.mem_toList, h1] at this
          cases this
      | some v =>
        have := (gmap.mem_toList m1 k v).mpr h1
        rw [h, gmap.mem_toList] at this
        exact this.symm)

/-- Countability from a left-inverse map into a countable type (stdpp `inj_countable'`). -/
abbrev countableOfLeftInverse {A B : Type} [Pos.Countable B] (f : A → B) (g : B → A)
    (h : ∀ a, g (f a) = a) : Pos.Countable A where
  encode a := Pos.Countable.encode (f a)
  decode p := (Pos.Countable.decode p : Option B).map g
  decode_encode a := by simp [Pos.Countable.decode_encode, h]

/-! ## Generic trees (stdpp `gen_tree`) -/

/-- Finitely-branching trees with `Pos` leaves and `Nat`-tagged nodes. -/
inductive GenTree where
  | leaf (p : Pos)
  | node (tag : Nat) (cs : List GenTree)
deriving Inhabited

namespace GenTree

/-- A leaf holding the encoding of `a`. -/
abbrev of {A : Type} [Pos.Countable A] (a : A) : GenTree := leaf (Pos.Countable.encode a)

/-- Decode a leaf (a left inverse of `of`). -/
def decLeaf {A : Type} [Pos.Countable A] [Inhabited A] : GenTree → A
  | leaf p => (Pos.Countable.decode p).getD default
  | _ => default

@[simp] theorem decLeaf_of {A : Type} [Pos.Countable A] [Inhabited A] (a : A) :
    decLeaf (of a) = a := by
  simp [decLeaf, Pos.Countable.decode_encode]

mutual
def enc : GenTree → Pos
  | leaf p => Pos.Countable.encode [Pos.Countable.encode (0 : Nat), p]
  | node n cs => Pos.Countable.encode (Pos.Countable.encode (n + 1) :: encList cs)
def encList : List GenTree → List Pos
  | [] => []
  | t :: ts => enc t :: encList ts
end

mutual
theorem enc_inj : ∀ {a b : GenTree}, enc a = enc b → a = b
  | leaf p, leaf q, h => by
    simp only [enc, Pos.encode_eq_iff, List.cons.injEq, and_true, true_and] at h; rw [h]
  | leaf p, node m cs, h => by
    simp only [enc, Pos.encode_eq_iff, List.cons.injEq] at h; omega
  | node n cs, leaf q, h => by
    simp only [enc, Pos.encode_eq_iff, List.cons.injEq] at h; omega
  | node n cs, node m ds, h => by
    simp only [enc, Pos.encode_eq_iff, List.cons.injEq, Nat.add_right_cancel_iff] at h
    rw [h.1, encList_inj h.2]
theorem encList_inj : ∀ {as bs : List GenTree}, encList as = encList bs → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList] at h
  | _ :: _, [], h => by simp [encList] at h
  | a :: as, b :: bs, h => by
    simp only [encList, List.cons.injEq] at h
    rw [enc_inj h.1, encList_inj h.2]
end

instance countable : Pos.Countable GenTree := .ofInjective enc (fun _ _ => enc_inj)

end GenTree

/-- Countability from an injection into `GenTree`. -/
abbrev countableOfTree {A : Type} (f : A → GenTree) (hf : ∀ {a b : A}, f a = f b → a = b) :
    Pos.Countable A :=
  .ofInjective (fun a => Pos.Countable.encode (f a)) (fun _ _ h => hf (Pos.encode_inj h))

end Perennial
