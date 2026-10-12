/-
Lemmas about byte ranges of the byte memory (`Lang.lean`, "Byte memory"):
`byteAddr`, `LookupRange`, `insertRange` and `FreshRange`.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

theorem byteAddr_zero (a : w64) : byteAddr a 0 = a := by
  simp [byteAddr]

theorem byteAddr_succ (a : w64) (i : Nat) : byteAddr (a + 1) i = byteAddr a (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : w64).toNat = 1 := rfl
  simp only [byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

theorem byteAddr_toNat (a : w64) (i : Nat) :
    (byteAddr a i).toNat = (a.toNat + i) % 2 ^ 64 := by
  simp only [byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem byteAddr_inj {a : w64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    byteAddr a i = byteAddr a j → i = j := by
  intro h
  have h' := congrArg BitVec.toNat h
  rw [byteAddr_toNat, byteAddr_toNat] at h'
  have := a.isLt
  omega

theorem lookup_insertRange_of_ne (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (x : w64) (h : ∀ i < cs.length, byteAddr a i ≠ x) : insertRange m a cs !! x = m !! x := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih =>
    have h0 : a ≠ x := by simpa [byteAddr_zero] using h 0 (by simp)
    simp only [insertRange]
    rw [GMap.lookup_insert_ne _ _ h0]
    apply ih
    intro i hi
    rw [byteAddr_succ]
    exact h (i + 1) (by simp; omega)

theorem lookup_insertRange_getElem (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hlen : cs.length ≤ 2 ^ 64) (i : Nat) (hi : i < cs.length) :
    insertRange m a cs !! byteAddr a i = some cs[i] := by
  induction cs generalizing a i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [insertRange]
    cases i with
    | zero => rw [byteAddr_zero]; exact GMap.lookup_insert _ _ _
    | succ k =>
      simp only [List.length_cons] at hi hlen
      have hne : a ≠ byteAddr a (k + 1) := by
        intro he
        have he' : byteAddr a 0 = byteAddr a (k + 1) := by rw [byteAddr_zero]; exact he
        have := byteAddr_inj (by omega) (by omega) he'
        omega
      rw [GMap.lookup_insert_ne _ _ hne, ← byteAddr_succ]
      simpa using ih (a + 1) (by omega) k (by omega)

theorem lookupRange_iff (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell) :
    LookupRange m a cs ↔ ∀ i (hi : i < cs.length), m !! byteAddr a i = some cs[i] := by
  induction cs generalizing a with
  | nil => simp [LookupRange]
  | cons c cs ih =>
    simp only [LookupRange, ih]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => simpa [byteAddr_zero] using h0
      | succ k =>
        rw [← byteAddr_succ]
        simpa using hr k (by simp at hi; omega)
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have := h 0 (by simp)
        rw [byteAddr_zero] at this
        exact this
      · rw [byteAddr_succ]
        exact h (i + 1) (by simp; omega)

theorem lookupRange_insertRange_self (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hlen : cs.length ≤ 2 ^ 64) : LookupRange (insertRange m a cs) a cs :=
  (lookupRange_iff _ _ _).2 fun i hi => lookup_insertRange_getElem m a cs hlen i hi

theorem lookupRange_insertRange_of_disjoint (m : GMap w64 ByteCell) (a b : w64)
    (cs ds : List ByteCell) (hd : LookupRange m b ds)
    (hdisj : ∀ j < ds.length, ∀ i < cs.length, byteAddr a i ≠ byteAddr b j) :
    LookupRange (insertRange m a cs) b ds := by
  rw [lookupRange_iff] at hd ⊢
  intro j hj
  rw [lookup_insertRange_of_ne _ _ _ _ (fun i hi => hdisj j hj i hi)]
  exact hd j hj

theorem insertRange_isSome (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell) (x : w64) :
    (m !! x).isSome → (insertRange m a cs !! x).isSome := by
  intro h
  induction cs generalizing a with
  | nil => exact h
  | cons c cs ih =>
    simp only [insertRange, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact ih _

theorem insertRange_lookup_cases {m : GMap w64 ByteCell} {a : w64} {cs : List ByteCell}
    {x : w64} {c : ByteCell} :
    insertRange m a cs !! x = some c → m !! x = some c ∨ ∃ i < cs.length, x = byteAddr a i := by
  induction cs generalizing a with
  | nil => exact Or.inl
  | cons d cs ih =>
    simp only [insertRange, GMap.lookup_insert_eq_iff]
    split
    · rename_i he
      intro _
      exact Or.inr ⟨0, by simp, by rw [byteAddr_zero, he]⟩
    · intro h
      rcases ih h with h | ⟨i, hi, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨i + 1, by simp; omega, byteAddr_succ a i⟩

theorem freshRange_ne_zero {m : GMap w64 ByteCell} {a : w64} {n i : Nat}
    (h : FreshRange m a n) (hi : i < n) : byteAddr a i ≠ 0 := by
  obtain ⟨h0, hn, _⟩ := h
  intro he
  have h' := congrArg BitVec.toNat he
  rw [byteAddr_toNat] at h'
  have : a.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq (by simpa using hz))
  simp at h'
  rw [Nat.mod_eq_of_lt (by omega)] at h'
  omega

theorem freshRange_lookup {m : GMap w64 ByteCell} {a : w64} {n i : Nat}
    (h : FreshRange m a n) (hi : i < n) : m !! byteAddr a i = none :=
  h.2.2 i hi

theorem freshRange_insertRange_disjoint {m : GMap w64 ByteCell} {a : w64} {n : Nat} {x : w64}
    (h : FreshRange m a n) (hx : (m !! x).isSome) : ∀ i < n, byteAddr a i ≠ x := by
  intro i hi he
  have := freshRange_lookup h hi
  rw [he] at this
  simp [this] at hx

theorem insertRange_insertRange_same (m : GMap w64 ByteCell) (a : w64) (cs ds : List ByteCell)
    (h : cs.length = ds.length) (hlen : ds.length ≤ 2 ^ 64) :
    insertRange (insertRange m a cs) a ds = insertRange m a ds := by
  apply GMap.ext
  intro x
  by_cases hx : ∃ i < ds.length, byteAddr a i = x
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [lookup_insertRange_getElem _ _ _ hlen i hi, lookup_insertRange_getElem _ _ _ hlen i hi]
  · have hx' : ∀ i < ds.length, byteAddr a i ≠ x := fun i hi he => hx ⟨i, hi, he⟩
    rw [lookup_insertRange_of_ne _ _ _ _ hx', lookup_insertRange_of_ne _ _ _ _ hx',
      lookup_insertRange_of_ne _ _ _ _ (h ▸ hx')]

theorem insertRange_eq_self_of_lookupRange (m : GMap w64 ByteCell) (a : w64) (cs : List ByteCell)
    (hlen : cs.length ≤ 2 ^ 64) (h : LookupRange m a cs) : insertRange m a cs = m := by
  apply GMap.ext
  intro x
  by_cases hx : ∃ i < cs.length, byteAddr a i = x
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [lookup_insertRange_getElem _ _ _ hlen i hi, (lookupRange_iff _ _ _).1 h i hi]
  · exact lookup_insertRange_of_ne _ _ _ _ fun i hi he => hx ⟨i, hi, he⟩

end Perennial
