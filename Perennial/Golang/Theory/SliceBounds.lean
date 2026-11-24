/-
The length of a fully owned slice is below `maxAddr` when each element is a heap cell
(`ownSlice_length_lt_maxAddr_of_cells`; strings: `ownSlice_string_length_lt_maxAddr`): with full
ownership no two elements share a cell, and every cell is at an address in `(0, maxAddr)`. A
derivation from the heap points-to, not a new rule. (A fractional or persistent slice points-to
gives no such bound: `arrayIndexRef` may map every index to one cell, which then holds every
element at a fraction.)
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL

/-- A list of distinct naturals, all in `[1, m)`, has fewer than `m` elements (`m ≥ 1`). -/
theorem nodup_length_lt_of_bounded (xs : List Nat) (m : Nat) (hm : 1 ≤ m) (hnd : xs.Nodup)
    (hb : ∀ x ∈ xs, 1 ≤ x ∧ x < m) : xs.length < m := by
  have hsub : xs ⊆ List.range' 1 (m - 1) := by
    intro x hx
    have := hb x hx
    simp only [List.mem_range'_1]
    omega
  have := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_range'] at this
  omega

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- A fully owned heap cell is at an address other than those of the fully owned cells `f i`. -/
theorem heapPointsto_own_cells_ne (a : Loc) (w : val) (f : Nat → Loc) (vs : List V)
    (cell : Nat → V → val) :
    (heapPointsto a (DFrac.own 1) w : IProp GF) ⊢
      ([∗list] i ↦ v ∈ vs, heapPointsto (f i) (DFrac.own 1) (cell i v)) -∗
      ⌜∀ i, i < vs.length → (f i).addr ≠ a.addr⌝ := by
  induction vs generalizing f cell with
  | nil =>
    iintro _ _
    ipureintro
    intro i hi
    simp at hi
  | cons v vs ih =>
    iintro Ha Hs
    icases bigSepL_cons.1 $$ Hs with ⟨H0, Hs⟩
    by_cases h0 : (f 0).addr = a.addr
    · have hl : f 0 = a := by
        cases hf : f 0 with
        | mk x => cases a with
          | mk y => rw [hf] at h0; simp only at h0; rw [h0]
      rw [hl]
      icombine Ha H0 gives %Hv
      exact absurd (DFrac.valid_op_own Hv.1) (by simp)
    · icases (ih (fun i => f (i + 1)) (fun i => cell (i + 1))) $$ Ha Hs with %Ht
      ipureintro
      intro i hi
      cases i with
      | zero => exact h0
      | succ i => exact Ht i (by simp at hi; omega)

/-- Fully owned heap cells `f i` are at distinct addresses in `(0, maxAddr)`. -/
theorem own_cells_addrs (f : Nat → Loc) (vs : List V) (cell : Nat → V → val) :
    ([∗list] i ↦ v ∈ vs, (heapPointsto (f i) (DFrac.own 1) (cell i v) : IProp GF)) ⊢
      ⌜((List.range vs.length).map (fun i => (f i).addr.toNat)).Nodup ∧
        ∀ i, i < vs.length → 0 < (f i).addr ∧ (f i).addr < maxAddr⌝ := by
  induction vs generalizing f cell with
  | nil =>
    iintro _
    ipureintro
    simp
  | cons v vs ih =>
    iintro Hs
    icases bigSepL_cons.1 $$ Hs with ⟨H0, Hs⟩
    icases heapPointsto_pos _ _ _ $$ H0 with %Hp
    icases heapPointsto_lt_maxAddr _ _ _ $$ H0 with %Hm
    icases (ih (fun i => f (i + 1)) (fun i => cell (i + 1))) $$ Hs with %Hih
    obtain ⟨Hnd, Hb⟩ := Hih
    icases heapPointsto_own_cells_ne (f 0) _ (fun i => f (i + 1)) vs (fun i => cell (i + 1))
      $$ H0 Hs with %Hne
    ipureintro
    constructor
    · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.nodup_cons,
        List.map_map]
      refine ⟨?_, Hnd⟩
      intro hmem
      obtain ⟨i, hi, he⟩ := List.mem_map.1 hmem
      have hi' := List.mem_range.1 hi
      have h1 := Hne i hi'
      have h2 := Hb i hi'
      simp only [Function.comp_apply, Nat.succ_eq_add_one] at he
      have e1 : (((f (i + 1)).addr.toNat : Nat) : Int) = (f (i + 1)).addr :=
        Int.toNat_of_nonneg (by omega)
      have e2 : (((f 0).addr.toNat : Nat) : Int) = (f 0).addr := Int.toNat_of_nonneg (by omega)
      rw [he] at e1
      omega
    · intro i hi
      cases i with
      | zero => exact ⟨Hp, Hm⟩
      | succ i => exact Hb i (by simp at hi; omega)

/-- A fully owned slice whose elements are heap cells (`hcell`: each element's points-to is a
fully owned heap points-to) has fewer than `maxAddr` elements. -/
theorem ownSlice_length_lt_maxAddr_of_cells
    (hcell : ∀ (l : Loc) (v : V), typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      (heapPointsto l (DFrac.own 1) (#v) : IProp GF))
    (s : GoSlice) (vs : List V) :
    (s ↦* vs : IProp GF) ⊢ ⌜(vs.length : Int) < maxAddr⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  iintro (%H | ⟨⟨⟨%_, He⟩, _⟩, %_⟩)
  · obtain ⟨_, rfl⟩ := H
    ipureintro; simp [maxAddr]
  · icases (bigSepL_mono_of_forall (PROP := IProp GF) (l := vs)
        (Φ := fun i ve => typedPointsto (arrayIndexRef V (i : Int) s.ptr) ve (DFrac.own 1))
        (Ψ := fun i ve => heapPointsto (arrayIndexRef V (i : Int) s.ptr)
          (DFrac.own 1) (#ve))
        (fun {_ x} => hcell _ x)) $$ He with He
    icases own_cells_addrs (fun i => arrayIndexRef V (i : Int) s.ptr) vs (fun _ v => #v)
      $$ He with %Hih
    obtain ⟨Hnd, Hb⟩ := Hih
    ipureintro
    have hm0 : (0 : Int) ≤ maxAddr := by simp [maxAddr]
    have em : ((maxAddr.toNat : Nat) : Int) = maxAddr := Int.toNat_of_nonneg hm0
    have hlt := nodup_length_lt_of_bounded
      ((List.range vs.length).map (fun (i : Nat) => (arrayIndexRef V (i : Int) s.ptr).addr.toNat))
      maxAddr.toNat (by simp [maxAddr]) Hnd (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        have := Hb i (List.mem_range.1 hi)
        have e : (((arrayIndexRef V (i : Int) s.ptr).addr.toNat : Nat) : Int) =
            (arrayIndexRef V (i : Int) s.ptr).addr := Int.toNat_of_nonneg (by omega)
        omega)
    simp only [List.length_map, List.length_range] at hlt
    omega

/-- A fully owned slice of strings has fewer than `maxAddr` elements. -/
theorem ownSlice_string_length_lt_maxAddr (s : GoSlice) (xs : List GoString) :
    (s ↦* xs : IProp GF) ⊢ ⌜(xs.length : Int) < maxAddr⌝ :=
  ownSlice_length_lt_maxAddr_of_cells (fun l v => typedPointsto_split l v _) s xs

end lemmas

end Perennial
