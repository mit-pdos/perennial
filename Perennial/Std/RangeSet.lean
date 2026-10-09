module

public import Perennial.Std.Word.Properties

@[expose] public section

noncomputable section

namespace Perennial

/-- The set of words `W64 start, ..., W64 (start + sz - 1)`. -/
def rangeSet (start sz : Int) : GSet w64 := listToSet ((seqZ start sz).map W64)

theorem rangeSet_lookup (start sz : Int) (i : w64) (hpos : 0 ≤ start) (hov : start + sz < 2 ^ 64) :
    i ∈ rangeSet start sz ↔ start ≤ uint.Z i ∧ uint.Z i < start + sz := by
  rw [rangeSet, elem_of_list_to_set, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [elem_of_seqZ] at hy
    rw [uint_Z_W64 y (by omega) (by omega)]; exact hy
  · intro h
    refine ⟨uint.Z i, (elem_of_seqZ _ _ _).mpr h, ?_⟩
    simp [W64, uint.Z]

theorem rangeSet_diag (start sz : Int) (h : sz = 0) : rangeSet start sz = ∅ := by
  subst h; rfl

theorem rangeSet_empty (start sz : Int) (h : sz ≤ 0) : rangeSet start sz = ∅ := by
  rw [rangeSet, seqZ_nil _ _ h]; rfl

theorem rangeSet_size (start sz : Int) (h1 : 0 ≤ start) (h2 : 0 ≤ sz) (hov : start + sz < 2 ^ 64) :
    GMap.size (rangeSet start sz) = sz.toNat := by
  rw [rangeSet, size_list_to_set _ (seq_U64_NoDup start sz h1 hov), List.length_map, length_seqZ]

theorem rangeSet_append_one (start sz : w64) (hb : uint.Z start + uint.Z sz < 2 ^ 64) (i : w64)
    (hi : uint.Z i < uint.Z (start + sz)) (hlo : uint.Z start ≤ uint.Z i) :
    {[i]} ∪ rangeSet (uint.Z start) (uint.Z i - uint.Z start) =
      rangeSet (uint.Z start) (uint.Z i - uint.Z start + 1) := by
  have hadd : uint.Z (start + sz) = uint.Z start + uint.Z sz := by word
  have h0 := uint_Z_nonneg start
  apply set_eq; intro x
  rw [elem_of_union, elem_of_singleton, rangeSet_lookup _ _ _ h0 (by omega),
    rangeSet_lookup _ _ _ h0 (by omega)]
  constructor
  · rintro (rfl | h) <;> omega
  · intro h
    by_cases e : uint.Z x = uint.Z i
    · exact Or.inl (uint_Z_inj.mp e)
    · right; omega

theorem rangeSet_first (start sz : Int) (h : sz > 0) :
    rangeSet start sz = {[W64 start]} ∪ rangeSet (start + 1) (sz - 1) := by
  rw [rangeSet, seqZ_cons _ _ h, List.map_cons, listToSet_cons]; rfl

theorem rangeSet_first_disjoint (start sz : Int) (h1 : 0 ≤ start) (hov : start + sz < 2 ^ 64) :
    {[W64 start]} ## rangeSet (start + 1) (sz - 1) := by
  rw [disjoint_singleton_l, rangeSet_lookup _ _ _ (by omega) (by omega)]
  have : uint.Z (W64 start) ≤ start := by
    rw [word.unsigned_of_Z]; omega
  omega

end Perennial
