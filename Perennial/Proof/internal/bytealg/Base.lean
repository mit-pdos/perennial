/-
Shared definitions of the proofs of `internal/bytealg`: its `isPkgInit` (`MaxLen`'s value), and
the pure functions its specs are written in (the first index of a byte or a substring, the
Rabin-Karp hashes, what `CompareString` returns) with their laws.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.bytealg
public import Perennial.Proof.internal.gomodel.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.bytealg

/-- What `bytealg.CompareString(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less
than, equal to or greater than `b` (Go's `<` on strings, `GoStringLt`). -/
def compareResult [GooseExts] (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

/-! ## The first index of a substring -/

/-- The first index below `j` at which `sep` occurs in `s`, or `-1`. -/
def indexBelow (s sep : List w8) : Nat → Int
  | 0 => -1
  | j + 1 =>
    let r := indexBelow s sep j
    if 0 ≤ r then r else if sep <+: s.drop j then j else -1

/-- The first index at which `sep` occurs in `s`, or `-1` (`0` for an empty `sep`). -/
def index (s sep : List w8) : Int := indexBelow s sep (s.length + 1)

theorem indexBelow_eq_neg (s sep : List w8) :
    ∀ k, (∀ j < k, ¬ sep <+: s.drop j) → indexBelow s sep k = -1
  | 0, _ => rfl
  | k + 1, H => by
    simp only [indexBelow]
    rw [indexBelow_eq_neg s sep k (fun j hj => H j (by omega))]
    simp [H k (by omega)]

theorem indexBelow_eq_of (s sep : List w8) (i : Nat) (h : sep <+: s.drop i)
    (hmin : ∀ j < i, ¬ sep <+: s.drop j) : ∀ k, i < k → indexBelow s sep k = i := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [indexBelow]
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [ih hik]; simp
    · have hik : k = i := by omega
      subst hik
      rw [indexBelow_eq_neg s sep k hmin]; simp [h]

/-- `sep` occurs at `i` and nowhere before: `index s sep = i`. -/
theorem index_eq_of (s sep : List w8) (i : Nat) (h : sep <+: s.drop i)
    (hmin : ∀ j < i, ¬ sep <+: s.drop j) : index s sep = i := by
  have hi : i ≤ s.length := by
    refine Classical.byContradiction fun hc => ?_
    have := h.length_le
    simp only [List.length_drop] at this
    have hsep : sep = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact hmin 0 (by omega) (hsep ▸ List.nil_prefix)
  exact indexBelow_eq_of s sep i h hmin _ (by omega)

/-- `sep` occurs nowhere in `s`: `index s sep = -1`. -/
theorem index_eq_neg (s sep : List w8) (h : ∀ j, ¬ sep <+: s.drop j) : index s sep = -1 :=
  indexBelow_eq_neg s sep _ (fun j _ => h j)

/-- A property of naturals that holds somewhere holds at a least place. -/
theorem exists_least (P : Nat → Prop) [DecidablePred P] (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m < n, ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hm : ∃ m < n, P m
    · obtain ⟨m, hlt, hPm⟩ := hm
      exact ih m hlt hPm
    · exact ⟨n, hn, fun m hlt hPm => hm ⟨m, hlt, hPm⟩⟩

/-- What `index` is: the least occurrence, or `-1` if there is none. -/
theorem index_cases (s sep : List w8) :
    (∃ i : Nat, index s sep = i ∧ sep <+: s.drop i ∧ ∀ j < i, ¬ sep <+: s.drop j) ∨
    (index s sep = -1 ∧ ∀ j, ¬ sep <+: s.drop j) := by
  by_cases h : ∃ j, sep <+: s.drop j
  · obtain ⟨i, hi, hmin⟩ := exists_least _ h
    exact Or.inl ⟨i, index_eq_of s sep i hi hmin, hi, hmin⟩
  · have h' : ∀ j, ¬ sep <+: s.drop j := fun j hj => h ⟨j, hj⟩
    exact Or.inr ⟨index_eq_neg s sep h', h'⟩

theorem index_bounds (s sep : List w8) :
    -1 ≤ index s sep ∧ (0 ≤ index s sep → index s sep + sep.length ≤ s.length) := by
  rcases index_cases s sep with ⟨i, hi, hp, -⟩ | ⟨hi, hn⟩
  · have := hp.length_le
    simp only [List.length_drop] at this
    have : i ≤ s.length := by
      refine Classical.byContradiction fun hc => ?_
      have : sep.length = 0 := by omega
      have hsep : sep = [] := List.eq_nil_of_length_eq_zero this
      have := index_eq_of s sep 0 (by simp [hsep]) (by simp)
      omega
    omega
  · rw [hi]; omega

/-- No occurrence before `i`: the first occurrence in `s` is the first in `s.drop i`, shifted. -/
theorem index_drop (s sep : List w8) (i : Nat) (h : ∀ k < i, ¬ sep <+: s.drop k) :
    index s sep = if 0 ≤ index (s.drop i) sep then index (s.drop i) sep + i else -1 := by
  rcases index_cases (s.drop i) sep with ⟨r, hr, hp, hmin⟩ | ⟨hr, hn⟩
  · rw [hr]
    simp only [Int.natCast_nonneg, ↓reduceIte]
    rw [List.drop_drop] at hp
    rw [show (r : Int) + i = ((i + r : Nat) : Int) by omega]
    refine index_eq_of s sep (i + r) hp (fun k hk => ?_)
    rcases Nat.lt_or_ge k i with hki | hki
    · exact h k hki
    · have := hmin (k - i) (by omega)
      rwa [List.drop_drop, show i + (k - i) = k by omega] at this
  · rw [hr]
    simp only [Int.reduceNeg, Int.reduceLE, ↓reduceIte]
    refine index_eq_neg s sep (fun k => ?_)
    rcases Nat.lt_or_ge k i with hki | hki
    · exact h k hki
    · have := hn (k - i)
      rwa [List.drop_drop, show i + (k - i) = k by omega] at this

/-- `sep` does not occur where the rest of `s` is shorter than `sep`. -/
theorem not_prefix_drop_of_long (s sep : List w8) (k : Nat) (hne : 0 < sep.length)
    (hk : s.length < k + sep.length) : ¬ sep <+: s.drop k := fun hp => by
  have := hp.length_le; simp only [List.length_drop] at this; omega

/-- `sep` (of first byte `c`) does not occur where `s` does not have `c`. -/
theorem not_prefix_drop_of_head (s rest : List w8) (c : w8) (k : Nat) (hk : s[k]? ≠ some c) :
    ¬ (c :: rest) <+: s.drop k := fun ⟨t, ht⟩ => hk (by
  have := congrArg (fun l => l[0]?) ht
  simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero] at this
  exact this.symm)

/-- `sep` does not occur at `k` if its byte `j` is not `s`'s byte `k + j`. -/
theorem not_prefix_drop_of_getElem (s sep : List w8) (c : w8) (j k : Nat)
    (hj : sep[j]? = some c) (hk : s[k + j]? ≠ some c) : ¬ sep <+: s.drop k := fun ⟨t, ht⟩ =>
  hk (by
    have := congrArg (fun l => l[j]?) ht
    simp only [List.getElem?_drop] at this
    rw [← this, List.getElem?_append_left (by
      rcases Nat.lt_or_ge j sep.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hj), hj])

/-! ## The first index of a byte -/

/-- The first index of `c` in `s`, or `-1`: the first index of the one-byte string `[c]`. -/
def indexByte (s : List w8) (c : w8) : Int := index s [c]

theorem singleton_prefix_drop (s : List w8) (c : w8) (j : Nat) :
    [c] <+: s.drop j ↔ s[j]? = some c := by
  rw [List.singleton_prefix_iff_head?_eq_some, List.head?_drop]

theorem indexByte_eq_of (s : List w8) (c : w8) (i : Nat) (hc : s[i]? = some c)
    (hmin : ∀ j < i, s[j]? ≠ some c) : indexByte s c = i :=
  index_eq_of s [c] i ((singleton_prefix_drop s c i).2 hc)
    (fun j hj h => hmin j hj ((singleton_prefix_drop s c j).1 h))

theorem indexByte_eq_neg (s : List w8) (c : w8) (h : ∀ j : Nat, s[j]? ≠ some c) :
    indexByte s c = -1 :=
  index_eq_neg s [c] (fun j hj => h j ((singleton_prefix_drop s c j).1 hj))

/-- The first index of `c` in the substring `s[a:a+b]`. -/
theorem indexByte_slice_cases (s : List w8) (c : w8) (a b : Nat) :
    (∃ r : Nat, indexByte ((s.drop a).take b) c = r ∧ r < b ∧ s[a + r]? = some c ∧
      ∀ j < r, s[a + j]? ≠ some c) ∨
    (indexByte ((s.drop a).take b) c = -1 ∧ ∀ j < b, s[a + j]? ≠ some c) := by
  have key : ∀ j, ((s.drop a).take b)[j]? = some c ↔ j < b ∧ s[a + j]? = some c := by
    intro j
    rw [List.getElem?_take, List.getElem?_drop]
    split <;> (simp_all; try omega)
  rcases index_cases ((s.drop a).take b) [c] with ⟨r, hr, hp, hmin⟩ | ⟨hr, hn⟩
  · rw [singleton_prefix_drop, key] at hp
    refine Or.inl ⟨r, hr, hp.1, hp.2, fun j hj h => hmin j hj ?_⟩
    rw [singleton_prefix_drop, key]
    exact ⟨by omega, h⟩
  · refine Or.inr ⟨hr, fun j hj h => hn j ?_⟩
    rw [singleton_prefix_drop, key]
    exact ⟨hj, h⟩

theorem indexByte_bounds (s : List w8) (c : w8) :
    -1 ≤ indexByte s c ∧ indexByte s c < s.length := by
  have := index_bounds s [c]
  simp only [List.length_singleton] at this
  unfold indexByte; omega

/-! ## Rabin-Karp hashes, mod 2^32 -/

/-- `PrimeRK`, the base of the Rabin-Karp hashes. -/
abbrev primeRK : w32 := W32 16777619

/-- `HashStr`'s hash of `s`: its bytes as the digits, most significant first, of a number in base
`primeRK`, mod 2^32. -/
def hashStr (s : List w8) : w32 := s.foldl (fun h b => h * primeRK + W32 (uint.Z b)) 0

/-- `HashStrRev`'s hash of `s`: the hash of its reverse. -/
def hashStrRev (s : List w8) : w32 := hashStr s.reverse

/-- `primeRK ^ n`, mod 2^32: `HashStr`'s multiplicative factor for a pattern of length `n`. -/
def powRK : Nat → w32
  | 0 => 1
  | n + 1 => powRK n * primeRK

theorem powRK_add (m n : Nat) : powRK (m + n) = powRK m * powRK n := by
  induction n with
  | zero => simp [powRK]
  | succ n ih => rw [← Nat.add_assoc, powRK, powRK, ih]; grind

theorem powRK_eq_pow (n : Nat) : powRK n = primeRK ^ n := by
  induction n with
  | zero => simp [powRK]
  | succ n ih => rw [powRK, ih, BitVec.pow_succ]

theorem sq_pow (q : w32) (m : Nat) : (q * q) ^ m = q ^ (2 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [BitVec.pow_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, BitVec.pow_succ,
      BitVec.pow_succ]
    grind

/-- The step of `HashStr`'s square-and-multiply loop for `PrimeRK ^ len(sep)`. -/
theorem pow_halve (q : w32) (k : Nat) :
    q ^ k = (if k % 2 = 1 then q else 1) * (q * q) ^ (k / 2) := by
  rw [sq_pow]
  obtain ⟨m, rfl | rfl⟩ : ∃ m, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
  · rw [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
    simp
  · rw [show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
    simp only [↓reduceIte, BitVec.pow_succ]
    grind

/-- `i >>= 1` on a non-negative `int`. -/
theorem sshiftRight'_one_nat (k : Nat) (hk : k < 2 ^ 63) :
    BitVec.sshiftRight' (W64 (k : Int)) (W64 1) = W64 ((k / 2 : Nat) : Int) := by
  have hx : W64 (k : Int) = BitVec.ofNat 64 k := by simp [W64]
  rw [hx]
  apply BitVec.eq_of_toNat_eq
  have : (BitVec.ofNat 64 k).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp [BitVec.sshiftRight', BitVec.sshiftRight_eq_of_msb_false this, W64]
  omega

/-- `i & 1 == 0` on a non-negative `int`. -/
theorem and_one_eq_zero_nat (k : Nat) (_hk : k < 2 ^ 63) :
    (W64 (k : Int) &&& W64 1 = W64 0) ↔ k % 2 = 0 := by
  have hx : W64 (k : Int) = BitVec.ofNat 64 k := by simp [W64]
  rw [hx, ← BitVec.toNat_inj]
  simp [W64]

theorem hashStr_append_singleton (s : List w8) (b : w8) :
    hashStr (s ++ [b]) = hashStr s * primeRK + W32 (uint.Z b) := by
  simp [hashStr, List.foldl_append]

theorem foldl_hash_init (s : List w8) (h0 : w32) :
    s.foldl (fun h b => h * primeRK + W32 (uint.Z b)) h0 =
      h0 * powRK s.length + hashStr s := by
  induction s generalizing h0 with
  | nil => simp [hashStr, powRK]
  | cons x s ih =>
    simp only [List.foldl_cons, List.length_cons, hashStr]
    rw [ih, ih (0 * primeRK + W32 (uint.Z x))]
    rw [show powRK (s.length + 1) = powRK 1 * powRK s.length by
      rw [Nat.add_comm]; exact powRK_add 1 s.length]
    simp only [powRK]
    grind

theorem hashStr_cons (x : w8) (s : List w8) :
    hashStr (x :: s) = W32 (uint.Z x) * powRK s.length + hashStr s := by
  rw [hashStr, List.foldl_cons, foldl_hash_init]
  grind

/-- The forward rolling step: drop the first byte `x` of a window of length `n`, add `y`. -/
theorem hashStr_roll (x y : w8) (w : List w8) :
    (hashStr (x :: w) * primeRK + W32 (uint.Z y)) - powRK (w.length + 1) * W32 (uint.Z x) =
      hashStr (w ++ [y]) := by
  rw [hashStr_cons, hashStr_append_singleton, powRK]
  grind

/-- The forward rolling step on the windows of length `n` of `s`: from the window at `t` to the
window at `t + 1`. -/
theorem hashStr_window_roll (s : List w8) (n t : Nat) (x y : w8) (hn : 0 < n)
    (hx : s[t]? = some x) (hy : s[t + n]? = some y) :
    (hashStr ((s.drop t).take n) * primeRK + W32 (uint.Z y)) - powRK n * W32 (uint.Z x) =
      hashStr ((s.drop (t + 1)).take n) := by
  have ht : t < s.length := by
    rcases Nat.lt_or_ge t s.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hx
  have hdrop : s.drop t = x :: s.drop (t + 1) := by
    rw [List.drop_eq_getElem_cons ht]
    rw [List.getElem?_eq_getElem ht] at hx
    rw [Option.some.inj hx]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw : (s.drop t).take (m + 1) = x :: (s.drop (t + 1)).take m := by
    rw [hdrop, List.take_succ_cons]
  have hw' : (s.drop (t + 1)).take (m + 1) = (s.drop (t + 1)).take m ++ [y] := by
    rw [List.take_add_one, List.getElem?_drop,
      show t + 1 + m = t + (m + 1) by omega, hy, Option.toList_some]
  have hlen : ((s.drop (t + 1)).take m).length = m := by
    have : t + (m + 1) < s.length := by
      rcases Nat.lt_or_ge (t + (m + 1)) s.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hy
    simp only [List.length_take, List.length_drop]; omega
  rw [hw, hw', ← hashStr_roll x y, hlen]

theorem hashStrRev_cons (x : w8) (s : List w8) :
    hashStrRev (x :: s) = hashStrRev s * primeRK + W32 (uint.Z x) := by
  simp [hashStrRev, hashStr_append_singleton]

theorem hashStrRev_append_singleton (s : List w8) (y : w8) :
    hashStrRev (s ++ [y]) = W32 (uint.Z y) * powRK s.length + hashStrRev s := by
  simp [hashStrRev, hashStr_cons]

/-- The backward rolling step: drop the last byte `y` of a window of length `n`, add `x` in
front. -/
theorem hashStrRev_roll (x y : w8) (w : List w8) :
    (hashStrRev (w ++ [y]) * primeRK + W32 (uint.Z x)) - powRK (w.length + 1) * W32 (uint.Z y) =
      hashStrRev (x :: w) := by
  rw [hashStrRev_cons, hashStrRev_append_singleton, powRK]
  grind

/-- The backward rolling step on the windows of length `n` of `s`: from the window at `i + 1` to
the window at `i`. -/
theorem hashStrRev_window_roll (s : List w8) (n i : Nat) (x y : w8) (hn : 0 < n)
    (hx : s[i]? = some x) (hy : s[i + n]? = some y) :
    (hashStrRev ((s.drop (i + 1)).take n) * primeRK + W32 (uint.Z x)) - powRK n * W32 (uint.Z y) =
      hashStrRev ((s.drop i).take n) := by
  have hi : i < s.length := by
    rcases Nat.lt_or_ge i s.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hx
  have hdrop : s.drop i = x :: s.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi]
    rw [List.getElem?_eq_getElem hi] at hx
    rw [Option.some.inj hx]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw : (s.drop i).take (m + 1) = x :: (s.drop (i + 1)).take m := by
    rw [hdrop, List.take_succ_cons]
  have hw' : (s.drop (i + 1)).take (m + 1) = (s.drop (i + 1)).take m ++ [y] := by
    rw [List.take_add_one, List.getElem?_drop,
      show i + 1 + m = i + (m + 1) by omega, hy, Option.toList_some]
  have hlen : ((s.drop (i + 1)).take m).length = m := by
    have : i + (m + 1) < s.length := by
      rcases Nat.lt_or_ge (i + (m + 1)) s.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hy
    simp only [List.length_take, List.length_drop]; omega
  rw [hw, hw', ← hashStrRev_roll x y, hlen]

end internal.bytealg

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

namespace internal.bytealg

/-- The package-initialized state (persistent: nothing writes `MaxLen` after `init`):
`MaxLen` holds 31 or 63 (`init.0`'s Go model, goose/model/overlay/internal/bytealg/init.go). -/
abbrev isInit : IProp GF :=
  iprop(∃ m : w64, globalAddr MaxLen ↦□ m ∗ ⌜m = W64 31 ∨ m = W64 63⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.bytealg

end internal.bytealg

end wps

end Perennial
