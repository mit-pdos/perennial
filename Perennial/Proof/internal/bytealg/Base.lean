/-
Shared definitions of the proofs of `internal/bytealg`: the first occurrence of a substring
(`firstOcc`, and `indexResult`, what Go's `Index` returns), `compareResult`, the Rabin-Karp hash
(`rkHash`) and lemmas about them, and the package's `isPkgInit` (`MaxLen`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.bytealg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.bytealg

/-! ## Occurrences of a substring -/

/-- The index of the first occurrence of `sub` in `s` (the least `k` with `sub` a prefix of
`s.drop k`), if there is one. -/
def firstOcc (s sub : GoString) : Option Nat :=
  match s with
  | [] => if sub <+: [] then some 0 else none
  | c :: r => if sub <+: c :: r then some 0 else (firstOcc r sub).map (· + 1)

/-- What Go's `Index(s, sub)` returns: the index of the first occurrence of `sub` in `s`, or
`-1`. -/
def indexResult (s sub : GoString) : w64 :=
  match firstOcc s sub with
  | some k => W64 k
  | none => W64 (-1)

example : firstOcc go!"abcbc" go!"bc" = some 1 := by decide
example : firstOcc go!"abcbc" go!"cc" = none := by decide
example : firstOcc go!"abc" go!"" = some 0 := by decide

/-- `firstOcc s sub = some k`: `sub` occurs at `k` and at no earlier index. -/
theorem firstOcc_eq_some_iff (s sub : GoString) (k : Nat) :
    firstOcc s sub = some k ↔
      k ≤ s.length ∧ sub <+: s.drop k ∧ ∀ i, i < k → ¬ sub <+: s.drop i := by
  induction s generalizing k with
  | nil =>
    unfold firstOcc
    by_cases h : sub <+: []
    · rw [ite_eq_left h]
      constructor
      · rintro ⟨⟩; exact ⟨Nat.le_refl _, h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      · rintro ⟨hk, -, -⟩; simp at hk; rw [hk]
    · rw [ite_eq_right h]
      constructor
      · intro h'; cases h'
      · rintro ⟨hk, hp, -⟩; simp at hk; subst hk; exact absurd hp h
  | cons c r ih =>
    unfold firstOcc
    by_cases h : sub <+: c :: r
    · rw [ite_eq_left h]
      constructor
      · rintro ⟨⟩; exact ⟨Nat.zero_le _, h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      · rintro ⟨-, -, hk⟩
        cases k with
        | zero => rfl
        | succ k => exact absurd h (hk 0 (Nat.succ_pos _))
    · rw [ite_eq_right h]
      constructor
      · intro h'
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 h'
        obtain ⟨h1, h2, h3⟩ := (ih k').1 hk'
        refine ⟨by simp; omega, by simpa using h2, fun i hi => ?_⟩
        cases i with
        | zero => exact h
        | succ i => simpa using h3 i (by omega)
      · rintro ⟨h1, h2, h3⟩
        cases k with
        | zero => exact absurd h2 h
        | succ k =>
          refine Option.map_eq_some_iff.2 ⟨k, (ih k).2 ⟨?_, ?_, ?_⟩, rfl⟩
          · simp at h1; omega
          · simpa using h2
          · intro i hi; simpa using h3 (i + 1) (by omega)

/-- `firstOcc s sub = none`: `sub` occurs nowhere in `s`. -/
theorem firstOcc_eq_none_iff (s sub : GoString) :
    firstOcc s sub = none ↔ ∀ i, i ≤ s.length → ¬ sub <+: s.drop i := by
  induction s with
  | nil =>
    unfold firstOcc
    by_cases h : sub <+: []
    · rw [ite_eq_left h]
      simp only [reduceCtorEq, false_iff]
      exact fun H => H 0 (Nat.le_refl _) (by simpa using h)
    · rw [ite_eq_right h]
      simp only [true_iff]
      intro i hi; simp at hi; subst hi; simpa using h
  | cons c r ih =>
    unfold firstOcc
    by_cases h : sub <+: c :: r
    · rw [ite_eq_left h]
      simp only [reduceCtorEq, false_iff]
      exact fun H => H 0 (Nat.zero_le _) (by simpa using h)
    · rw [ite_eq_right h, Option.map_eq_none_iff, ih]
      constructor
      · intro H i hi
        cases i with
        | zero => simpa using h
        | succ i => simpa using H i (by simp at hi; omega)
      · intro H i hi
        simpa using H (i + 1) (by simp; omega)

/-- Where `firstOcc` finds `sub`, `sub` occurs. -/
theorem occ_of_firstOcc (s sub : GoString) (k : Nat) (h : firstOcc s sub = some k) :
    sub <+: s.drop k := ((firstOcc_eq_some_iff s sub k).1 h).2.1

/-- A non-empty `sub` does not occur where fewer than `len(sub)` bytes are left. -/
theorem not_occ_of_short (s sub : GoString) (hsub : sub ≠ []) (i : Nat)
    (h : s.length < i + sub.length) :
    ¬ sub <+: s.drop i := by
  intro hp
  have := hp.length_le
  have := List.length_pos_iff.2 hsub
  simp only [List.length_drop] at *
  omega

/-- The bytes `s[i:i+len(sub)]` are `sub` iff `sub` occurs at `i`. -/
theorem slice_eq_iff_occ (s sub : GoString) (i : Nat) :
    (s.drop i).take sub.length = sub ↔ sub <+: s.drop i := by
  constructor
  · intro h
    rw [← h]
    exact List.take_prefix _ _
  · intro h
    exact (List.prefix_iff_eq_take.1 h).symm

/-- A one-byte `sub` occurs at `i` iff `s[i] = c`. -/
theorem occ_singleton_iff (s : GoString) (c : w8) (i : Nat) :
    [c] <+: s.drop i ↔ s[i]? = some c := by
  rw [List.prefix_iff_eq_take]
  simp only [List.length_singleton]
  constructor
  · intro h
    have : (s.drop i)[0]? = some c := by
      rw [← List.getElem?_take_of_lt (show 0 < 1 by omega), ← h]; rfl
    simpa using this
  · intro h
    have hlt : i < s.length := by
      rcases Nat.lt_or_ge i s.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; cases h
    rw [List.take_one, List.head?_drop, h]
    rfl
/-- With no occurrence before `i`, the first occurrence in `s` is `i` plus the first one in
`s[i:]`. -/
theorem firstOcc_drop (s sub : GoString) (i : Nat) (hi : i ≤ s.length)
    (hnone : ∀ j, j < i → ¬ sub <+: s.drop j) :
    firstOcc s sub = (firstOcc (s.drop i) sub).map (· + i) := by
  rcases h : firstOcc (s.drop i) sub with _ | k
  · rw [Option.map_none, firstOcc_eq_none_iff]
    intro j hj
    rcases Nat.lt_or_ge j i with hj' | hj'
    · exact hnone j hj'
    · have := (firstOcc_eq_none_iff _ _).1 h (j - i) (by simp; omega)
      rwa [List.drop_drop, show i + (j - i) = j by omega] at this
  · obtain ⟨h1, h2, h3⟩ := (firstOcc_eq_some_iff _ _ _).1 h
    rw [Option.map_some, firstOcc_eq_some_iff]
    simp only [List.length_drop, List.drop_drop] at h1 h2 h3
    refine ⟨by omega, by rwa [Nat.add_comm], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j i with hj' | hj'
    · exact hnone j hj'
    · have := h3 (j - i) (by omega)
      rwa [show i + (j - i) = j by omega] at this

/-- Where `c :: r` occurs, `s` has `c`. -/
theorem occ_head (s r : GoString) (c : w8) (j : Nat) (h : (c :: r) <+: s.drop j) :
    s[j]? = some c := by
  obtain ⟨t, ht⟩ := h
  have := congrArg (·[0]?) ht
  simpa using this.symm

/-- Where `c0 :: c1 :: r` occurs at `j`, `s` has `c1` at `j + 1`. -/
theorem occ_second (s r : GoString) (c0 c1 : w8) (j : Nat) (h : (c0 :: c1 :: r) <+: s.drop j) :
    s[j + 1]? = some c1 := by
  obtain ⟨t, ht⟩ := h
  have := congrArg (·[1]?) ht
  simp at this
  rw [← this]

/-- The empty string occurs at 0. -/
theorem indexResult_nil (s : GoString) : indexResult s [] = W64 0 := by
  unfold indexResult
  rw [(firstOcc_eq_some_iff s [] 0).2
    ⟨Nat.zero_le _, List.nil_prefix, fun i hi => absurd hi (by omega)⟩]; rfl

/-- A string at least as long as `s` occurs in `s` only if it is `s`, at 0. -/
theorem indexResult_of_length_ge (s sub : GoString) (h : s.length ≤ sub.length) :
    indexResult s sub = if sub = s then W64 0 else W64 (-1) := by
  by_cases heq : sub = s
  · subst heq
    rw [ite_eq_left rfl]
    unfold indexResult
    rw [(firstOcc_eq_some_iff sub sub 0).2
      ⟨Nat.zero_le _, by simp, fun i hi => absurd hi (by omega)⟩]; rfl
  · rw [ite_eq_right heq]
    unfold indexResult
    rw [(firstOcc_eq_none_iff s sub).2]
    intro i hi hp
    have hlen := hp.length_le
    simp only [List.length_drop] at hlen
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [List.drop_zero] at hp
      exact heq (hp.eq_of_length (by omega))
    · have := List.length_pos_iff.2 (show sub ≠ [] by
        rintro rfl; simp only [List.length_nil, Nat.le_zero] at h; omega)
      omega

/-- `indexResult s sub` is `k` when `sub` occurs first at `k`. -/
theorem indexResult_of_occ (s sub : GoString) (k : w64) (hk : 0 ≤ sint.Z k)
    (hle : sint.nat k ≤ s.length) (hocc : sub <+: s.drop (sint.nat k))
    (hnone : ∀ j, j < sint.nat k → ¬ sub <+: s.drop j) :
    indexResult s sub = k := by
  unfold indexResult
  rw [(firstOcc_eq_some_iff s sub (sint.nat k)).2 ⟨hle, hocc, hnone⟩]
  simp only
  word

/-- `indexResult s sub` is `-1` when `sub` does not occur. -/
theorem indexResult_of_none (s sub : GoString) (hnone : ∀ j, j ≤ s.length → ¬ sub <+: s.drop j) :
    indexResult s sub = W64 (-1) := by
  unfold indexResult
  rw [(firstOcc_eq_none_iff s sub).2 hnone]


/-- The two cases of `indexResult`. -/
theorem indexResult_cases (s sub : GoString) :
    (∃ k, firstOcc s sub = some k ∧ indexResult s sub = W64 k ∧ k ≤ s.length) ∨
      (firstOcc s sub = none ∧ indexResult s sub = W64 (-1)) := by
  unfold indexResult
  rcases h : firstOcc s sub with _ | k
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨k, rfl, rfl, ((firstOcc_eq_some_iff _ _ _).1 h).1⟩

/-- What Go's `Compare(a, b)` returns: `-1`, `0` or `+1` as `a` is lexicographically less than,
equal to or greater than `b` (Go's `<` on strings, `GoStringLt`). -/
def compareResult (a b : GoString) : w64 :=
  if go.GoStringLt a b then W64 (-1) else if a = b then W64 0 else W64 1

/-! ## The Rabin-Karp hash -/

/-- `PrimeRK`, the base of the Rabin-Karp hash. -/
def primeRK : w32 := W32 16777619

/-- The Rabin-Karp hash of `w`, `w[0]·P^(n-1) + ... + w[n-1]` modulo `2^32` (what `HashStr`'s
first loop computes), from the hash `h` of what comes before `w`. -/
def rkHashFrom (h : w32) (w : GoString) : w32 :=
  w.foldl (fun h c => h * primeRK + W32 (uint.Z c)) h

/-- The Rabin-Karp hash of `w`. -/
def rkHash (w : GoString) : w32 := rkHashFrom 0 w

theorem rkHashFrom_eq (h : w32) (w : GoString) :
    rkHashFrom h w = h * primeRK ^ w.length + rkHash w := by
  unfold rkHash rkHashFrom
  induction w generalizing h with
  | nil => simp
  | cons c w ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * primeRK + W32 (uint.Z c))]
    grind

theorem rkHash_snoc (w : GoString) (c : w8) :
    rkHash (w ++ [c]) = rkHash w * primeRK + W32 (uint.Z c) := by
  unfold rkHash rkHashFrom
  simp

theorem rkHash_cons (c : w8) (w : GoString) :
    rkHash (c :: w) = W32 (uint.Z c) * primeRK ^ w.length + rkHash w := by
  show rkHashFrom (0 * primeRK + W32 (uint.Z c)) w = _
  rw [rkHashFrom_eq]
  grind

/-- The hash of the window one byte on: drop the first byte `c0` of a window of `n + 1` bytes
and append `c`. -/
theorem rkHash_roll (c0 c : w8) (w : GoString) :
    rkHash (c0 :: w) * primeRK + W32 (uint.Z c) -
        primeRK ^ (w.length + 1) * W32 (uint.Z c0) =
      rkHash (w ++ [c]) := by
  rw [rkHash_cons, rkHash_snoc]
  grind

/-- The window of `n ≥ 1` bytes of `s` at `a`, and the one at `a + 1`: the first drops `s[a]`
and the second appends `s[a+n]`. -/
theorem window_step (s : GoString) (a n : Nat) (hn : 0 < n) (h : a + n < s.length) :
    ∃ c0 c w, (s.drop a).take n = c0 :: w ∧ (s.drop (a + 1)).take n = w ++ [c] ∧
      s[a]? = some c0 ∧ s[a + n]? = some c ∧ w.length + 1 = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨s[a], s[a + (m + 1)], (s.drop (a + 1)).take m, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
  · rw [List.take_add_one, List.getElem?_drop, show a + 1 + m = a + (m + 1) by omega,
      List.getElem?_eq_getElem (by omega)]
    rfl
  · exact List.getElem?_eq_getElem (by omega)
  · exact List.getElem?_eq_getElem (by omega)
  · simp; omega

theorem pow_sq (x : w32) (k : Nat) : (x * x) ^ k = x ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, BitVec.pow_succ, ih]; grind

/-- For a non-negative `int` `i`, `i & 1 == 0` says that `i` is even. -/
theorem and_one_eq_zero_iff (i : w64) (h : 0 ≤ sint.Z i) :
    (i &&& W64 1 = W64 0) ↔ sint.nat i % 2 = 0 := by
  have hn : sint.nat i = i.toNat := by word
  rw [hn, ← BitVec.toNat_inj, BitVec.toNat_and]
  have h1 : (W64 1).toNat = 1 := by decide
  have h0 : (W64 0).toNat = 0 := by decide
  rw [h1, h0, Nat.and_one_is_mod]

/-- For a non-negative `int` `i`, `i >> 1` is `i / 2`. -/
theorem sshiftRight_one (i : w64) (h : 0 ≤ sint.Z i) :
    sint.Z (BitVec.sshiftRight' i (W64 1)) = sint.Z i / 2 := by
  have hmsb : i.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; word
  simp only [BitVec.sshiftRight']
  have h1 : (W64 1).toNat = 1 := by decide
  rw [h1, BitVec.sshiftRight_eq_of_msb_false hmsb]
  have := BitVec.toNat_ushiftRight i 1
  rw [Nat.shiftRight_eq_div_pow] at this
  word

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- The package-initialized state: `MaxLen` holds 31 or 63 (as the CPU has AVX2 or not) and is
never written again. -/
abbrev isInit : IProp GF :=
  iprop(∃ m : w64, typedPointsto (globalAddr MaxLen) m DFrac.discard ∗
    ⌜m = W64 31 ∨ m = W64 63⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

omit package_sem in
/-- The `MaxLen` of an initialized `bytealg`. -/
theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.bytealg

end wps

end internal.bytealg

end Perennial
end
