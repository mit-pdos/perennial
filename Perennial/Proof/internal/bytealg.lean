/-
Specs for `internal/bytealg`.
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

omit package_sem in
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.bytealg get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w64) MaxLen go.int as HM
  unfold MaxLenAddr
  rw [show (go!"internal/bytealg.MaxLen" : GoString) = MaxLen from rfl]
  wp_bind ArbitraryInt
  wp_apply wp_ArbitraryInt as %x _
  iapply wp_fupd
  wp_if_destruct
  all_goals
    ipersist HM
    imodintro
    iframe Hown
    isPkgInit_unfold
    isplitl []
    · ipureintro; simp
    imodintro
    iexists _
    iframe HM
    ipureintro
    simp

/-- `bytealg.MakeNoZero(n)`, for `0 ≤ n ≤ maxAlloc`: a new slice of `n` bytes (zero in the
model, unspecified in Go: a caller must not read a byte before writing it). -/
theorem wp_MakeNoZero (n : w64) (Hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ maxAlloc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val (@! MakeNoZero)) (Val #n))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* List.replicate (sint.nat n) (W8 0) ∗ ownSliceCap w8 sl (DFrac.own 1) }} := by
  wp_start
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  have Hmax : sint.Z (W64 maxAlloc) = maxAlloc := by unfold maxAlloc; word
  rw [decide_eq_false (show ¬ sint.Z (W64 maxAlloc) < sint.Z n by rw [Hmax]; omega)]
  wp_auto
  wp_apply wp_new_cap with %cap %Hcap
  wp_apply wp_slice_make3 (V := w8) n cap ⟨Hn.1, Hcap⟩ with %sl ⟨Hsl, Hsl_cap, -⟩
  iapply HΦ
  iframe
/-- `bytealg.IndexByteString(s, c)`: the index of the first `c` in `s`, or `-1`. -/
theorem wp_IndexByteString (s : GoString) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! IndexByteString)) (Val #s)) (Val #c))
    {{ RET #(indexResult s [c]); True }} := by
  wp_start
  have H0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ s.length ∧
      ∀ j, j < sint.nat (W64 0) → ¬ [c] <+: s.drop j :=
    ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  generalize W64 0 = i at H0 ⊢
  iloeb as IH generalizing %i %H0
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have hlt : sint.nat i < s.length := by word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [H0.1, ↓reduceIte, hb]
    wp_auto
    wp_if_destruct
    · subst Hif
      rw [← indexResult_of_occ s [b] i H0.1 (by omega) ((occ_singleton_iff _ _ _).2 hb) H0.2.2]
      iapply HΦ; itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          ∀ j, j < sint.nat (i + W64 1) → ¬ [c] <+: s.drop j := by
        refine ⟨by word, by word, fun j hj => ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact H0.2.2 j hj'
        · obtain rfl : j = sint.nat i := by omega
          rw [occ_singleton_iff, hb]
          intro h; cases h; exact Hif rfl
      iapply IH $$ %(i + W64 1) %H1 HΦ
  · rw [indexResult_of_none s [c] ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
    · exact H0.2.2 j hj'
    · exact not_occ_of_short s [c] (by simp) j (by simp; word)

/-- `CountString.loop s c i n`, for `n` the number of `c`s in `s[:i]`: the number of `c`s in
`s`. -/
theorem wp_CountString_loop (s : GoString) (c : w8) (i n : w64)
    (H : 0 ≤ sint.Z i ∧ sint.Z i ≤ s.length ∧ n = W64 ((s.take (sint.nat i)).count c)) :
    {{ (True : IProp GF) }}
      (App (App (App (App (Val CountString.loop) (Val #s)) (Val #c)) (Val #i)) (Val #n))
    {{ RET #(W64 (s.count c)); True }} := by
  iintro %Φ _ HΦ
  wp_call
  iloeb as IH generalizing %i %n %H
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have hlt : sint.nat i < s.length := by word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [H.1, ↓reduceIte, hb]
    wp_auto
    have Htake : s.take (sint.nat (i + W64 1)) = s.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hb]; rfl
    wp_if_destruct
    · subst Hif
      have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          n + W64 1 = W64 ((s.take (sint.nat (i + W64 1))).count b) := by
        refine ⟨by word, by word, ?_⟩
        rw [Htake, List.count_append, H.2.2]; simp; word
      wp_call
      iapply IH $$ %(i + W64 1) %(n + W64 1) %H1 [] HΦ
      itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          n = W64 ((s.take (sint.nat (i + W64 1))).count c) := by
        refine ⟨by word, by word, ?_⟩
        rw [Htake, List.count_append, H.2.2]
        simp [Hif]
      wp_call
      iapply IH $$ %(i + W64 1) %n %H1 [] HΦ
      itrivial
  · rw [H.2.2, show sint.nat i = s.length by word, List.take_length]
    iapply HΦ; itrivial

/-- `bytealg.CountString(s, c)`: the number of `c`s in `s`. -/
theorem wp_CountString (s : GoString) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! CountString)) (Val #s)) (Val #c))
    {{ RET #(W64 (s.count c)); True }} := by
  wp_start
  wp_apply wp_CountString_loop s c (W64 0) (W64 0) ⟨by decide, by word, by simp [sint.nat]⟩
  iapply HΦ; itrivial
/-- `bytealg.IndexString(a, b)`, for `2 ≤ len(b) ≤ MaxLen`: the index of the first occurrence of
`b` in `a`, or `-1`. -/
theorem wp_IndexString (a b : GoString) (m : w64) (Hb : 2 ≤ b.length ∧ b.length ≤ sint.Z m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg ∗
        typedPointsto (globalAddr MaxLen) m DFrac.discard }}
      (App (App (Val (@! IndexString)) (Val #a)) (Val #b))
    {{ RET #(indexResult a b); True }} := by
  wp_start as #HM
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hblen
  unfold MaxLenAddr
  rw [show (go!"internal/bytealg.MaxLen" : GoString) = MaxLen from rfl,
    decide_eq_false (show ¬ sint.Z (W64 b.length) < sint.Z (W64 2) by word)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z m < sint.Z (W64 b.length) by word)]
  wp_auto
  have H0 : 0 ≤ sint.Z (W64 0) ∧ ∀ j, j < sint.nat (W64 0) → ¬ b <+: a.drop j :=
    ⟨by decide, fun j hj => by simp at hj; omega⟩
  generalize W64 0 = i at H0 ⊢
  iloeb as IH generalizing %i %H0
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Ha
  have Hsub : sint.Z (W64 a.length - W64 b.length) = a.length - b.length := by word
  wp_if_destruct
  · rw [Hsub] at Hif
    have Hk : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 b.length) ∧
        sint.Z (i + W64 b.length) ≤ a.length := by word
    rw [ite_eq_left Hk]
    wp_auto
    have Hlen : sint.nat (i + W64 b.length) - sint.nat i = b.length := by word
    rw [Hlen]
    wp_if_destruct
    · rw [← indexResult_of_occ a b i H0.1 (by word) ((slice_eq_iff_occ _ _ _).1 Hif) H0.2]
      iapply HΦ; itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧
          ∀ j, j < sint.nat (i + W64 1) → ¬ b <+: a.drop j := by
        refine ⟨by word, fun j hj => ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact H0.2 j hj'
        · obtain rfl : j = sint.nat i := by omega
          rw [← slice_eq_iff_occ]; exact Hif
      iapply IH $$ %(i + W64 1) %H1 HΦ
  · rw [Hsub] at Hif
    rw [indexResult_of_none a b ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
    · exact H0.2 j hj'
    · exact not_occ_of_short a b (by rintro rfl; simp at Hb) j (by word)

/-- `bytealg.HashStr(sep)`, at type `string`: the Rabin-Karp hash of `sep` and `PrimeRK` to the
power `len(sep)`. -/
theorem wp_HashStr (sep : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val #(functions HashStr [go.string])) (Val #sep))
    {{ RET (PairV #(rkHash sep) #(primeRK ^ sep.length)); True }} := by
  wp_start
  wp_auto
  ihave IH : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "hash" ∷ hash_ptr ↦ rkHash (sep.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sep.length⌝) $$ [i hash]
  · iexists (W64 0)
    rw [show rkHash (sep.take (sint.nat (W64 0))) = W32 0 from rfl]
    iframe
    ipureintro
    exact ⟨by decide, by word⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have hlt : sint.nat i < sep.length := by word
    obtain ⟨c, hc⟩ : ∃ c, sep[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, ↓reduceIte, hc]
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    have Htake : sep.take (sint.nat (i + W64 1)) = sep.take (sint.nat i) ++ [c] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hc]; rfl
    rw [Htake, rkHash_snoc, show (W32 16777619 : w32) = primeRK from rfl]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · have Hnot : ¬ sint.Z i < sint.Z (W64 sep.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    rw [show sint.nat i = sep.length by word, List.take_length]
    wp_auto
    rw [show (W32 16777619 : w32) = primeRK from rfl]
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    ihave IH2 : iprop(∃ (j : w64) (sq pw : w32),
        "i" ∷ i_ptr ↦ j ∗
        "sq" ∷ sq_ptr ↦ sq ∗
        "pow" ∷ pow_ptr ↦ pw ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ pw * sq ^ sint.nat j = primeRK ^ sep.length⌝) $$ [i sq pow]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [show sint.nat (W64 sep.length) = sep.length by word]
      grind
    wp_for IH2
    wp_if_destruct
    · have Hhalf : sint.Z (BitVec.sshiftRight' j (W64 1)) = sint.Z j / 2 := sshiftRight_one j Hj.1
      have Hhalf' : sint.nat (BitVec.sshiftRight' j (W64 1)) = sint.nat j / 2 := by
        show (sint.Z _).toNat = (sint.Z j).toNat / 2
        rw [Hhalf]; omega
      wp_if_destruct
      · -- `j` even
        have Heven : sint.nat j % 2 = 0 := (and_one_eq_zero_iff j Hj.1).1 Hif
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, ?_⟩
        rw [Hhalf', pow_sq, ← Hj.2, show 2 * (sint.nat j / 2) = sint.nat j by omega]
      · -- `j` odd: `pow *= sq`
        have Hodd : sint.nat j % 2 = 1 := by
          have := mt (and_one_eq_zero_iff j Hj.1).2 Hif; omega
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, ?_⟩
        rw [Hhalf', pow_sq, ← Hj.2]
        conv => rhs; rw [show sint.nat j = 2 * (sint.nat j / 2) + 1 by omega, BitVec.pow_succ]
        grind
    · have hj0 : sint.nat j = 0 := by word
      have hpw : pw = primeRK ^ sep.length := by rw [← Hj.2, hj0]; grind
      rw [hpw]
      iapply HΦ; itrivial

/-- `bytealg.IndexRabinKarp(s, sep)`, at type `string`, for `len(sep) ≤ len(s)`: the index of the
first occurrence of `sep` in `s`, or `-1`. -/
theorem wp_IndexRabinKarp (s sep : GoString) (Hlen : sep.length ≤ s.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val #(functions IndexRabinKarp [go.string])) (Val #s)) (Val #sep))
    {{ RET #(indexResult s sep); True }} := by
  wp_start
  wp_auto
  wp_apply wp_HashStr
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsep
  -- the hash of the first `len(sep)` bytes
  ihave IH : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "h" ∷ h_ptr ↦ rkHash (s.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sep.length⌝) $$ [i h]
  · iexists (W64 0)
    rw [show rkHash (s.take (sint.nat (W64 0))) = W32 0 from rfl]
    iframe
    ipureintro
    exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hif' := Hif
    have hlt : sint.nat i < s.length := by word
    obtain ⟨c, hc⟩ : ∃ c, s[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, ↓reduceIte, hc]
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    have Htake : s.take (sint.nat (i + W64 1)) = s.take (sint.nat i) ++ [c] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hc]; rfl
    rw [Htake, rkHash_snoc, show (W32 16777619 : w32) = primeRK from rfl]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  have Hnot := Hif
  have Hin : sint.nat i = sep.length := by word
  rw [Hin]
  -- an occurrence at 0
  have Hocc0 := slice_eq_iff_occ s sep 0
  rw [List.drop_zero] at Hocc0
  have Hlen0 : sint.nat (W64 (sep.length : Int)) - 0 = sep.length := by word
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal ∧ ¬ sep <+: s⌝ ∨ ⌜v = returnVal #(W64 0) ∧ sep <+: s⌝) ∗
      sep_ptr ↦ sep ∗ s_ptr ↦ s ∗ n_ptr ↦ W64 sep.length ∗
      hashss_ptr ↦ rkHash sep ∗ h_ptr ↦ rkHash (s.take sep.length)))
    with [sep s n hashss h]
  · rw [ite_eq_left ⟨by decide, by word, by word⟩]
    wp_auto
    simp only [Hlen0, List.drop_zero]
    wp_if_destruct
    · iframe
      iright
      ipureintro
      exact ⟨trivial, Hocc0.1 Hif⟩
    · iframe
      ileft
      ipureintro
      exact ⟨trivial, fun h => Hif (Hocc0.2 h)⟩
  · iframe
    ileft
    ipureintro
    exact ⟨trivial, fun h => Hif (by rw [Hocc0.2 h])⟩
  iintro ⟨Hv, sep, s, n, hashss, h⟩
  icases Hv with (%Hv | %Hv)
  rotate_left
  · obtain ⟨rfl, Hocc⟩ := Hv
    wp_auto
    rw [indexResult_of_occ s sep (W64 0) (by decide) (by word)
      (by rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]; exact Hocc)
      (fun j hj => by simp at hj; omega)]
    iapply HΦ; itrivial
  obtain ⟨rfl, Hn0⟩ := Hv
  wp_auto
  -- the rolling hash of the window `s[i-n:i]`
  have Hsep0 : sep ≠ [] := by rintro rfl; exact Hn0 (List.nil_prefix)
  have HN : 0 < sep.length := List.length_pos_iff.2 Hsep0
  ihave IH2 : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "h" ∷ h_ptr ↦ rkHash ((s.drop (sint.nat i - sep.length)).take sep.length) ∗
      "%Hi" ∷ ⌜sep.length ≤ sint.Z i ∧ sint.Z i ≤ s.length ∧
        ∀ j, j ≤ sint.nat i - sep.length → ¬ sep <+: s.drop j⌝) $$ [i h]
  · iexists _
    rw [show sint.nat (W64 (sep.length : Int)) - sep.length = 0 by word, List.drop_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    exact Hn0
  wp_for IH2
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have hI : sint.nat i < s.length := by word
    have hIN : sep.length ≤ sint.nat i := by word
    obtain ⟨c0, c, w, Hw0, Hw1, Hc0, Hc, Hwlen⟩ :=
      window_step s (sint.nat i - sep.length) sep.length HN (by omega)
    rw [show sint.nat i - sep.length + sep.length = sint.nat i by omega] at Hc
    have Hia : sint.nat (i - W64 sep.length) = sint.nat i - sep.length := by word
    simp only [show 0 ≤ sint.Z i by word, ↓reduceIte, Hc]
    wp_auto
    simp only [show 0 ≤ sint.Z (i - W64 sep.length) by word, ↓reduceIte, Hia, Hc0]
    wp_auto
    have Hroll : rkHash ((s.drop (sint.nat i - sep.length)).take sep.length) * W32 16777619 +
          W32 (uint.Z c) - primeRK ^ sep.length * W32 (uint.Z c0) =
        rkHash ((s.drop (sint.nat i - sep.length + 1)).take sep.length) := by
      rw [Hw0, Hw1, show (W32 16777619 : w32) = primeRK from rfl, ← Hwlen]
      exact rkHash_roll c0 c w
    rw [Hroll]
    have Hi1 : sint.nat (i + W64 1) - sep.length = sint.nat i - sep.length + 1 := by word
    have Hi1' : sint.nat (i + W64 1 - W64 sep.length) = sint.nat i - sep.length + 1 := by word
    -- the invariant for `i + 1`, when the window at `i + 1 - n` is not `sep`
    have Hnext : ¬ (s.drop (sint.nat i - sep.length + 1)).take sep.length = sep →
        sep.length ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
        ∀ j, j ≤ sint.nat i - sep.length + 1 → ¬ sep <+: s.drop j := by
      intro Hne
      refine ⟨by word, by word, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (sint.nat i - sep.length + 1) with hj' | hj'
      · exact Hi.2.2 j (by omega)
      · obtain rfl : j = sint.nat i - sep.length + 1 := by omega
        rw [← slice_eq_iff_occ]; exact Hne
    wp_if_destruct
    · -- the hashes match: compare the bytes
      rw [ite_eq_left ⟨by word, by word, by word⟩]
      wp_auto
      rw [Hi1', show sint.nat (i + W64 1) - (sint.nat i - sep.length + 1) = sep.length by word]
      wp_if_destruct
      · -- an occurrence at `i + 1 - n`, the first
        wp_for_post
        rw [indexResult_of_occ s sep (i + W64 1 - W64 sep.length) (by word) (by word)
          (by rw [Hi1']; exact (slice_eq_iff_occ _ _ _).1 Hif)
          (fun j hj => Hi.2.2 j (by rw [Hi1'] at hj; omega))]
        iapply HΦ; itrivial
      · wp_for_post
        iframe
        iexists _
        rw [Hi1]
        iframe
        ipureintro
        exact Hnext Hif
    · wp_for_post
      iframe
      iexists _
      rw [Hi1]
      iframe
      ipureintro
      exact Hnext (fun h => Hif (by rw [h]))
  · have Hnot : ¬ sint.Z i < sint.Z (W64 s.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    rw [indexResult_of_none s sep ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i - sep.length + 1) with hj' | hj'
    · exact Hi.2.2 j (by omega)
    · exact not_occ_of_short s sep Hsep0 j (by word)

/-- `bytealg.Cutover(n)` returns some `int` (`(n + 16) / 8`); `Index` only uses it to decide
when to switch strategies, so its value does not matter. -/
theorem wp_Cutover (n : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val (@! Cutover)) (Val #n))
    {{ (r : w64), RET #r; True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

/-- `bytealg.CompareString(a, b)`: `compareResult a b`. -/
theorem wp_CompareString (a b : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! CompareString)) (Val #a)) (Val #b))
    {{ RET #(compareResult a b); True }} := by
  wp_start
  wp_auto
  wp_func_call
  wp_call
  unfold compareResult
  by_cases hlt : go.GoStringLt a b
  · simp only [hlt, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [hlt, decide_false, ↓reduceIte]
    wp_auto
    by_cases heq : a = b
    · simp only [heq, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [heq, decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

end wps

end internal.bytealg

end Perennial
end
