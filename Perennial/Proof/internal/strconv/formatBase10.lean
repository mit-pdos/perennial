/-
The proof of `internal.strconv.formatBase10`.
-/
module

public import Perennial.Spec.internal.strconv.formatBase10

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-! The state of `formatBase10`'s loops (`n` is the slice's length): the decimal digits `ds`
written at its end, from the index `k`, and what is left of the number `U`. -/

/-- Between chunks: `uc` left, `U = uc * 10 ^ len(ds) + digitsVal 10 ds`, no leading `0` in `ds`
while `uc ≠ 0`. -/
def internal.strconv.b10Inv (U uc : Nat) (ds : List Nat) (k : Int) (n : Nat) : Prop :=
  (∀ d ∈ ds, d < 10) ∧ U = uc * 10 ^ ds.length + internal.strconv.digitsVal 10 ds ∧
    (ds = [] ∨ 1 ≤ uc) ∧ k + ds.length = n

/-- In a 9-digit chunk `c = uc % 10^9` of `uc = q * 10^9 + c ≥ 2^29`, after `j` pairs of digits:
`lo = c / 100^j` is left of the chunk. -/
def internal.strconv.chunkInv (U q c lo j : Nat) (ds : List Nat) (k : Int) (n : Nat) : Prop :=
  (∀ d ∈ ds, d < 10) ∧ c < 10 ^ 9 ∧ lo = c / 100 ^ j ∧ j ≤ 4 ∧ 2 ^ 29 ≤ q * 10 ^ 9 + c ∧
    U = (q * 10 ^ (9 - 2 * j) + lo) * 10 ^ ds.length + internal.strconv.digitsVal 10 ds ∧
    k + ds.length = n ∧ ds.length ≤ 10 + 2 * j

theorem internal.strconv.step_arith (Q A r1 r0 P V : Nat) :
    (100 * Q + (100 * A + (10 * r1 + r0))) * P + V =
      (Q + A) * (P * 100) + (r1 * (P * 10) + (r0 * P + V)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]; omega

theorem internal.strconv.pow10_le_lt {m U : Nat} (h1 : 10 ^ m ≤ U) (h2 : U < 2 ^ 64) : m ≤ 19 := by
  refine Classical.byContradiction fun h => ?_
  have : 10 ^ 20 ≤ 10 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have : (2 : Nat) ^ 64 < 10 ^ 20 := by decide
  omega

theorem internal.strconv.b10Inv_len {U uc : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U uc ds k n) (hU : U < 2 ^ 64) : ds.length ≤ 19 := by
  obtain ⟨_, hUe, hne, _⟩ := h
  rcases hne with rfl | h1
  · simp
  · exact internal.strconv.pow10_le_lt (by
      have : 10 ^ ds.length ≤ uc * 10 ^ ds.length := Nat.le_mul_of_pos_left _ h1
      omega) hU

theorem internal.strconv.b10Inv_len29 {U uc : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U uc ds k n) (hU : U < 2 ^ 64) (hu : 2 ^ 29 ≤ uc) :
    ds.length ≤ 10 := by
  obtain ⟨_, hUe, _, _⟩ := h
  refine Classical.byContradiction fun hc => ?_
  have : 10 ^ 11 ≤ 10 ^ ds.length := Nat.pow_le_pow_right (by decide) (by omega)
  have : 2 ^ 29 * 10 ^ 11 ≤ uc * 10 ^ ds.length := Nat.mul_le_mul hu this
  have : (2 : Nat) ^ 64 < 2 ^ 29 * 10 ^ 11 := by decide
  omega

theorem internal.strconv.chunkInv_init {U uc : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U uc ds k n) (hU : U < 2 ^ 64) (hu : 2 ^ 29 ≤ uc) :
    internal.strconv.chunkInv U (uc / 10 ^ 9) (uc % 10 ^ 9) (uc % 10 ^ 9) 0 ds k n := by
  have hl := internal.strconv.b10Inv_len29 h hU hu
  obtain ⟨hlt, hU, _, hk⟩ := h
  refine ⟨hlt, Nat.mod_lt _ (by decide), by simp, by omega, ?_, ?_, hk, by omega⟩
  · have := Nat.div_add_mod uc (10 ^ 9); rw [Nat.mul_comm] at this; omega
  · rw [hU]; congr 1; congr 1
    have := Nat.div_add_mod uc (10 ^ 9); rw [Nat.mul_comm] at this; simp; omega

theorem internal.strconv.chunkInv_step {U q c lo j : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.chunkInv U q c lo j ds k n) (hj : j < 4) :
    internal.strconv.chunkInv U q c (lo / 100) (j + 1)
      ((lo % 100) / 10 :: (lo % 100) % 10 :: ds) (k - 2) n := by
  obtain ⟨hlt, hc, hlo, _, h29, hU, hk, hl⟩ := h
  refine ⟨?_, hc, ?_, by omega, h29, ?_, ?_, by simp only [List.length_cons]; omega⟩
  · intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · have := Nat.mod_lt lo (show 0 < 100 by decide); omega
    · exact Nat.mod_lt _ (by decide)
    · exact hlt d hd
  · rw [hlo, Nat.div_div_eq_div_mul, Nat.pow_succ]
  · rw [internal.strconv.digitsVal_cons, internal.strconv.digitsVal_cons, hU]
    simp only [List.length_cons]
    have e9 : 10 ^ (9 - 2 * j) = 100 * 10 ^ (9 - 2 * (j + 1)) := by
      rw [show 9 - 2 * j = 9 - 2 * (j + 1) + 2 by omega, Nat.pow_add, Nat.mul_comm]
    have e2 : 10 ^ (ds.length + 1 + 1) = 10 ^ ds.length * 100 := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    have e1 : 10 ^ (ds.length + 1) = 10 ^ ds.length * 10 := Nat.pow_succ _ _
    have hlo2 : lo = 100 * (lo / 100) + (10 * ((lo % 100) / 10) + (lo % 100) % 10) := by
      have := Nat.div_add_mod lo 100; have := Nat.div_add_mod (lo % 100) 10; omega
    rw [e9, e2, e1, Nat.mul_left_comm q 100]
    generalize lo / 100 = A at hlo2 ⊢
    generalize lo % 100 / 10 = r1 at hlo2 ⊢
    generalize lo % 100 % 10 = r0 at hlo2 ⊢
    rw [hlo2]
    exact internal.strconv.step_arith _ _ _ _ _ _
  · simp only [List.length_cons]; push_cast; omega

/-- After a chunk's four pairs: its first digit `lo`, not `0` if nothing is left (`q = 0`). -/
theorem internal.strconv.chunkInv_fin {U q c lo : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.chunkInv U q c lo 4 ds k n) :
    lo < 10 ∧ (q = 0 → 1 ≤ lo) ∧ (∀ d ∈ lo :: ds, d < 10) ∧
      U = q * 10 ^ (lo :: ds).length + internal.strconv.digitsVal 10 (lo :: ds) ∧
      ds.length ≤ 18 := by
  obtain ⟨hlt, hc, hlo, _, h29, hU, _, hl⟩ := h
  have h8 : (100 : Nat) ^ 4 = 10 ^ 8 := by decide
  rw [h8] at hlo
  have hlo10 : lo < 10 := by rw [hlo]; exact Nat.div_lt_of_lt_mul (by omega)
  refine ⟨hlo10, ?_, ?_, ?_, by omega⟩
  · intro hq; subst hq; rw [hlo]; exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  · intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hlo10
    · exact hlt d hd
  · rw [internal.strconv.digitsVal_cons, List.length_cons, Nat.pow_succ', hU]
    have e : 9 - 2 * 4 = 1 := rfl
    rw [e, Nat.pow_one, Nat.add_mul, Nat.mul_assoc]
    omega

theorem internal.strconv.b10Inv_len100 {U lo : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U lo ds k n) (hU : U < 2 ^ 64) (hlo : 100 ≤ lo) :
    ds.length ≤ 17 := by
  obtain ⟨_, hUe, _, _⟩ := h
  have : 10 ^ (ds.length + 2) ≤ U := by
    rw [Nat.pow_add, Nat.mul_comm]
    have : 10 ^ 2 * 10 ^ ds.length ≤ lo * 10 ^ ds.length := Nat.mul_le_mul_right _ hlo
    omega
  have := internal.strconv.pow10_le_lt this hU
  omega

theorem internal.strconv.b10Inv_len10 {U lo : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U lo ds k n) (hU : U < 2 ^ 64) (hlo : 10 ≤ lo) :
    ds.length ≤ 18 := by
  obtain ⟨_, hUe, _, _⟩ := h
  have : 10 ^ (ds.length + 1) ≤ U := by
    rw [Nat.pow_succ, Nat.mul_comm]
    have : 10 * 10 ^ ds.length ≤ lo * 10 ^ ds.length := Nat.mul_le_mul_right _ hlo
    omega
  have := internal.strconv.pow10_le_lt this hU
  omega

/-- A pair of digits off `lo ≥ 100`. -/
theorem internal.strconv.b10Inv_step {U lo : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv U lo ds k n) (hlo : 100 ≤ lo) :
    internal.strconv.b10Inv U (lo / 100) ((lo % 100) / 10 :: (lo % 100) % 10 :: ds) (k - 2) n := by
  obtain ⟨hlt, hU, _, hk⟩ := h
  refine ⟨?_, ?_, Or.inr ((Nat.le_div_iff_mul_le (by decide)).mpr (by omega)), ?_⟩
  · intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · have := Nat.mod_lt lo (show 0 < 100 by decide); omega
    · exact Nat.mod_lt _ (by decide)
    · exact hlt d hd
  · rw [internal.strconv.digitsVal_cons, internal.strconv.digitsVal_cons, hU]
    simp only [List.length_cons]
    have e2 : 10 ^ (ds.length + 1 + 1) = 10 ^ ds.length * 100 := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    have e1 : 10 ^ (ds.length + 1) = 10 ^ ds.length * 10 := Nat.pow_succ _ _
    have hlo2 : lo = 100 * (lo / 100) + (10 * ((lo % 100) / 10) + (lo % 100) % 10) := by
      have := Nat.div_add_mod lo 100; have := Nat.div_add_mod (lo % 100) 10; omega
    rw [e2, e1]
    generalize lo / 100 = A at hlo2 ⊢
    generalize lo % 100 / 10 = r1 at hlo2 ⊢
    generalize lo % 100 % 10 = r0 at hlo2 ⊢
    rw [hlo2]
    have := internal.strconv.step_arith 0 A r1 r0 (10 ^ ds.length) (internal.strconv.digitsVal 10 ds)
    simpa using this
  · simp only [List.length_cons]; push_cast; omega

/-- The digits of `U` once `lo < 100` is left: its one or two digits, then `ds`. -/
theorem internal.strconv.b10Inv_fin {Uw : w64} {lo : Nat} {ds : List Nat} {k : Int} {n : Nat}
    (h : internal.strconv.b10Inv Uw.toNat lo ds k n) (hlo : lo < 100) :
    internal.strconv.fmtUint Uw (W64 10) =
      (if 10 ≤ lo then [lo / 10, lo % 10] else [lo]).map internal.strconv.digitChar ++
        ds.map internal.strconv.digitChar := by
  obtain ⟨hlt, hU, hne, _⟩ := h
  have hb : 2 ≤ (W64 10).toNat := by decide
  have h10 : (W64 10).toNat = 10 := rfl
  split
  · rename_i h10le
    have := internal.strconv.fmtUint_eq_of Uw (W64 10) hb (lo / 10 :: lo % 10 :: ds)
      (by
        intro d hd; rw [h10]
        simp only [List.mem_cons] at hd
        rcases hd with rfl | rfl | hd
        · omega
        · exact Nat.mod_lt _ (by decide)
        · exact hlt d hd)
      (by simp) (Or.inr (by simp; omega))
      (by
        rw [h10, internal.strconv.digitsVal_cons, internal.strconv.digitsVal_cons, hU]
        simp only [List.length_cons]
        rw [Nat.pow_succ]
        have := Nat.div_add_mod lo 10
        generalize 10 ^ ds.length = P
        generalize lo / 10 = A at this ⊢
        generalize lo % 10 = r at this ⊢
        subst this
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]; omega)
    rw [this]; simp
  · rename_i h10le
    have := internal.strconv.fmtUint_eq_of Uw (W64 10) hb (lo :: ds)
      (by
        intro d hd; rw [h10]
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · omega
        · exact hlt d hd)
      (by simp)
      (hne.elim (fun h => by subst h; exact Or.inl rfl) (fun h1 => Or.inr (by simp; omega)))
      (by rw [h10, internal.strconv.digitsVal_cons, hU])
    rw [this]; simp

/-- After a chunk with nothing left: the digits of `U`. -/
theorem internal.strconv.chunk_done {Uw : w64} {lo : Nat} {ds : List Nat}
    (hlt : ∀ d ∈ lo :: ds, d < 10) (hlo : 1 ≤ lo)
    (hU : Uw.toNat = 0 * 10 ^ (lo :: ds).length + internal.strconv.digitsVal 10 (lo :: ds)) :
    internal.strconv.fmtUint Uw (W64 10) = (lo :: ds).map internal.strconv.digitChar := by
  apply internal.strconv.fmtUint_eq_of Uw (W64 10) (by decide) (lo :: ds) hlt (by simp)
    (Or.inr (by simp; omega))
  simpa using hU.symm

/-- Writing `c` just before the cut of `xs` (at `k`, `k < len(xs)`). -/
theorem internal.strconv.take_set (xs R : List w8) (k : Nat) (c : w8) (hk : k < xs.length) :
    (xs.take (k + 1) ++ R).set k c = xs.take k ++ c :: R := by
  have h1 : xs.take (k + 1) = xs.take k ++ [xs[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have h2 : (xs.take k).length = k := by simp; omega
  rw [h1, List.append_assoc, List.set_append_right _ _ (by omega), h2, Nat.sub_self]
  rfl

theorem internal.strconv.take_lookup (xs R : List w8) (k : Nat) (hk : k < xs.length) :
    (xs.take (k + 1) ++ R)[k]? = some xs[k] := by
  rw [List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_take, hk]

/-- Writing `c` at the last index before the cut `K` of `xs`. -/
theorem internal.strconv.take_set_pred (xs R : List w8) (K : Nat) (c : w8) (hK : 1 ≤ K)
    (hKl : K ≤ xs.length) : (xs.take K ++ R).set (K - 1) c = xs.take (K - 1) ++ c :: R := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact internal.strconv.take_set xs R K' c (by omega)

/-- Writing `c0 c1` at the last two indices before the cut `K` of `xs`. -/
theorem internal.strconv.two_set (xs D : List w8) (K : Nat) (c0 c1 : w8) (hK : 2 ≤ K)
    (hKl : K ≤ xs.length) :
    ((xs.take K ++ D).set (K - 2) c0).set (K - 1) c1 = xs.take (K - 2) ++ c0 :: c1 :: D := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show K' + 2 - 1 = K' + 1 by omega]
  rw [List.set_comm _ _ (by omega), internal.strconv.take_set xs D (K' + 1) c1 (by omega),
    internal.strconv.take_set xs (c1 :: D) K' c0 (by omega)]

theorem internal.strconv.formatBase10.wp_proof :
    internal.strconv.formatBase10.spec (GF := GF) (hG := hG) := by
  intro a xs u hxs
  wp_start as Ha
  ihave %Hlen := ownSlice_len $$ Ha
  wp_auto
  have hn : sint.Z a.len = xs.length := by
    have : (sint.nat a.len : Int) = sint.Z a.len := by word
    omega
  ihave IH : iprop(∃ (uc : w64) (ds : List Nat) (k : w64), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
      "Ha" ∷ a ↦* (xs.take (sint.nat k) ++ ds.map internal.strconv.digitChar) ∗
      "%Hinv" ∷ ⌜internal.strconv.b10Inv u.toNat uc.toNat ds (sint.Z k) xs.length⌝) $$ [u i Ha]
  · iexists u, [], a.len
    rw [show sint.nat a.len = xs.length by omega, List.take_length, List.map_nil, List.append_nil]
    iframe
    ipureintro
    simp [internal.strconv.b10Inv, internal.strconv.digitsVal, hn]
  wp_for IH
  have hUlt : u.toNat < 2 ^ 64 := u.isLt
  wp_if_destruct
  · -- what is left is below 2^29
    have hu29 : uc.toNat < 2 ^ 29 := by
      have h := congrArg BitVec.toNat Hif
      rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
      have h2 : ((W64 29).toNat) = 29 := rfl
      rw [h2] at h
      have : (W64 0).toNat = 0 := rfl
      rw [this] at h
      exact (Nat.div_eq_zero_iff_lt (by decide)).mp h
    have hlo0 : (W32 (uint.Z uc)).toNat = uc.toNat := by
      have : (W32 (uint.Z uc)).toNat = uc.toNat % 2 ^ 32 := by word
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    ihave IH3 : iprop(∃ (lo : w32) (ds : List Nat) (k : w64), "lo" ∷ lo_ptr ↦ lo ∗ "i" ∷ i_ptr ↦ k ∗
        "Ha" ∷ a ↦* (xs.take (sint.nat k) ++ ds.map internal.strconv.digitChar) ∗
        "%Hinv" ∷ ⌜internal.strconv.b10Inv u.toNat lo.toNat ds (sint.Z k) xs.length⌝) $$ [lo i Ha]
    · iexists (W32 (uint.Z uc)), ds, k
      iframe
      ipureintro
      rw [hlo0]; exact Hinv
    wp_for IH3
    wp_if_destruct
    · -- a pair of digits off `lo ≥ 100`
      have h100 : 100 ≤ lo.toNat := by word
      have hl := internal.strconv.b10Inv_len100 Hinv hUlt h100
      have hkd := Hinv.2.2.2
      have hk20 : sint.Z (k - W64 2 + W64 0) = sint.Z k - 2 := by word
      have hk21 : sint.Z (k - W64 2 + W64 1) = sint.Z k - 1 := by word
      rw [hk20, if_pos ⟨by omega, by omega⟩]
      wp_auto
      rw [hk21, if_pos ⟨by omega, by omega⟩]
      wp_auto
      have hm : lo.toNat % 100 < 100 := Nat.mod_lt _ (by decide)
      have hs := internal.strconv.smalls_getElem ⟨lo.toNat % 100, hm⟩
      simp only at hs
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo % W32 100 * W32 2 + W32 0))) =
        2 * (lo.toNat % 100) by word, hs.1]
      wp_auto
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo % W32 100 * W32 2 + W32 1))) =
        2 * (lo.toNat % 100) + 1 by word, hs.2]
      have hK : (sint.nat k : Int) = sint.Z k := by word
      have hKl : sint.nat k ≤ xs.length := by omega
      have hLlen : (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar).length =
          xs.length := by simp; omega
      obtain ⟨v0, hv0⟩ : ∃ v, (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar)[
          (sint.Z k - 2).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 2) v0 a _ _ (by omega) hv0 $$ Ha with ⟨H0, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H0
      obtain ⟨v1, hv1⟩ : ∃ v, ((List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar).set
          (sint.Z k - 2).toNat (internal.strconv.digitChar (lo.toNat % 100 / 10)))[
          (sint.Z k - 1).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 1) v1 a _ _ (by omega) hv1 $$ Ha with ⟨H1, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H1
      rw [show (sint.Z k - 2).toNat = sint.nat k - 2 by omega, show (sint.Z k - 1).toNat = sint.nat k - 1 by omega,
        internal.strconv.two_set _ _ _ _ _ (by omega) hKl,
        show sint.nat k - 2 = sint.nat (k - W64 2) by word]
      wp_for_post
      iframe
      iexists (lo / W32 100), (lo.toNat % 100 / 10 :: lo.toNat % 100 % 10 :: ds), (k - W64 2)
      rw [List.map_cons, List.map_cons]
      iframe
      ipureintro
      have := internal.strconv.b10Inv_step Hinv h100
      rw [BitVec.toNat_udiv, show sint.Z (k - W64 2) = sint.Z k - 2 by word]
      exact this
    · -- the last one or two digits
      have h100 : lo.toNat < 100 := by word
      have hfmt := internal.strconv.b10Inv_fin (Uw := u) Hinv h100
      have hkd := Hinv.2.2.2
      have hlen := internal.strconv.b10Inv_len Hinv hUlt
      have hs := internal.strconv.smalls_getElem ⟨lo.toNat, h100⟩
      simp only at hs
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo * W32 2 + W32 1))) = 2 * lo.toNat + 1 by word,
        hs.2]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hK : (sint.nat k : Int) = sint.Z k := by word
      have hKl : sint.nat k ≤ xs.length := by omega
      rw [hk1, if_pos ⟨by omega, by omega⟩]
      obtain ⟨v0, hv0⟩ : ∃ v, (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar)[
          (sint.Z k - 1).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 1) v0 a _ _ (by omega) hv0 $$ Ha with ⟨H0, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H0
      rw [show (sint.Z k - 1).toNat = sint.nat k - 1 by omega,
        internal.strconv.take_set_pred _ _ _ _ (by omega) hKl]
      wp_if_destruct
      · -- `lo ≥ 10`: its tens digit too
        have h10 : 10 ≤ lo.toNat := by word
        have hl10 := internal.strconv.b10Inv_len10 Hinv hUlt h10
        rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo * W32 2 + W32 0))) = 2 * lo.toNat by word,
          hs.1]
        wp_auto
        have hk2 : sint.Z (k - W64 1 - W64 1) = sint.Z k - 2 := by word
        rw [hk2, if_pos ⟨by omega, by omega⟩]
        obtain ⟨v1, hv1⟩ : ∃ v, (List.take (sint.nat k - 1) xs ++
            internal.strconv.digitChar (lo.toNat % 10) :: ds.map internal.strconv.digitChar)[
            (sint.Z k - 2).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
        icases ownSlice_elem_acc (V := w8) (sint.Z k - 2) v1 a _ _ (by omega) hv1 $$ Ha with ⟨H1, Ha⟩
        wp_auto
        ihave Ha := Ha $$ H1
        rw [show (sint.Z k - 2).toNat = sint.nat k - 1 - 1 by omega,
          internal.strconv.take_set_pred _ _ _ _ (by omega) (by omega)]
        iapply HΦ
        rw [hfmt, if_pos h10, show sint.nat (k - W64 1 - W64 1) = sint.nat k - 1 - 1 by word]
        iframe
        ipureintro
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_map]
        push_cast
        omega
      · -- `lo < 10`
        have h10 : lo.toNat < 10 := by word
        iapply HΦ
        rw [hfmt, if_neg (by omega), show sint.nat (k - W64 1) = sint.nat k - 1 by word,
          show lo.toNat % 10 = lo.toNat by omega]
        iframe
        ipureintro
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.length_cons,
          List.length_map]
        push_cast
        omega
  · -- a 9-digit chunk
    have h29 : 2 ^ 29 ≤ uc.toNat := by
      refine Classical.byContradiction fun h => Hif ?_
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      show uc.toNat / 2 ^ ((29 : Int) % 2 ^ 64).toNat = 0
      rw [Nat.div_eq_of_lt (by simp; omega)]
    have hc : (W32 (uint.Z (uc % W64 1000000000))).toNat = uc.toNat % 10 ^ 9 := by
      rw [show (W32 (uint.Z (uc % W64 1000000000))).toNat = (uc % W64 1000000000).toNat % 2 ^ 32 by word,
        BitVec.toNat_umod]
      have : uc.toNat % (W64 1000000000).toNat < 10 ^ 9 := Nat.mod_lt _ (by decide)
      exact Nat.mod_eq_of_lt (by omega)
    have hCI := internal.strconv.chunkInv_init Hinv hUlt h29
    ihave IH2 : iprop(∃ (j : w64) (lo : w32) (ds : List Nat) (k : w64),
        "ri" ∷ «$range_i_ptr» ↦ j ∗ "lo" ∷ lo_ptr ↦ lo ∗ "i" ∷ i_ptr ↦ k ∗
        "Ha" ∷ a ↦* (xs.take (sint.nat k) ++ ds.map internal.strconv.digitChar) ∗
        "%Hc" ∷ ⌜0 ≤ sint.Z j ∧ internal.strconv.chunkInv u.toNat (uc.toNat / 10 ^ 9)
          (uc.toNat % 10 ^ 9) lo.toNat (sint.nat j) ds (sint.Z k) xs.length⌝)
      $$ [«$range_i» lo i Ha]
    · iexists (zero_val w64), (W32 (uint.Z (uc % W64 1000000000))), ds, k
      iframe
      ipureintro
      rw [hc]
      exact ⟨by decide, hCI⟩
    wp_for IH2
    wp_if_destruct
    · -- a pair of digits
      obtain ⟨hj0, hCI⟩ := Hc
      have hj4 : sint.nat j < 4 := by word
      have hl := hCI.2.2.2.2.2.2.2
      have hkd := hCI.2.2.2.2.2.2.1
      have hk20 : sint.Z (k - W64 2 + W64 0) = sint.Z k - 2 := by word
      have hk21 : sint.Z (k - W64 2 + W64 1) = sint.Z k - 1 := by word
      rw [hk20, if_pos ⟨by omega, by omega⟩]
      wp_auto
      rw [hk21, if_pos ⟨by omega, by omega⟩]
      wp_auto
      have hm : lo.toNat % 100 < 100 := Nat.mod_lt _ (by decide)
      have hs := internal.strconv.smalls_getElem ⟨lo.toNat % 100, hm⟩
      simp only at hs
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo % W32 100 * W32 2 + W32 0))) =
        2 * (lo.toNat % 100) by word, hs.1]
      wp_auto
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo % W32 100 * W32 2 + W32 1))) =
        2 * (lo.toNat % 100) + 1 by word, hs.2]
      have hK : (sint.nat k : Int) = sint.Z k := by word
      have hKl : sint.nat k ≤ xs.length := by omega
      have hLlen : (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar).length =
          xs.length := by simp; omega
      obtain ⟨v0, hv0⟩ : ∃ v, (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar)[
          (sint.Z k - 2).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 2) v0 a _ _ (by omega) hv0 $$ Ha with ⟨H0, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H0
      obtain ⟨v1, hv1⟩ : ∃ v, ((List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar).set
          (sint.Z k - 2).toNat (internal.strconv.digitChar (lo.toNat % 100 / 10)))[
          (sint.Z k - 1).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 1) v1 a _ _ (by omega) hv1 $$ Ha with ⟨H1, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H1
      rw [show (sint.Z k - 2).toNat = sint.nat k - 2 by omega, show (sint.Z k - 1).toNat = sint.nat k - 1 by omega,
        internal.strconv.two_set _ _ _ _ _ (by omega) hKl,
        show sint.nat k - 2 = sint.nat (k - W64 2) by word]
      wp_for_post
      iframe
      iexists (j + W64 1), (lo / W32 100), (lo.toNat % 100 / 10 :: lo.toNat % 100 % 10 :: ds),
        (k - W64 2)
      rw [List.map_cons, List.map_cons]
      iframe
      ipureintro
      have := internal.strconv.chunkInv_step hCI (by omega)
      rw [BitVec.toNat_udiv, show sint.nat (j + W64 1) = sint.nat j + 1 by word,
        show sint.Z (k - W64 2) = sint.Z k - 2 by word]
      exact ⟨by word, this⟩
    · -- the chunk's first digit
      obtain ⟨hj0, hCI⟩ := Hc
      have hj4 : sint.nat j = 4 := by have := hCI.2.2.2.1; word
      rw [hj4] at hCI
      obtain ⟨hlo10, hq0, hlt', hU', hl⟩ := internal.strconv.chunkInv_fin hCI
      have hkd := hCI.2.2.2.2.2.2.1
      have hs := internal.strconv.smalls_getElem ⟨lo.toNat, by omega⟩
      simp only at hs
      rw [if_pos (by word), show sint.nat (W64 (uint.Z (lo * W32 2 + W32 1))) = 2 * lo.toNat + 1 by word,
        hs.2, show lo.toNat % 10 = lo.toNat by omega]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hK : (sint.nat k : Int) = sint.Z k := by word
      have hKl : sint.nat k ≤ xs.length := by omega
      rw [hk1, if_pos ⟨by omega, by omega⟩]
      obtain ⟨v0, hv0⟩ : ∃ v, (List.take (sint.nat k) xs ++ ds.map internal.strconv.digitChar)[
          (sint.Z k - 1).toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z k - 1) v0 a _ _ (by omega) hv0 $$ Ha with ⟨H0, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H0
      rw [show (sint.Z k - 1).toNat = sint.nat k - 1 by omega]
      rw [internal.strconv.take_set_pred _ _ _ _ (by omega) hKl,
        show sint.nat k - 1 = sint.nat (k - W64 1) by word]
      have hqn : (uc / W64 1000000000).toNat = uc.toNat / 10 ^ 9 := by rw [BitVec.toNat_udiv]; rfl
      wp_if_destruct
      · -- nothing is left: the number is written
        have hq : uc.toNat / 10 ^ 9 = 0 := by rw [← hqn, Hif]; rfl
        have hfmt := internal.strconv.chunk_done (Uw := u) hlt' (hq0 hq) (by rw [hU', hq])
        wp_for_post
        iapply HΦ
        rw [hfmt, List.map_cons]
        iframe
        ipureintro
        simp only [List.length_cons, List.length_map]
        have : sint.Z (k - W64 1) = sint.Z k - 1 := by word
        push_cast
        omega
      · -- the next chunk
        have hq : uc.toNat / 10 ^ 9 ≠ 0 := by
          intro h; apply Hif; apply BitVec.eq_of_toNat_eq; rw [hqn, h]; rfl
        wp_for_post
        iframe
        iexists (uc / W64 1000000000), (lo.toNat :: ds), (k - W64 1)
        rw [List.map_cons]
        iframe
        ipureintro
        refine ⟨hlt', ?_, Or.inr (by rw [hqn]; omega), ?_⟩
        · rw [hqn]; exact hU'
        · simp only [List.length_cons]
          have : sint.Z (k - W64 1) = sint.Z k - 1 := by word
          push_cast
          omega


end proof

end Perennial
