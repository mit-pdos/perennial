/-
The proof of `internal.strconv.formatBits`.
-/
module

public import Perennial.Spec.internal.strconv.formatBits
public import Perennial.Spec.internal.strconv.isPowerOfTwo
public import Perennial.Spec.math.bits.TrailingZeros

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

/-- The state of `formatBits`' digit loops: the digits `ds` written so far (below the base `b`),
the value `uc` left, with `U = uc * b ^ len(ds) + digitsVal b ds`, no leading `0` in `ds` while
`uc ≠ 0`, and the next free index `k`. -/
def internal.strconv.fbInv (U b uc : Nat) (ds : List Nat) (k : Int) : Prop :=
  (∀ d ∈ ds, d < b) ∧ U = uc * b ^ ds.length + internal.strconv.digitsVal b ds ∧
    (ds = [] ∨ 1 ≤ uc) ∧ k + ds.length = 65

theorem internal.strconv.fbInv_init (U b : Nat) : internal.strconv.fbInv U b U [] 65 := by
  simp [internal.strconv.fbInv, internal.strconv.digitsVal]

theorem internal.strconv.fbInv_step {U b uc : Nat} {ds : List Nat} {k : Int} (hb : 2 ≤ b)
    (hu : b ≤ uc) (h : internal.strconv.fbInv U b uc ds k) :
    internal.strconv.fbInv U b (uc / b) ((uc % b) :: ds) (k - 1) := by
  obtain ⟨hlt, hU, _, hk⟩ := h
  refine ⟨?_, ?_, Or.inr ?_, ?_⟩
  · intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by omega)
    · exact hlt d hd
  · rw [internal.strconv.digitsVal_cons, hU, List.length_cons, Nat.pow_succ']
    have := Nat.div_add_mod uc b
    have e : uc * b ^ ds.length = (b * (uc / b) + uc % b) * b ^ ds.length := by rw [this]
    rw [e, Nat.add_mul, Nat.mul_comm b (uc / b), Nat.mul_assoc]
    omega
  · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  · simp only [List.length_cons]; omega

theorem internal.strconv.fbInv_len {U b uc : Nat} {ds : List Nat} {k : Int} (hU : U < 2 ^ 64)
    (hb : 2 ≤ b) (h : internal.strconv.fbInv U b uc ds k) : ds.length ≤ 63 := by
  obtain ⟨_, hUe, hne, _⟩ := h
  rcases hne with rfl | h1
  · simp
  · have h2 : 2 ^ ds.length ≤ b ^ ds.length := Nat.pow_le_pow_left hb _
    have h3 : b ^ ds.length ≤ uc * b ^ ds.length := Nat.le_mul_of_pos_left _ h1
    have h4 : 2 ^ ds.length < 2 ^ 64 := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp h4
    omega

theorem internal.strconv.fbInv_fin {Uw base : w64} {uc : Nat} {ds : List Nat} {k : Int}
    (hb : 2 ≤ base.toNat) (hu : uc < base.toNat)
    (h : internal.strconv.fbInv Uw.toNat base.toNat uc ds k) :
    internal.strconv.fmtUint Uw base = (uc :: ds).map internal.strconv.digitChar := by
  obtain ⟨hlt, hU, hne, _⟩ := h
  apply internal.strconv.fmtUint_eq_of Uw base hb (uc :: ds)
  · intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hu
    · exact hlt d hd
  · simp
  · rcases hne with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr (by simp; omega)
  · rw [internal.strconv.digitsVal_cons, hU]

/-- A base between 2 and 36 with `b & (b - 1) = 0` is a power of two (checked for each). -/
theorem internal.strconv.pow2_of_and (b : w64) (h1 : 2 ≤ b.toNat) (h2 : b.toNat ≤ 36)
    (h : b &&& b - W64 1 = W64 0) : ∃ k, k < 6 ∧ b = W64 (2 ^ k) := by
  have key : ∀ n : Fin 37, 2 ≤ n.val → W64 n.val &&& W64 n.val - W64 1 = W64 0 →
      ∃ k : Fin 6, n.val = 2 ^ k.val := by decide +kernel
  have hb : b = W64 b.toNat := by apply BitVec.eq_of_toNat_eq; simp [W64]
  rw [hb] at h
  obtain ⟨k, hk⟩ := key ⟨b.toNat, by omega⟩ h1 h
  exact ⟨k.val, k.isLt, by rw [hb]; simp only at hk; rw [hk]; push_cast; rfl⟩

/-- Writing `c` just before a block: the block of `n + 1` padding bytes loses its last. -/
theorem internal.strconv.set_replicate_append (n : Nat) (z c : w8) (X : List w8) :
    (List.replicate (n + 1) z ++ X).set n c = List.replicate n z ++ c :: X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, List.set_cons_succ, ih, List.replicate_succ,
      List.cons_append]

theorem internal.strconv.formatBits.wp_proof
    (wp_isPowerOfTwo : internal.strconv.isPowerOfTwo.spec (GF := GF) (hG := hG))
    (wp_TrailingZeros : math.bits.TrailingZeros.spec (GF := GF) (hG := hG)) :
    internal.strconv.formatBits.spec (GF := GF) (hG := hG) := by
  intro u base neg hb1 hb2 hb10
  wp_start
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z base < sint.Z (W64 2) by word)]
  wp_auto
  rw [decide_eq_false hb10]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z (W64 36) < sint.Z base by word)]
  wp_auto
  -- `if neg { u = -u }`
  wp_join iprop(∃ U : w64, "u" ∷ u_ptr ↦ U ∗ "%HU" ∷ ⌜U = if neg then -u else u⌝) with [u]
    as ⟨%U, u, %HU⟩
  · iexists _; iframe; ipureintro; simp
  · iexists _; iframe; ipureintro; simp
  wp_apply wp_isPowerOfTwo
  have hbn : 2 ≤ base.toNat := by word
  have hbn36 : base.toNat ≤ 36 := by word
  wp_join iprop(∃ (k uc : w64), "a" ∷ a_ptr ↦ array.mk 65 (List.replicate (sint.nat k) (zero_val w8) ++
      internal.strconv.fmtUint U base) ∗ "i" ∷ i_ptr ↦ k ∗ "u" ∷ u_ptr ↦ uc ∗ "base" ∷ base_ptr ↦ base ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k + (internal.strconv.fmtUint U base).length = 65⌝)
    with [a i u base] as ⟨%k, %uc, a, i, u, base, %Hk⟩
  · -- a power of two
    obtain ⟨sh, hsh, hbsh⟩ := internal.strconv.pow2_of_and base hbn hbn36 Hif
    wp_apply wp_TrailingZeros base as %r %Hr
    obtain rfl := Hr.2 sh (by omega) hbsh
    ihave IH : iprop(∃ (uc : w64) (ds : List Nat) (k : w64), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
        "a" ∷ a_ptr ↦ array.mk 65 (List.replicate (sint.nat k) (zero_val w8) ++
          ds.map internal.strconv.digitChar) ∗ "b" ∷ b_ptr ↦ base ∗ "m" ∷ m_ptr ↦ (base - W64 1) ∗
        "shift" ∷ shift_ptr ↦ W64 (sh : Int) ∗
        "%Hinv" ∷ ⌜internal.strconv.fbInv U.toNat base.toNat uc.toNat ds (sint.Z k)⌝) $$ [u i a b m shift]
    · iexists U, [], W64 65
      iframe
      ipureintro
      exact internal.strconv.fbInv_init _ _
    wp_for IH
    have hlen := internal.strconv.fbInv_len U.isLt hbn Hinv
    have hkd := Hinv.2.2.2
    wp_if_destruct
    · -- `u >= b`: one more digit
      have hge : base.toNat ≤ uc.toNat := by word
      have hbt : base.toNat = 2 ^ sh := by
        rw [hbsh]; show (2 ^ sh : Int).toNat % 2 ^ 64 = 2 ^ sh
        have : 2 ^ sh < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
        push_cast; exact Nat.mod_eq_of_lt this
      have hd : uc.toNat % base.toNat < base.toNat := Nat.mod_lt _ (by omega)
      have hidx : uc &&& base - W64 1 = W64 (uc.toNat % base.toNat) := by
        have e1 : (base - W64 1).toNat = 2 ^ sh - 1 := by
          rw [BitVec.toNat_sub, hbt]
          have h1 : (W64 1).toNat = 1 := rfl
          have : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
          have : 2 ^ sh < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
          rw [h1, show 2 ^ 64 - 1 + 2 ^ sh = 2 ^ 64 + (2 ^ sh - 1) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]
        have e2 : (W64 (uc.toNat % base.toNat)).toNat = uc.toNat % base.toNat := by word
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_and, e1, Nat.and_two_pow_sub_one_eq_mod, e2, hbt]
      rw [hidx, if_pos (by word),
        show sint.nat (W64 (uc.toNat % base.toNat)) = uc.toNat % base.toNat by word]
      have hdc := internal.strconv.digits_getElem ⟨uc.toNat % base.toNat, by omega⟩
      simp only at hdc
      rw [hdc]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat k = (sint.Z (k - W64 1)).toNat + 1 := by word
      rw [if_pos ⟨by omega, by omega⟩]
      icases array_acc (V := w8) a_ptr (sint.Z (k - W64 1)) _ _ _ (zero_val w8) (by omega)
        (by rw [List.getElem?_append_left (by rw [List.length_replicate, hkn]; omega),
          List.getElem?_replicate, if_pos (by omega)])
        $$ a with ⟨Ha, a⟩
      wp_auto
      ihave a := a $$ Ha
      have hL : (List.replicate (sint.nat k) (zero_val w8) ++ ds.map internal.strconv.digitChar).set
          (sint.Z (k - W64 1)).toNat (internal.strconv.digitChar (uc.toNat % base.toNat)) =
          List.replicate (sint.nat (k - W64 1)) (zero_val w8) ++
            (uc.toNat % base.toNat :: ds).map internal.strconv.digitChar := by
        rw [hkn, internal.strconv.set_replicate_append, List.map_cons,
          show sint.nat (k - W64 1) = (sint.Z (k - W64 1)).toNat by word]
      rw [hL]
      have hsh' : (W64 (sh : Int)).toNat = sh := by word
      have hshr : (uc >>> W64 (sh : Int)).toNat = uc.toNat / base.toNat := by
        rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, hsh', Nat.shiftRight_eq_div_pow, hbt]
      wp_for_post
      iframe
      iexists (uc >>> W64 (sh : Int)), (uc.toNat % base.toNat :: ds), (k - W64 1)
      iframe
      ipureintro
      have := internal.strconv.fbInv_step hbn hge Hinv
      rw [hshr, hk1]
      exact this
    · -- the last digit
      have hlt : uc.toNat < base.toNat := by word
      rw [if_pos (by word), show sint.nat uc = uc.toNat by word]
      have hdc := internal.strconv.digits_getElem ⟨uc.toNat, by omega⟩
      simp only at hdc
      rw [hdc]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat k = (sint.Z (k - W64 1)).toNat + 1 := by word
      rw [if_pos ⟨by omega, by omega⟩]
      icases array_acc (V := w8) a_ptr (sint.Z (k - W64 1)) _ _ _ (zero_val w8) (by omega)
        (by rw [List.getElem?_append_left (by rw [List.length_replicate, hkn]; omega),
          List.getElem?_replicate, if_pos (by omega)])
        $$ a with ⟨Ha, a⟩
      wp_auto
      ihave a := a $$ Ha
      have hfin := internal.strconv.fbInv_fin hbn hlt Hinv
      have hL : (List.replicate (sint.nat k) (zero_val w8) ++ ds.map internal.strconv.digitChar).set
          (sint.Z (k - W64 1)).toNat (internal.strconv.digitChar uc.toNat) =
          List.replicate (sint.nat (k - W64 1)) (zero_val w8) ++ internal.strconv.fmtUint U base := by
        rw [hkn, internal.strconv.set_replicate_append, hfin, List.map_cons,
          show sint.nat (k - W64 1) = (sint.Z (k - W64 1)).toNat by word]
      rw [hL]
      wp_join_done
      iexists (k - W64 1), uc
      iframe
      ipureintro
      rw [hfin]
      simp only [List.length_cons, List.length_map]
      omega

  · -- the general case
    ihave IH : iprop(∃ (uc : w64) (ds : List Nat) (k : w64), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
        "a" ∷ a_ptr ↦ array.mk 65 (List.replicate (sint.nat k) (zero_val w8) ++
          ds.map internal.strconv.digitChar) ∗ "b" ∷ b_ptr ↦ base ∗
        "%Hinv" ∷ ⌜internal.strconv.fbInv U.toNat base.toNat uc.toNat ds (sint.Z k)⌝) $$ [u i a b]
    · iexists U, [], W64 65
      iframe
      ipureintro
      exact internal.strconv.fbInv_init _ _
    wp_for IH
    have hlen := internal.strconv.fbInv_len U.isLt hbn Hinv
    have hkd := Hinv.2.2.2
    wp_if_destruct
    · -- `u >= b`: one more digit
      have hge : base.toNat ≤ uc.toNat := by word
      rw [if_neg (show ¬ uint.Z base = 0 by word)]
      wp_auto
      have hd : uc.toNat % base.toNat < base.toNat := Nat.mod_lt _ (by omega)
      have hidx : uc - uc / base * base = W64 (uc.toNat % base.toNat) := by
        apply BitVec.eq_of_toNat_eq
        have h1 : (uc / base * base).toNat = uc.toNat / base.toNat * base.toNat := by
          rw [BitVec.toNat_mul, BitVec.toNat_udiv]
          apply Nat.mod_eq_of_lt
          have := Nat.div_mul_le_self uc.toNat base.toNat
          have := uc.isLt
          omega
        rw [BitVec.toNat_sub, h1]
        show _ = (uc.toNat % base.toNat) % 2 ^ 64
        have := Nat.div_mul_le_self uc.toNat base.toNat
        have := uc.isLt
        have e : uc.toNat % base.toNat = uc.toNat - uc.toNat / base.toNat * base.toNat := by
          have h1 := Nat.div_add_mod uc.toNat base.toNat
          have h2 := Nat.mul_comm base.toNat (uc.toNat / base.toNat)
          omega
        rw [e, show 2 ^ 64 - uc.toNat / base.toNat * base.toNat + uc.toNat =
          2 ^ 64 + (uc.toNat - uc.toNat / base.toNat * base.toNat) by omega, Nat.add_mod_left]
      rw [hidx, if_pos (by word),
        show sint.nat (W64 (uc.toNat % base.toNat)) = uc.toNat % base.toNat by word]
      have hdc := internal.strconv.digits_getElem ⟨uc.toNat % base.toNat, by omega⟩
      simp only at hdc
      rw [hdc]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat k = (sint.Z (k - W64 1)).toNat + 1 := by word
      rw [if_pos ⟨by omega, by omega⟩]
      icases array_acc (V := w8) a_ptr (sint.Z (k - W64 1)) _ _ _ (zero_val w8) (by omega)
        (by rw [List.getElem?_append_left (by rw [List.length_replicate, hkn]; omega),
          List.getElem?_replicate, if_pos (by omega)])
        $$ a with ⟨Ha, a⟩
      wp_auto
      ihave a := a $$ Ha
      have hL : (List.replicate (sint.nat k) (zero_val w8) ++ ds.map internal.strconv.digitChar).set
          (sint.Z (k - W64 1)).toNat (internal.strconv.digitChar (uc.toNat % base.toNat)) =
          List.replicate (sint.nat (k - W64 1)) (zero_val w8) ++
            (uc.toNat % base.toNat :: ds).map internal.strconv.digitChar := by
        rw [hkn, internal.strconv.set_replicate_append, List.map_cons,
          show sint.nat (k - W64 1) = (sint.Z (k - W64 1)).toNat by word]
      rw [hL]
      wp_for_post
      iframe
      iexists (uc / base), (uc.toNat % base.toNat :: ds), (k - W64 1)
      iframe
      ipureintro
      have := internal.strconv.fbInv_step hbn hge Hinv
      rw [BitVec.toNat_udiv, hk1]
      exact this
    · -- the last digit
      have hlt : uc.toNat < base.toNat := by word
      rw [if_pos (by word), show sint.nat uc = uc.toNat by word]
      have hdc := internal.strconv.digits_getElem ⟨uc.toNat, by omega⟩
      simp only at hdc
      rw [hdc]
      wp_auto
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat k = (sint.Z (k - W64 1)).toNat + 1 := by word
      rw [if_pos ⟨by omega, by omega⟩]
      icases array_acc (V := w8) a_ptr (sint.Z (k - W64 1)) _ _ _ (zero_val w8) (by omega)
        (by rw [List.getElem?_append_left (by rw [List.length_replicate, hkn]; omega),
          List.getElem?_replicate, if_pos (by omega)])
        $$ a with ⟨Ha, a⟩
      wp_auto
      ihave a := a $$ Ha
      have hfin := internal.strconv.fbInv_fin hbn hlt Hinv
      have hL : (List.replicate (sint.nat k) (zero_val w8) ++ ds.map internal.strconv.digitChar).set
          (sint.Z (k - W64 1)).toNat (internal.strconv.digitChar uc.toNat) =
          List.replicate (sint.nat (k - W64 1)) (zero_val w8) ++ internal.strconv.fmtUint U base := by
        rw [hkn, internal.strconv.set_replicate_append, hfin, List.map_cons,
          show sint.nat (k - W64 1) = (sint.Z (k - W64 1)).toNat by word]
      rw [hL]
      wp_join_done
      iexists (k - W64 1), uc
      iframe
      ipureintro
      rw [hfin]
      simp only [List.length_cons, List.length_map]
      omega
  -- the sign
  wp_join iprop(∃ (k' : w64) (str : GoString), "a" ∷ a_ptr ↦ array.mk 65
      (List.replicate (sint.nat k') (zero_val w8) ++ str) ∗ "i" ∷ i_ptr ↦ k' ∗
      "%Hk'" ∷ ⌜0 ≤ sint.Z k' ∧ sint.Z k' + str.length = 65 ∧
        str = if neg then W8 45 :: internal.strconv.fmtUint U base else internal.strconv.fmtUint U base⌝)
    with [a i] as ⟨%k', %str, a, i, %Hk'⟩
  · iexists k, internal.strconv.fmtUint U base
    iframe
    ipureintro
    exact ⟨by omega, by omega, by simp⟩
  · have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
    have hkn : sint.nat k = (sint.Z (k - W64 1)).toNat + 1 := by word
    rw [if_pos ⟨by omega, by omega⟩]
    icases array_acc (V := w8) a_ptr (sint.Z (k - W64 1)) _ _ _ (zero_val w8) (by omega)
      (by rw [List.getElem?_append_left (by rw [List.length_replicate, hkn]; omega),
        List.getElem?_replicate, if_pos (by omega)])
      $$ a with ⟨Ha, a⟩
    wp_auto
    ihave a := a $$ Ha
    rw [hkn, internal.strconv.set_replicate_append]
    wp_join_done
    iexists (k - W64 1), (W8 45 :: internal.strconv.fmtUint U base)
    rw [show sint.nat (k - W64 1) = (sint.Z (k - W64 1)).toNat by word]
    iframe
    ipureintro
    refine ⟨by omega, ?_, by simp⟩
    rw [List.length_cons]
    push_cast
    omega
  have hkz : (sint.nat k' : Int) = sint.Z k' := by word
  have hlen65 : (List.replicate (sint.nat k') (zero_val w8) ++ str).length = 65 := by
    rw [List.length_append, List.length_replicate]; omega
  rw [if_pos (show 0 ≤ sint.Z k' ∧ sint.Z k' ≤ sint.Z (W64 65) ∧ sint.Z (W64 65) ≤ 65 from
    ⟨Hk'.1, by word, by word⟩)]
  ihave Hsl := slice_array (GF := GF) a_ptr _ _ (by show (List.replicate _ _ ++ str).length < 2 ^ 63; omega)
    $$ a
  ihave Hsl := (ownSlice_trivial_slice (V := w8) _ _ _).1 $$ Hsl
  ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split (V := w8) k' _ _ _ (W64 0) _ ⟨by word, by word, by word⟩).1 $$ Hsl
  rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero,
    List.drop_left' (List.length_replicate (n := sint.nat k') (a := zero_val w8)),
    show slice.mk (arrayIndexRef w8 (sint.Z k') a_ptr) (W64 65 - k') (W64 65 - k') =
      slice.slice (slice.mk a_ptr (W64 65) (W64 65)) w8 k' (slice.mk a_ptr (W64 65) (W64 65)).len
      from rfl]
  wp_apply wp_bytes_to_string _ _ _ $$ Hsuf as Hsuf
  have hstr : str = if neg then W8 45 :: internal.strconv.fmtUint (-u) base
      else internal.strconv.fmtUint u base := by
    rw [Hk'.2.2, HU]; cases neg <;> rfl
  rw [hstr]
  iapply HΦ
  itrivial

end proof

end Perennial
