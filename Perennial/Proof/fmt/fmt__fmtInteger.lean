/-
The proof of `fmt.(*fmt).fmtInteger`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtInteger
public import Perennial.Spec.fmt.fmt__pad

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure

/-- The digits of `n` in base `b` (16: `hexNat`, otherwise `decimalNat`). -/
def fmt.digitsOf (b n : Nat) : GoString := if b = 16 then fmt.hexNat n else fmt.decimalNat n

/-- Writing `c` just before the suffix `D` of a buffer. -/
theorem fmt.take_append_set {α : Type} (xs D : List α) (k : Nat) (c : α) (hk : 1 ≤ k)
    (hk' : k ≤ xs.length) :
    (xs.take k ++ D).set (k - 1) c = xs.take (k - 1) ++ c :: D := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.set_append_left _ _ (by simp; omega), Nat.add_sub_cancel, List.take_add_one,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some]
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left (show k ≤ xs.length by omega), Nat.sub_self]
  simp

theorem fmt.digit10_eq (uc : w64) :
    W8 (uint.Z (W64 48 + uc - uc / W64 10 * W64 10)) = fmt.digitByte (uc.toNat % 10) := by
  unfold fmt.digitByte
  word

theorem fmt.hexDigits_get (d : Nat) (h : d < 16) :
    (fmt.hexDigits false)[d]? = some (fmt.hexDigitByte d) := by
  have key : ∀ d : Fin 16, (fmt.hexDigits false)[d.val]? = some (fmt.hexDigitByte d.val) := by
    decide +kernel
  exact key ⟨d, h⟩

theorem fmt.digitByte_eq_hex {d : Nat} (h : d < 10) : fmt.digitByte d = fmt.hexDigitByte d := by
  unfold fmt.digitByte fmt.hexDigitByte; simp [h]

theorem fmt.length_decimalNat_w64 (U : w64) : (fmt.decimalNat U.toNat).length ≤ 20 :=
  fmt.length_decimalNat_le _ 20 (by omega) (by have := U.isLt; omega)

theorem fmt.length_hexNat_w64 (U : w64) : (fmt.hexNat U.toNat).length ≤ 16 :=
  fmt.length_hexNat_le _ 16 (by omega) (by have := U.isLt; omega)

theorem fmt.precZ (wP neg : Bool) (wid : w64)
    (h : wP = true → 0 ≤ sint.Z wid ∧ sint.Z wid ≤ 1000000) :
    sint.Z (if wP then (if neg then wid - W64 1 else wid) else W64 0) =
      (if wP then sint.Z wid - (if neg then 1 else 0) else 0) := by
  cases wP
  · rfl
  · obtain ⟨hw0, hw1⟩ := h rfl
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> word

theorem fmt.precN (wP neg : Bool) (wid Pw : w64) (n : Nat)
    (hz : sint.Z Pw = (if wP then sint.Z wid - (if neg then 1 else 0) else 0))
    (h : wP = true → 0 ≤ sint.Z wid ∧ 3 + sint.Z wid ≤ n) (hn : 3 ≤ n) :
    (sint.Z Pw).toNat + 3 ≤ n := by
  cases wP
  · simp at hz; omega
  · obtain ⟨hw0, hw1⟩ := h rfl
    cases neg <;> simp at hz <;> omega

theorem fmt.hexDigitByte_ascii {d : Nat} (h : d < 16) : uint.Z (fmt.hexDigitByte d) < 128 := by
  unfold fmt.hexDigitByte; split <;> word

theorem fmt.hexNat_ascii (n : Nat) : ∀ c ∈ fmt.hexNat n, uint.Z c < 128 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    rw [fmt.hexNat_eq] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · split at hc
      · simp at hc
      · exact ih (n / 16) (by omega) c hc
    · exact fmt.hexDigitByte_ascii (Nat.mod_lt _ (by omega))

theorem fmt.digitsOf_ascii (b n : Nat) : ∀ c ∈ fmt.digitsOf b n, uint.Z c < 128 := by
  unfold fmt.digitsOf
  split
  · exact fmt.hexNat_ascii n
  · intro c hc; have := (fmt.decimalNat_digits n c hc).2; omega

theorem fmt.padZeros_ascii {n : Nat} {s : GoString} (h : ∀ c ∈ s, uint.Z c < 128) :
    ∀ c ∈ fmt.padZeros n s, uint.Z c < 128 := by
  intro c hc
  unfold fmt.padZeros at hc
  simp only [List.mem_append, List.mem_replicate] at hc
  rcases hc with ⟨-, rfl⟩ | hc
  · decide
  · exact h c hc

/-- The magnitude formatted: `|z|` for `z` the operand as a signed or unsigned integer. -/
theorem fmt.natAbs_eq (u : w64) (isSigned neg : Bool)
    (hneg : (isSigned && decide (sint.Z u < 0)) = neg) :
    ((if isSigned then sint.Z u else uint.Z u) < 0 ↔ neg = true) ∧
    (if isSigned then sint.Z u else uint.Z u).natAbs = (if neg then -u else u).toNat := by
  subst hneg
  cases isSigned
  · refine ⟨?_, ?_⟩
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, iff_false]; word
    · simp [uint.Z]
  · refine ⟨by simp, ?_⟩
    simp only [Bool.true_and, ↓reduceIte, decide_eq_true_eq]
    by_cases h : sint.Z u < 0
    · rw [if_pos h]
      have : (((-u).toNat : Nat) : Int) = - sint.Z u := by word
      omega
    · rw [if_neg h]
      have : ((u.toNat : Nat) : Int) = sint.Z u := by word
      omega

/-- The bytes `fmtInteger` formats (the sign, the zero padding to the precision `Pw`, the digits
of the magnitude) are `intOut`. -/
theorem fmt.intOut_eq (base : w64) (u : w64) (isSigned neg : Bool)
    (hneg : (isSigned && decide (sint.Z u < 0)) = neg) (wP : Bool) (wid Pw : w64)
    (hw : wP = true → 0 ≤ sint.Z wid)
    (hPz : sint.Z Pw = if wP then sint.Z wid - (if neg then 1 else 0) else 0) :
    (if neg then W8 45 :: fmt.padZeros (sint.Z Pw).toNat
        (fmt.digitsOf (uint.nat base) (if neg then -u else u).toNat)
      else fmt.padZeros (sint.Z Pw).toNat
        (fmt.digitsOf (uint.nat base) (if neg then -u else u).toNat)) =
    fmt.intOut (uint.nat base) (if wP then sint.nat wid else 0)
      (if isSigned then sint.Z u else uint.Z u) := by
  obtain ⟨hz, habs⟩ := fmt.natAbs_eq u isSigned neg hneg
  generalize (if isSigned then sint.Z u else uint.Z u) = z at hz habs
  generalize (if neg then -u else u).toNat = n at habs
  subst habs
  have hP : (sint.Z Pw).toNat =
      (if neg then (if wP then sint.nat wid else 0) - 1 else (if wP then sint.nat wid else 0)) := by
    cases wP
    · cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hPz ⊢ <;> omega
    · have h0 := hw rfl
      have hn : (sint.nat wid : Int) = sint.Z wid := by word
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hPz ⊢ <;> omega
  rw [hP]
  unfold fmt.intOut fmt.hexPad fmt.decimalPad fmt.digitsOf
  cases neg
  · have : ¬ z < 0 := fun h => by simp_all
    by_cases hb : uint.nat base = 16 <;> simp [hb, this]
  · have : z < 0 := hz.2 rfl
    by_cases hb : uint.nat base = 16 <;> simp [hb, this]

/-- `pad`'s precondition for the bytes `fmtInteger` formats. -/
theorem fmt.pad_ok (neg wP : Bool) (wid Pw : w64) (S : GoString)
    (hS : ∀ c ∈ S, uint.Z c < 128) (hw : wP = true → 0 ≤ sint.Z wid)
    (hPz : sint.Z Pw = if wP then sint.Z wid - (if neg then 1 else 0) else 0) :
    wP = false ∨ wid = W64 0 ∨
      ((∀ c ∈ (if neg then W8 45 :: fmt.padZeros (sint.Z Pw).toNat S
          else fmt.padZeros (sint.Z Pw).toNat S), uint.Z c < 128) ∧ 0 ≤ sint.Z wid ∧
        sint.Z wid ≤ (if neg then W8 45 :: fmt.padZeros (sint.Z Pw).toNat S
          else fmt.padZeros (sint.Z Pw).toNat S).length) := by
  cases wP
  · exact Or.inl rfl
  · refine Or.inr (Or.inr ⟨?_, hw rfl, ?_⟩)
    · cases neg
      · exact fmt.padZeros_ascii hS
      · intro c hc
        simp only [↓reduceIte, List.mem_cons] at hc
        rcases hc with rfl | hc
        · decide
        · exact fmt.padZeros_ascii hS c hc
    · have := hw rfl
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hPz ⊢ <;>
        simp only [List.length_cons, fmt.length_padZeros] <;> omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

omit package_sem in
/-- A slice of length and capacity 68 at `l` is the array `[68]byte` at `l`. -/
theorem fmt.slice68_to_array (l : Loc) (vs : List w8) :
    (slice.mk l (W64 68) (W64 68) ↦* vs : IProp GF) ⊢
      ∃ ib : GoArray w8 68, typedPointsto l ib (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, _⟩)
  · exfalso; rw [slice_mk_eq_nil] at H; exact absurd H.1.2.1 (by decide)
  · iexists (array.mk 68 vs : GoArray w8 68)
    icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ H with H
    simp only [TypedPointsto.typedPointstoDef] at Hnn ⊢
    icases H with ⟨%Hlen, H⟩
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe H
    ipureintro
    exact Hlen

theorem fmt.fmt.fmtInteger.wp_proof (wp_pad : fmt.fmt.pad.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtInteger.spec (GF := GF) (hG := hG) :=
  fun f b F wid prec bs u base isSigned verb hbase hverb hsharp hplus hspace hminus hprecP hwid => by
  obtain ⟨wP, pP, mi, pl, sh, sp, ze, pV, sV⟩ := F
  simp only at hsharp hplus hspace hminus hprecP hwid ⊢
  subst hsharp hplus hspace hminus hprecP
  unfold fmt.fmtOwn fmt.intbufOwn
  wp_start as ⟨⟨Hbuf, Hflags, Hwid, Hprec⟩, ⟨%ib, Hib⟩, Hb⟩
  wp_auto
  wp_join (v := #(isSigned && decide (sint.Z u < 0))) with [u]
  · iframe; ipureintro; rfl
  generalize hneg : (isSigned && decide (sint.Z u < 0)) = neg
  wp_join iprop(∃ U : w64, "u" ∷ u_ptr ↦ U ∗ "%HU" ∷ ⌜U = if neg then -u else u⌝) with [u]
    as ⟨%U, u, %HU⟩
  · iexists _; iframe; ipureintro; simp
  · iexists _; iframe; ipureintro; simp
  obtain ⟨ibs⟩ := ib
  ihave %Hibl := array_len _ _ _ _ $$ Hib
  ihave Hsl := slice_array (GF := GF) _ _ _ (by simp only; omega) $$ Hib
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 68 - W64 0 = W64 68 from rfl]
  wp_join (v := #wP) at (if: _ then #true else _) with [Hflags f]
  · wp_if_destruct <;> wp_join_done
  wp_join iprop(∃ (sl : GoSlice) (xs : List w8), "buf" ∷ buf_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
      "Hback" ∷ (∀ xs' : List w8, sl ↦* xs' -∗
        ∃ ib : GoArray w8 68, f.[fmt.fmt, go!"intbuf"] ↦ ib) ∗
      "%Hxs" ∷ ⌜68 ≤ xs.length ∧ (wP = true → 3 + sint.Z wid ≤ xs.length) ∧
        xs.length ≤ 1000003⌝ ∗
      "f" ∷ f_ptr ↦ f ∗ "Hwid" ∷ f.[fmt.fmt, go!"wid"] ↦ wid ∗
      "Hprec" ∷ f.[fmt.fmt, go!"prec"] ↦ prec) with [buf Hsl Hwid Hprec f]
    as ⟨%sl, %xs, buf, Hsl, Hback, %Hxs, f, Hwid, Hprec⟩
  · iexists _, _
    iframe
    isplit
    · iintro %xs' Hsl'
      iapply fmt.slice68_to_array $$ Hsl'
    · ipureintro; exact ⟨by omega, False.elim, by omega⟩
  · obtain ⟨hze, hw0, hw1, rfl⟩ := hwid rfl
    wp_if_destruct
    · wp_apply wp_slice_make2 (V := w8) $$ [] as %sl' ⟨Hsl', _⟩
      · ipureintro; word
      wp_join_done
      iexists _, _
      iframe
      isplit
      · iintro %xs' _
        iapply fmt.slice68_to_array $$ Hsl
      · ipureintro; simp only [List.length_replicate]; word
    · wp_join_done
      iexists _, _
      iframe
      isplit
      · iintro %xs' Hsl'
        iapply fmt.slice68_to_array $$ Hsl'
      · ipureintro; word
  wp_join iprop("prec" ∷ prec_ptr ↦ (if wP then (if neg then wid - W64 1 else wid) else W64 0) ∗
      "f" ∷ f_ptr ↦ f ∗ "Hwid" ∷ f.[fmt.fmt, go!"wid"] ↦ wid ∗
      "Hflags" ∷ f.[fmt.fmt, go!"fmtFlags"] ↦
        fmt.fmtFlags.mk wP false false false false false ze pV sV ∗
      "negative" ∷ negative_ptr ↦ neg) at next
    with [prec f Hwid Hflags negative] as ⟨prec, f, Hwid, Hflags, negative⟩
  · cases wP
    · cases ze <;> dsimp only <;> wp_auto <;> wp_join_done
    · obtain ⟨rfl, -, -, -⟩ := hwid rfl
      dsimp only
      wp_auto
      cases neg <;> wp_auto <;> wp_join_done
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
  ipersist buf
  ipersist digits
  ipersist f
  ipersist base
  ipersist verb
  wp_join iprop(∃ (uc k : w64) (D : List w8), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
      "Hsl" ∷ sl ↦* (xs.take (sint.nat k) ++ D) ∗
      "%Hd" ∷ ⌜uc.toNat < uint.nat base ∧
        fmt.digitsOf (uint.nat base) U.toNat = fmt.hexDigitByte uc.toNat :: D ∧
        sint.Z k + D.length = xs.length ∧ 0 ≤ sint.Z k ∧ D.length < 20⌝) with [u i Hsl]
    as ⟨%uc, %k, %D, u, i, Hsl, %Hd⟩
  · -- base 10
    ihave IH : iprop(∃ (uc k : w64) (D : List w8), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
      "Hsl" ∷ sl ↦* (xs.take (sint.nat k) ++ D) ∗
      "%Hd" ∷ ⌜fmt.decimalNat U.toNat = fmt.decimalNat uc.toNat ++ D ∧
        sint.Z k + D.length = xs.length ∧ 0 ≤ sint.Z k⌝) $$ [u i Hsl]
    · iexists U, sl.len, []
      have : sint.nat sl.len = xs.length := by omega
      simp only [this, List.take_length, List.append_nil, List.length_nil]
      iframe
      ipureintro
      simp only [true_and]
      constructor <;> word
    wp_for IH
    have hDl := Hd.1 ▸ fmt.length_decimalNat_w64 U
    have hDl' := fmt.length_decimalNat_pos uc.toNat
    simp only [List.length_append] at hDl
    wp_if_destruct
    · -- `u >= 10`: one more digit
      have hge : 10 ≤ uc.toNat := by have h := Hif; simp at h; word
      have hkz : (sint.nat k : Int) = sint.Z k := by word
      have hslz : (sint.nat sl.len : Int) = sint.Z sl.len := by word
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by word
      rw [if_pos ⟨by omega, by omega⟩, fmt.digit10_eq]
      wp_apply wp_store_slice_index sl (sint.Z (k - W64 1)) _ _ $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; omega
      wp_auto
      wp_for_post
      iframe
      iexists (uc / W64 10), (k - W64 1), (fmt.digitByte (uc.toNat % 10) :: D)
      rw [show (sint.Z (k - W64 1)).toNat = sint.nat k - 1 by word,
        fmt.take_append_set _ _ _ _ (by omega) (by omega), hkn]
      iframe
      ipureintro
      refine ⟨?_, by simp only [List.length_cons]; omega, by omega⟩
      rw [Hd.1, fmt.decimalNat_of_ge hge, BitVec.toNat_udiv]
      simp
    · -- the last digit is left in `u`
      have hlt : uc.toNat < 10 := by word
      wp_join_done
      iexists uc, k, D
      iframe
      ipureintro
      have h10 : uint.nat (W64 10) = 10 := rfl
      rw [h10]
      refine ⟨hlt, ?_, Hd.2.1, Hd.2.2, by omega⟩
      rw [fmt.digitsOf, if_neg (by decide), Hd.1, fmt.decimalNat_of_lt hlt,
        fmt.digitByte_eq_hex hlt]
      rfl
  · -- base 16
    wp_if_destruct
    · ihave IH : iprop(∃ (uc k : w64) (D : List w8), "u" ∷ u_ptr ↦ uc ∗ "i" ∷ i_ptr ↦ k ∗
        "Hsl" ∷ sl ↦* (xs.take (sint.nat k) ++ D) ∗
        "%Hd" ∷ ⌜fmt.hexNat U.toNat = fmt.hexNat uc.toNat ++ D ∧
          sint.Z k + D.length = xs.length ∧ 0 ≤ sint.Z k⌝) $$ [u i Hsl]
      · iexists U, sl.len, []
        have : sint.nat sl.len = xs.length := by omega
        simp only [this, List.take_length, List.append_nil, List.length_nil]
        iframe
        ipureintro
        simp only [true_and]
        constructor <;> word
      wp_for IH
      have hDl := Hd.1 ▸ fmt.length_hexNat_w64 U
      have hDl' : 0 < (fmt.hexNat uc.toNat).length :=
        List.length_pos_iff.mpr (fmt.hexNat_ne_nil _)
      simp only [List.length_append] at hDl
      wp_if_destruct
      · -- `u >= 16`: one more digit
        have hge : 16 ≤ uc.toNat := by have h := Hif; simp at h; word
        have hkz : (sint.nat k : Int) = sint.Z k := by word
        have hslz : (sint.nat sl.len : Int) = sint.Z sl.len := by word
        have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
        have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by word
        have hand : uc &&& W64 15 = W64 (uc.toNat % 16 : Nat) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_and]
          have : (W64 15).toNat = 2 ^ 4 - 1 := rfl
          rw [this, Nat.and_two_pow_sub_one_eq_mod]
          word
        have hd16 : uc.toNat % 16 < 16 := Nat.mod_lt _ (by omega)
        rw [hand, if_pos (by word), show sint.nat (W64 (uc.toNat % 16 : Nat)) = uc.toNat % 16 by word,
          fmt.hexDigits_get _ hd16]
        wp_auto
        rw [if_pos ⟨by omega, by omega⟩]
        wp_apply wp_store_slice_index sl (sint.Z (k - W64 1)) _ _ $$ [Hsl] as Hsl
        · iframe; ipureintro; simp only [List.length_append, List.length_take]; omega
        wp_for_post
        iexists (uc >>> W64 4), (k - W64 1), (fmt.hexDigitByte (uc.toNat % 16) :: D)
        rw [show (sint.Z (k - W64 1)).toNat = sint.nat k - 1 by word,
          fmt.take_append_set _ _ _ _ (by omega) (by omega), hkn]
        iframe
        ipureintro
        refine ⟨?_, by simp only [List.length_cons]; omega, by omega⟩
        have hsh : (uc >>> W64 4).toNat = uc.toNat / 16 := by
          rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
        rw [Hd.1, fmt.hexNat_of_ge hge, hsh]
        simp
      · -- the last digit is left in `u`
        have hlt : uc.toNat < 16 := by word
        wp_join_done
        iexists uc, k, D
        iframe
        ipureintro
        have h16 : uint.nat (W64 16) = 16 := rfl
        rw [h16]
        refine ⟨hlt, ?_, Hd.2.1, Hd.2.2, by omega⟩
        rw [fmt.digitsOf, if_pos rfl, Hd.1, fmt.hexNat_of_lt hlt]
        rfl
    · exfalso
      rcases hbase with h | h <;> simp_all
  -- the last digit
  have hb16 : uint.nat base = 10 ∨ uint.nat base = 16 := by
    rcases hbase with rfl | rfl <;> simp
  have huc : uc.toNat < 16 := by omega
  have hkz : (sint.nat k : Int) = sint.Z k := by word
  have hslz : (sint.nat sl.len : Int) = sint.Z sl.len := by word
  have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
  have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by word
  have huc0 : 0 ≤ sint.Z uc := by word
  have hucn : sint.nat uc = uc.toNat := by word
  have hkb : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z sl.len := ⟨by omega, by omega⟩
  rw [if_pos huc0, hucn, fmt.hexDigits_get _ huc]
  wp_auto
  rw [if_pos hkb]
  wp_apply wp_store_slice_index sl (sint.Z (k - W64 1)) _ _ $$ [Hsl] as Hsl
  · iframe; ipureintro; simp only [List.length_append, List.length_take]; omega
  rw [show (sint.Z (k - W64 1)).toNat = sint.nat k - 1 by word,
    fmt.take_append_set _ _ _ _ (by omega) (by omega), ← hkn, ← Hd.2.1]
  generalize hS : fmt.digitsOf (uint.nat base) U.toNat = S at Hd
  have hSl : S.length ≤ 20 := by rw [Hd.2.1]; simp only [List.length_cons]; omega
  have hk1x : sint.Z (k - W64 1) + S.length = xs.length := by
    rw [Hd.2.1]; simp only [List.length_cons]; omega
  generalize k - W64 1 = k1 at hk1x hkb
  clear hkz hk1 hkn
  -- the precision (zero padding)
  have hPz := fmt.precZ wP neg wid (fun h => ⟨(hwid h).2.1, (hwid h).2.2.1⟩)
  generalize (if wP then (if neg then wid - W64 1 else wid) else W64 0) = Pw at hPz
  have hPn := fmt.precN wP neg wid Pw xs.length hPz
    (fun h => ⟨(hwid h).2.1, Hxs.2.1 h⟩) (by omega)
  ihave IH : iprop(∃ (k : w64) (m : Nat), "i" ∷ i_ptr ↦ k ∗
      "Hsl" ∷ sl ↦* (xs.take (sint.nat k) ++ (List.replicate m (W8 48) ++ S)) ∗
      "%Hm" ∷ ⌜sint.Z k + m + S.length = xs.length ∧ 0 ≤ sint.Z k ∧
        m + S.length ≤ max (sint.Z Pw).toNat S.length⌝) $$ [i Hsl]
  · iexists k1, 0
    simp only [List.replicate_zero, List.nil_append]
    iframe
    ipureintro
    omega
  wp_for IH
  have hkz : (sint.nat k : Int) = sint.Z k := by word
  have hslk : sint.Z (sl.len - k) = xs.length - sint.Z k := by word
  wp_if_destruct
  · have hk0 : 1 ≤ sint.Z k := by word
    wp_if_destruct
    · -- one more `0`
      have hlt : m + S.length < (sint.Z Pw).toNat := by omega
      have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by word
      have hkb : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z sl.len := ⟨by omega, by omega⟩
      rw [if_pos hkb]
      wp_apply wp_store_slice_index sl (sint.Z (k - W64 1)) _ _ $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take, List.length_replicate]; omega
      wp_for_post
      iframe
      iexists (k - W64 1), (m + 1)
      rw [show (sint.Z (k - W64 1)).toNat = sint.nat k - 1 by word,
        fmt.take_append_set _ _ _ _ (by omega) (by omega), hkn, List.replicate_succ, List.cons_append]
      iframe
      ipureintro
      omega
    · -- done: `len(buf) - i >= prec`
      have hge : (sint.Z Pw).toNat ≤ m + S.length := by omega
      have hm : List.replicate m (W8 48) ++ S = fmt.padZeros (sint.Z Pw).toNat S := by
        unfold fmt.padZeros; congr 2; omega
      rw [hm]
      generalize hZ : fmt.padZeros (sint.Z Pw).toNat S = Z
      have hZl : sint.Z k + Z.length = xs.length := by
        rw [← hZ, fmt.length_padZeros]; omega
      rw [decide_eq_false hverb]
      wp_auto
      wp_join iprop(∃ (k' : w64) (T : GoString), "i" ∷ i_ptr ↦ k' ∗
          "Hsl" ∷ sl ↦* (xs.take (sint.nat k') ++ T) ∗
          "Hflags" ∷ f.[fmt.fmt, go!"fmtFlags"] ↦
            fmt.fmtFlags.mk wP false false false false false ze pV sV ∗
          "%HT" ∷ ⌜T = (if neg then W8 45 :: Z else Z) ∧ sint.Z k' + T.length = xs.length ∧
            0 ≤ sint.Z k'⌝) with [i Hsl Hflags] as ⟨%k', %T, i, Hsl, Hflags, %HT⟩
      · iexists k, Z
        iframe
        ipureintro
        exact ⟨by simp, hZl, by omega⟩
      · -- negative: the sign
        have hk1 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
        have hkn : sint.nat (k - W64 1) = sint.nat k - 1 := by word
        have hkb : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z sl.len :=
          ⟨by omega, by omega⟩
        rw [if_pos hkb]
        wp_apply wp_store_slice_index sl (sint.Z (k - W64 1)) _ _ $$ [Hsl] as Hsl
        · iframe; ipureintro; simp only [List.length_append, List.length_take]; omega
        wp_join_done
        iexists (k - W64 1), (W8 45 :: Z)
        rw [show (sint.Z (k - W64 1)).toNat = sint.nat k - 1 by word,
          fmt.take_append_set _ _ _ _ (by omega) (by omega), hkn]
        iframe
        ipureintro
        refine ⟨by simp, by simp only [List.length_cons]; omega, by omega⟩
      -- `f.zero = false; f.pad(buf[i:]); f.zero = oldZero`
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have hsb : 0 ≤ sint.Z k' ∧ sint.Z k' ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap :=
        ⟨HT.2.2, by omega, Hwf.2⟩
      rw [if_pos hsb]
      icases (ownSlice_split_all (V := w8) k' sl _ _ ⟨HT.2.2, by omega⟩).1 $$ Hsl with ⟨Hpre, Hsuf⟩
      have hlenT : (List.take (sint.nat k') xs).length = sint.nat k' := by
        simp only [List.length_take]; have : (sint.nat k' : Int) = sint.Z k' := by word
        omega
      rw [List.drop_left' hlenT, List.take_left' hlenT]
      have hpad := fmt.pad_ok neg wP wid Pw S (hS ▸ fmt.digitsOf_ascii _ _)
        (fun h => (hwid h).2.1) hPz
      rw [hZ, ← HT.1] at hpad
      wp_auto
      wp_apply wp_pad f b (fmt.fmtFlags.mk wP false false false false false false pV sV) wid prec bs
        _ T (DFrac.own 1) hpad $$ [Hbuf Hflags Hwid Hprec Hb Hsuf] as ⟨Hown, Hb, Hsuf⟩
      · unfold fmt.fmtOwn; iframe
      unfold fmt.fmtOwn
      icases Hown with ⟨Hbuf, Hflags, Hwid, Hprec⟩
      wp_auto
      have e := ownSlice_split_all (GF := GF) (V := w8) k' sl (DFrac.own 1)
        (List.take (sint.nat k') xs ++ T) ⟨HT.2.2, by omega⟩
      rw [List.take_left' hlenT, List.drop_left' hlenT] at e
      ihave Hsl := e.2 $$ [Hpre Hsuf]
      · iframe
      ihave Hib := Hback $$ Hsl
      iapply HΦ
      rw [← fmt.intOut_eq base u isSigned neg hneg wP wid Pw (fun h => (hwid h).2.1) hPz, ← HU, hS,
        hZ, ← HT.1]
      iframe
  · -- `i == 0` cannot happen: the buffer is longer than the digits and the padding
    exfalso
    have : sint.Z k = 0 := by word
    omega

end proof

end Perennial
