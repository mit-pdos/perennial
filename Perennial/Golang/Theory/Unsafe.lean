/-
The program logic of package `unsafe` (`go.UnsafeSemantics`): memory reached through an
`unsafe.Pointer` is bytes (`CheckBytes`), so these WPs take the bytes they cross.
-/
module

public import Perennial.Golang.Theory.Auto

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- The address `go.pointerAddr` chooses is in `[8, 2^48 + 8)`. -/
theorem pointerAddr_bound (x y : w64) (hy : y.toNat < 8) :
    8 ≤ ((x % W64 (2^45-1) + W64 1) * W64 8 + y).toNat ∧
    ((x % W64 (2^45-1) + W64 1) * W64 8 + y).toNat < 2^48 + 8 := by
  have c1 : (W64 (2^45-1)).toNat = 2^45-1 := by decide
  have c2 : (W64 1).toNat = 1 := by decide
  have c3 : (W64 8).toNat = 8 := by decide
  have hm : (x % W64 (2^45-1)).toNat < 2^45-1 := by
    rw [BitVec.toNat_umod, c1]; exact Nat.mod_lt _ (by decide)
  have e1 : (x % W64 (2^45-1) + W64 1).toNat = (x % W64 (2^45-1)).toNat + 1 := by
    rw [BitVec.toNat_add, c2]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : ((x % W64 (2^45-1) + W64 1) * W64 8).toNat = ((x % W64 (2^45-1)).toNat + 1) * 8 := by
    rw [BitVec.toNat_mul, e1, c3]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, e2, Nat.mod_eq_of_lt (by omega)]
  omega

section unsafe_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- The cells of the bytes `bs`. -/
abbrev byteCells (bs : List w8) : List val := bs.map fun b => LitV (LitByte b)

theorem byteCells_bytes (bs : List w8) : ∀ v ∈ byteCells bs, ∃ b, v = LitV (LitByte b) := by
  intro v hv; simp only [byteCells, List.mem_map] at hv; obtain ⟨b, -, rfl⟩ := hv; exact ⟨b, rfl⟩

/-- `CheckBytes (l, n)` over owned bytes, with `n` as a `w64`. -/
theorem wp_CheckBytes (l : Loc) (dq : DFrac) (bs : List w8) (n : w64)
    (hn : uint.nat n = bs.length) :
    {{ ▷ pointstoVals (GF := GF) l dq (byteCells bs) }}
      (CheckBytes (Val (PairV #l #n))) @ s; E
    {{ RET #(); pointstoVals l dq (byteCells bs) }} := by
  rw [go.intoVal_unfold w64]
  exact wp_checkBytes l dq _ n (by simp [hn]) (byteCells_bytes bs)

/-- `(*t)(p)` for a `Reinterpretable` `t`, over the `t`'s bytes from `p`. -/
theorem wp_convert_unsafe_to_pointer (elem : go.GoType) [go.Reinterpretable elem] {V : Type}
    [ZeroVal V] [TypeRepr elem V] (l : Loc) (dq : DFrac) (bs : List w8)
    (hlen : (bs.length : Int) = typeSize V) (hsz : typeSize V < 2 ^ 64) :
    {{ (pointstoVals (GF := GF) l dq (byteCells bs)) }}
      (App (Val (GoInstruction (Convert «unsafe».Pointer (go.PointerType elem)))) (Val #l)) @ s; E
    {{ RET #l; pointstoVals l dq (byteCells bs) }} := by
  iintro %Φ Hl HΦ
  wp_pures
  by_cases hnull : l = null
  · subst hnull
    rw [if_pos rfl]
    wp_pures
    iapply HΦ $$ Hl
  · rw [if_neg hnull]
    have hn : uint.nat (W64 (typeSize V)) = (byteCells bs).length := by
      rw [show typeSize V = ((bs.length : Nat) : Int) from hlen.symm, uint_nat_W64 _ (by omega)]
      simp [byteCells]
    wp_bind (CheckBytes _)
    iapply (wp_checkBytes l dq _ (W64 (typeSize V)) hn (byteCells_bytes bs)) $$ Hl
    inext; iintro Hl; wp_pures; iapply HΦ $$ Hl

/-- `unsafe.Add(p, n)` for `n > 0`, over the bytes from `p` to `p + n` (both included). -/
theorem wp_unsafe_add_pos (p : Loc) (n : w64) (dq : DFrac) (bs : List w8) (hpos : 0 < sint.Z n)
    (hlen : (bs.length : Int) = sint.Z n + 1) :
    {{ (pointstoVals (GF := GF) p dq (byteCells bs)) }}
      (App (App (Val #(functions «unsafe».Add [])) (Val #p)) (Val #n)) @ s; E
    {{ RET #(p +ₗ sint.Z n); pointstoVals p dq (byteCells bs) }} := by
  iintro %Φ Hl HΦ
  wp_func_call
  wp_auto
  rw [decide_eq_false (show n ≠ W64 0 by intro h; subst h; simp at hpos)]
  wp_auto
  try rw [decide_eq_true (show sint.Z n > sint.Z (W64 0) by simpa using hpos)]
  wp_auto
  have hn : uint.nat (n + W64 1) = bs.length := by
    have h1 : uint.Z (n + W64 1) = sint.Z n + 1 := by word
    simp only [uint.Z] at h1
    simp only [uint.nat]; omega
  wp_bind (Primitive1 _ _)
  wp_apply_core (wp_CheckBytes p dq bs (n + W64 1) hn) $$ [Hl]
  · iexact Hl
  iintro Hl
  wp_auto
  iapply HΦ $$ Hl


/-- `unsafe.Add(p, n)` for `n < 0`, over the bytes from `p + n` to `p` (both included). -/
theorem wp_unsafe_add_neg (p : Loc) (n : w64) (dq : DFrac) (bs : List w8) (hneg : sint.Z n < 0)
    (hlen : (bs.length : Int) = 1 - sint.Z n) :
    {{ (pointstoVals (GF := GF) (p +ₗ sint.Z n) dq (byteCells bs)) }}
      (App (App (Val #(functions «unsafe».Add [])) (Val #p)) (Val #n)) @ s; E
    {{ RET #(p +ₗ sint.Z n); pointstoVals (p +ₗ sint.Z n) dq (byteCells bs) }} := by
  iintro %Φ Hl HΦ
  wp_func_call
  wp_auto
  rw [decide_eq_false (show n ≠ W64 0 by intro h; subst h; simp at hneg)]
  wp_auto
  try rw [decide_eq_false (show ¬ sint.Z n > sint.Z (W64 0) by simp; omega)]
  wp_auto
  have hn : uint.nat (W64 1 - n) = bs.length := by
    have h1 : uint.Z (W64 1 - n) = 1 - sint.Z n := by word
    simp only [uint.Z] at h1
    simp only [uint.nat]; omega
  wp_bind (Primitive1 _ _)
  wp_apply_core (wp_CheckBytes (p +ₗ sint.Z n) dq bs (W64 1 - n) hn) $$ [Hl]
  · iexact Hl
  iintro Hl
  wp_auto
  iapply HΦ $$ Hl

/-- `unsafe.Add(p, 0)` is `p`. -/
theorem wp_unsafe_add_zero (p : Loc) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions «unsafe».Add [])) (Val #p)) (Val #(W64 0))) @ s; E
    {{ RET #p; True }} := by
  iintro %Φ _ HΦ
  wp_func_call
  wp_auto
  iapply HΦ; itrivial

/-- `uintptr(p)`: some address, `0` for `nil`. -/
theorem wp_convert_pointer_to_uintptr (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (Convert «unsafe».Pointer go.uintptr))) (Val #l)) @ s; E
    {{ (a : w64), RET #a; ⌜l = null → a = W64 0⌝ }} := by
  iintro %Φ _ HΦ
  wp_pures
  by_cases hnull : l = null
  · rw [if_pos hnull]
    wp_pures
    iapply HΦ; ipureintro; intro; rfl
  · rw [if_neg hnull]
    unfold go.pointerAddr
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    rw [if_neg (by decide)]
    wp_pures
    iapply HΦ; ipureintro; intro h; exact absurd h hnull

/-- `uintptr(p) - uintptr(q)` (as goose emits it): the distance between two pointers into
one block. -/
theorem wp_ptr_diff (l1 l2 : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoOp GoSub «unsafe».Pointer))) (Val (PairV #l1 #l2))) @ s; E
    {{ (d : w64), RET #d; ⌜l1.locCar = l2.locCar → d = W64 (l1.locOff - l2.locOff)⌝ }} := by
  iintro %Φ _ HΦ
  wp_pures
  by_cases hc : l1.locCar = l2.locCar
  · rw [if_pos hc]
    wp_pures
    iapply HΦ; ipureintro; intro; rfl
  · rw [if_neg hc]
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    iapply HΦ; ipureintro; intro h; exact absurd h hc


/-- `CheckCopy t (dst, src)`, the check goose emits before `dst = src` with `src` in memory:
it steps when the copy cannot overlap partially. -/
theorem wp_check_copy (t : go.GoType) {V : Type} [ZeroVal V] [TypeRepr t V] (dst src : Loc)
    (h : go.NoPartialOverlap (typeSize V) dst src) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (CheckCopy t))) (Val (PairV #dst #src))) @ s; E
    {{ RET #(); True }} := by
  haveI := go.check_copy t dst src h
  iintro %Φ _ HΦ
  wp_pures
  iapply HΦ; itrivial

/-- Owning all of `n` cells from `dst` and some of `n` cells from `src` rules out a partial
overlap: they would share a cell. -/
theorem pointstoVals_noPartialOverlap (dst src : Loc) (dq : DFrac) (vs ws : List val) (n : Int)
    (h1 : (vs.length : Int) = n) (h2 : (ws.length : Int) = n) :
    pointstoVals (GF := GF) dst (.own 1) vs ∗ pointstoVals src dq ws ⊢
      ⌜go.NoPartialOverlap n dst src⌝ := by
  by_cases hno : go.NoPartialOverlap n dst src
  · iintro -; ipureintro; exact hno
  unfold go.NoPartialOverlap at hno
  simp only [not_or] at hno
  obtain ⟨hne, -, hcar, hlt1, hlt2⟩ := hno
  have hcar : dst.locCar = src.locCar := Classical.not_not.mp hcar
  have hoff : dst.locOff ≠ src.locOff := by
    intro ho; apply hne; cases dst; cases src; simp_all
  unfold pointstoVals
  iintro ⟨H1, H2⟩
  -- the cell at the larger of the two offsets is in both ranges
  by_cases hd : src.locOff < dst.locOff
  · have hj : (dst.locOff - src.locOff).toNat < ws.length := by omega
    obtain ⟨w, hw⟩ : ∃ w, ws[(dst.locOff - src.locOff).toNat]? = some w :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨v, hv⟩ : ∃ v, vs[0]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave Hv := BigSepL.bigSepL_lookup (Φ := fun j vj => heapPointsto (dst +ₗ (j : Int)) (.own 1) vj) hv $$ H1
    ihave Hw := BigSepL.bigSepL_lookup (Φ := fun j vj => heapPointsto (src +ₗ (j : Int)) dq vj) hw $$ H2
    have hl : src +ₗ ((dst.locOff - src.locOff).toNat : Int) = dst +ₗ ((0 : Nat) : Int) := by
      cases dst; cases src; simp only [Loc.add, Loc.mk.injEq] at *; omega
    rw [hl]
    icombine Hv Hw gives %hv'
    exact absurd hv'.1 CMRA.not_valid_excl_op_left
  · have hj : (src.locOff - dst.locOff).toNat < vs.length := by omega
    obtain ⟨v, hv⟩ : ∃ v, vs[(src.locOff - dst.locOff).toNat]? = some v :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨w, hw⟩ : ∃ w, ws[0]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave Hv := BigSepL.bigSepL_lookup (Φ := fun j vj => heapPointsto (dst +ₗ (j : Int)) (.own 1) vj) hv $$ H1
    ihave Hw := BigSepL.bigSepL_lookup (Φ := fun j vj => heapPointsto (src +ₗ (j : Int)) dq vj) hw $$ H2
    have hl : dst +ₗ ((src.locOff - dst.locOff).toNat : Int) = src +ₗ ((0 : Nat) : Int) := by
      cases dst; cases src; simp only [Loc.add, Loc.mk.injEq] at *; omega
    rw [hl]
    icombine Hv Hw gives %hv'
    exact absurd hv'.1 CMRA.not_valid_excl_op_left

/-- `unsafe.Slice(p, n)` for a `Reinterpretable` element type of positive size, over the
slice's bytes. -/
theorem wp_unsafe_slice (t : go.GoType) [go.Reinterpretable t] {V : Type} [ZeroVal V]
    [TypeRepr t V] (p : Loc) (n : w64) (dq : DFrac) (bs : List w8) (hp : p ≠ null)
    (hsz : 0 < typeSize V) (hn : 0 < sint.Z n) (hmem : sint.Z n * typeSize V < 2 ^ 47)
    (hlen : (bs.length : Int) = sint.Z n * typeSize V) :
    {{ (pointstoVals (GF := GF) p dq (byteCells bs)) }}
      (App (App (Val #(functions «unsafe».Slice [t])) (Val #p)) (Val #n)) @ s; E
    {{ RET #(slice.mk p n n); pointstoVals p dq (byteCells bs) }} := by
  iintro %Φ Hl HΦ
  wp_func_call
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by simp; omega)]
  simp only [if_neg (show ¬ typeSize V = 0 by omega)]
  wp_auto
  rw [if_neg hp]
  unfold go.pointerAddr
  wp_bind ArbitraryInt
  wp_apply wp_ArbitraryInt as %x -
  wp_pures
  rw [if_neg (by decide)]
  wp_auto
  have hnu : uint.Z n = sint.Z n := by word
  have hq : sint.Z n ≤ (2 ^ 64 - 1) / typeSize V :=
    (Int.le_ediv_iff_mul_le hsz).2 (by omega)
  have hq0 : 0 ≤ (2 ^ 64 - 1) / typeSize V := Int.ediv_nonneg (by decide) (by omega)
  have hq1 : (2 ^ 64 - 1) / typeSize V < 2 ^ 64 :=
    Int.lt_of_le_of_lt (Int.ediv_le_self _ (by decide)) (by decide)
  have hc1 : ¬ uint.Z (W64 ((2 ^ 64 - 1) / typeSize V)) < uint.Z n := by
    rw [hnu, show uint.Z (W64 ((2 ^ 64 - 1) / typeSize V)) = (2 ^ 64 - 1) / typeSize V by
      simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega]
    omega
  rw [decide_eq_false hc1]
  wp_auto
  have hszb : typeSize V < 2 ^ 47 := by
    have : 1 * typeSize V ≤ sint.Z n * typeSize V :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  have hszu : uint.Z (W64 (typeSize V)) = typeSize V := by
    simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega
  have hmul : uint.Z (n * W64 (typeSize V)) = sint.Z n * typeSize V := by
    have e : uint.Z (n * W64 (typeSize V)) = (uint.Z n * uint.Z (W64 (typeSize V))) % 2 ^ 64 := by
      simp only [uint.Z, BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul]; rfl
    rw [e, hnu, hszu]
    exact Int.emod_eq_of_lt (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hoff : (W64 (p.locOff % 8)).toNat < 8 := by
    have h1 := Int.emod_nonneg p.locOff (show (8 : Int) ≠ 0 by decide)
    have h2 := Int.emod_lt_of_pos p.locOff (show (0 : Int) < 8 by decide)
    simp only [W64, BitVec.toNat_ofInt]; omega
  have hc2 : ¬ uint.Z (W64 0 - ((x % W64 (2 ^ 45 - 1) + W64 1) * W64 8 + W64 (p.locOff % 8))) <
      uint.Z (n * W64 (typeSize V)) := by
    rw [hmul]
    obtain ⟨hA1, hA2⟩ := pointerAddr_bound x _ hoff
    generalize (x % W64 (2 ^ 45 - 1) + W64 1) * W64 8 + W64 (p.locOff % 8) = A at hA1 hA2 ⊢
    have : (W64 0 - A).toNat = 2 ^ 64 - A.toNat := by
      rw [BitVec.toNat_sub, show (W64 0).toNat = 0 by decide]; omega
    simp only [uint.Z, this]; omega
  rw [decide_eq_false hc2]
  wp_auto
  rw [decide_eq_false (show n ≠ W64 0 by intro h; subst h; simp at hn)]
  wp_auto
  have hbn : uint.nat (n * W64 (typeSize V)) = bs.length := by
    have := hmul; simp only [uint.Z] at this; simp only [uint.nat]; omega
  wp_bind (Primitive1 _ _)
  wp_apply_core (wp_CheckBytes p dq bs (n * W64 (typeSize V)) hbn) $$ [Hl]
  · iexact Hl
  iintro Hl
  wp_auto
  try iapply HΦ $$ Hl


/-- `(*[n]t)(p)[lo:hi:max]` (`unsafe.ArraySlice`) within bounds, over the `max` elements'
bytes. -/
theorem wp_unsafe_array_slice (n : Int) (t : go.GoType) [go.Reinterpretable t] {V : Type}
    [ZeroVal V] [TypeRepr t V] (p : Loc) (lo hi mx : w64) (dq : DFrac) (bs : List w8)
    (hp : p ≠ null)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z mx ∧ sint.Z mx ≤ n)
    (hpos : 0 < sint.Z mx) (hmem : sint.Z mx * typeSize V < 2 ^ 63)
    (hlen : (bs.length : Int) = sint.Z mx * typeSize V) :
    {{ (pointstoVals (GF := GF) p dq (byteCells bs)) }}
      (App (App (App (App (Val #(functions «unsafe».ArraySlice [go.ArrayType n t])) (Val #p))
        (Val #lo)) (Val #hi)) (Val #mx)) @ s; E
    {{ RET #(slice.mk (arrayIndexRef V (sint.Z lo) p) (hi - lo) (mx - lo));
        pointstoVals p dq (byteCells bs) }} := by
  iintro %Φ Hl HΦ
  wp_func_call
  wp_auto
  rw [if_neg hp, if_pos hb]
  wp_auto
  rw [decide_eq_false (show mx ≠ W64 0 by intro h; subst h; simp at hpos)]
  wp_auto
  have hsz := go.typeSize_nonneg V
  have hbn : uint.nat (mx * W64 (typeSize V)) = bs.length := by
    have hmu : uint.Z (mx * W64 (typeSize V)) = sint.Z mx * typeSize V := by
      have hszb : typeSize V < 2 ^ 63 := by
        have : 1 * typeSize V ≤ sint.Z mx * typeSize V :=
          Int.mul_le_mul_of_nonneg_right (by omega) hsz
        omega
      have hszu : uint.Z (W64 (typeSize V)) = typeSize V := by
        simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega
      have hnu : uint.Z mx = sint.Z mx := by word
      have e : uint.Z (mx * W64 (typeSize V)) = (uint.Z mx * uint.Z (W64 (typeSize V))) % 2 ^ 64 := by
        simp only [uint.Z, BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul]; rfl
      rw [e, hnu, hszu]
      exact Int.emod_eq_of_lt (Int.mul_nonneg (by omega) hsz) (by omega)
    simp only [uint.Z] at hmu; simp only [uint.nat]; omega
  wp_bind (Primitive1 _ _)
  wp_apply_core (wp_CheckBytes p dq bs (mx * W64 (typeSize V)) hbn) $$ [Hl]
  · iexact Hl
  iintro Hl
  wp_auto
  try iapply HΦ $$ Hl

/-- A `float64` operation's result (`go.floatResult64`): some `float64`, its bits being
observable through package `unsafe`, so a NaN result is any NaN. -/
theorem wp_floatResult64 (r : w64) (Φ : val → IProp GF) :
    (∀ f : w64, Φ #f) ⊢ WP (go.floatResult64 r) @ s; E {{ Φ }} := by
  iintro HΦ
  unfold go.floatResult64
  split
  · unfold go.arbitraryNaN64
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    rw [if_neg (by decide)]
    wp_pures
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %y -
    wp_pures
    rw [if_neg (by decide)]
    wp_pures
    iapply HΦ
  · wp_pures
    iapply HΦ

/-- `go.floatResult32`, for `float32`. -/
theorem wp_floatResult32 (r : w32) (Φ : val → IProp GF) :
    (∀ f : w32, Φ #f) ⊢ WP (go.floatResult32 r) @ s; E {{ Φ }} := by
  iintro HΦ
  unfold go.floatResult32
  split
  · unfold go.arbitraryNaN32
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    rw [if_neg (by decide)]
    wp_pures
    wp_bind ArbitraryInt
    wp_apply wp_ArbitraryInt as %y -
    wp_pures
    rw [if_neg (by decide)]
    wp_pures
    iapply HΦ
  · wp_pures
    iapply HΦ

end unsafe_wps

end Perennial
