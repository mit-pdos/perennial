/-
Shared definitions of the proofs of the Go `crypto/sha1` package: its `isPkgInit` (the package has
no variables; its `init` is a trusted no-op, TrustedCode/crypto/sha1.lean), the five state words
as the array `digest.h` holds them (`stArr`), and the state of a `digest` that has absorbed a
message (`absorbed`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto.sha1
public import Perennial.GeneratedProof.crypto.sha1
public import Perennial.Proof.crypto.internal.boring.Base
public import Perennial.Proof.crypto.internal.fips140only.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.hash.Base
public import Perennial.Proof.internal.byteorder.Base
public import Perennial.Proof.math.bits.Base
public import Perennial.Proof.crypto.sha1.Fips180

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.sha1

/-- The five state words, as `digest.h` holds them. -/
def stArr : St → GoArray w32 5
  | (a, b, c, d, e) => array.mk 5 [a, b, c, d, e]

/-- **A digest's state words `h`, buffer `x` and count `nx` after absorbing `m`**: the words are
the compression of `m`'s full blocks (`compressAll`), and the buffer holds the rest of `m` (fewer
than 64 bytes) in its first `nx` bytes. -/
def absorbedHX [GooseExts] (h : GoArray w32 5) (x : List w8) (nx : w64) (m : List w8) : Prop :=
  h = stArr (compressAll init m) ∧
  sint.Z nx = (m.length % 64 : Nat) ∧
  x.take (m.length % 64) = m.drop (64 * (m.length / 64))

/-- **`d` has absorbed the message `m`** (`absorbedHX`), and its `len` is `m`'s length (mod 2^64,
as Go's `uint64` counts it). -/
def absorbed [GooseExts] (d : digest) (m : List w8) : Prop :=
  absorbedHX d.h' d.x'.arr d.nx' m ∧ d.len' = W64 m.length

theorem stArr_inj (a b : St) (h : stArr a = stArr b) : a = b := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  obtain ⟨b0, b1, b2, b3, b4⟩ := b
  simp only [stArr] at h
  injection h with h
  simp only [List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := h
  rfl

/-- The full blocks of `m` are those of its first `64 * q` bytes. -/
theorem compressAll_append_short (h : St) (m c : List w8) (hc : m.length % 64 + c.length < 64) :
    compressAll h (m ++ c) = compressAll h m := by
  rw [compressAll_take _ (m ++ c), compressAll_take _ m]
  have hq : (m ++ c).length / 64 = m.length / 64 := by simp only [List.length_append]; omega
  rw [hq, List.take_append_of_le_length (by omega)]

/-- Appending fewer bytes than the buffer has room for. -/
theorem absorbedHX_fill [GooseExts] (h : GoArray w32 5) (x : List w8) (nx : w64) (m c : List w8)
    (H : absorbedHX h x nx m) (hx : x.length = 64) (hc : m.length % 64 + c.length < 64) :
    absorbedHX h (x.take (m.length % 64) ++ (c ++ (x.drop (m.length % 64)).drop c.length))
      (nx + W64 (c.length : Int)) (m ++ c) := by
  obtain ⟨Hh, Hnx, Hx⟩ := H
  refine ⟨by rw [compressAll_append_short _ _ _ hc]; exact Hh, ?_, ?_⟩
  · have : (m ++ c).length % 64 = m.length % 64 + c.length := by
      simp only [List.length_append]; omega
    rw [this]; word
  · have e1 : (m ++ c).length % 64 = m.length % 64 + c.length := by
      simp only [List.length_append]; omega
    have e2 : (m ++ c).length / 64 = m.length / 64 := by simp only [List.length_append]; omega
    have hr : (x.take (m.length % 64)).length = m.length % 64 := by simp; omega
    rw [e1, e2, List.take_append, hr, List.take_of_length_le (by omega),
      show m.length % 64 + c.length - m.length % 64 = c.length by omega,
      List.take_append, List.take_of_length_le (Nat.le_refl _), Nat.sub_self,
      List.take_zero, List.append_nil, List.drop_append_of_le_length (by omega), Hx]

/-- With `nx = 0`, `m` is a whole number of blocks. -/
theorem absorbedHX_mod0 [GooseExts] (h : GoArray w32 5) (x : List w8) (m : List w8)
    (H : absorbedHX h x (W64 0) m) : m.length % 64 = 0 := by
  have := H.2.1; simp only [show sint.Z (W64 0) = 0 from rfl] at this; omega

/-- Filling the buffer up to a block, which `block` then compresses. -/
theorem absorbedHX_fill_block [GooseExts] (hs : St) (x : List w8) (nx : w64) (m c : List w8)
    (H : absorbedHX (stArr hs) x nx m) (hc : c.length = 64 - m.length % 64)
    (x'' : List w8) :
    absorbedHX (stArr (compressAll hs (x.take (m.length % 64) ++ c))) x'' (W64 0) (m ++ c) := by
  obtain ⟨Hh, Hnx, Hx⟩ := H
  have hs' : hs = compressAll init m := stArr_inj _ _ Hh
  have hm : m ++ c = m.take (64 * (m.length / 64)) ++ (x.take (m.length % 64) ++ c) := by
    rw [Hx, ← List.append_assoc, List.take_append_drop]
  have hlen : (m ++ c).length % 64 = 0 := by simp only [List.length_append, hc]; omega
  have hca : compressAll init (m ++ c) = compressAll hs (x.take (m.length % 64) ++ c) := by
    rw [hm, compressAll_append _ _ _ (by simp; omega), ← compressAll_take, ← hs']
  refine ⟨by rw [hca], ?_, ?_⟩
  · rw [hlen]; rfl
  · rw [hlen, List.take_zero]
    symm; apply List.drop_eq_nil_of_le; omega

/-- Compressing whole blocks into a digest with an empty buffer. -/
theorem absorbedHX_blocks [GooseExts] (hs : St) (x : List w8) (m c : List w8)
    (H : absorbedHX (stArr hs) x (W64 0) m) (hc : c.length % 64 = 0) :
    absorbedHX (stArr (compressAll hs c)) x (W64 0) (m ++ c) := by
  have hm0 := absorbedHX_mod0 _ _ _ H
  obtain ⟨Hh, Hnx, Hx⟩ := H
  have hs' : hs = compressAll init m := stArr_inj _ _ Hh
  have hlen : (m ++ c).length % 64 = 0 := by simp only [List.length_append]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [compressAll_append _ _ _ hm0, hs']
  · rw [hlen]; rfl
  · rw [hlen, List.take_zero]
    symm; apply List.drop_eq_nil_of_le; omega

/-- Copying the last bytes (fewer than a block) into an empty buffer. -/
theorem absorbedHX_tail [GooseExts] (h : GoArray w32 5) (x : List w8) (m c : List w8) (n : w64)
    (H : absorbedHX h x (W64 0) m) (hc : c.length < 64) (hn : sint.Z n = (c.length : Int)) :
    absorbedHX h (c ++ x.drop c.length) n (m ++ c) := by
  have hm0 := absorbedHX_mod0 _ _ _ H
  obtain ⟨Hh, Hnx, Hx⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · rw [compressAll_append_short _ _ _ (by omega)]; exact Hh
  · rw [hn]; simp only [List.length_append]; omega
  · have e1 : (m ++ c).length % 64 = c.length := by simp only [List.length_append]; omega
    have e2 : 64 * ((m ++ c).length / 64) = m.length := by simp only [List.length_append]; omega
    rw [e1, e2, List.take_left' rfl, List.drop_left]

/-- `x &^ 63` clears the low six bits. -/
theorem bitclear63 (x : BitVec 64) : x &&& ~~~(BitVec.ofNat 64 63) = (x >>> 6) <<< 6 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases h : i < 6
  · have e : ∀ j, j < 6 → Nat.testBit (63 % 2 ^ 64) j = true := by decide
    have h63 : (BitVec.ofNat 64 63)[i] = true := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; exact e i h
    simp [h, h63]
  · have h63 : (BitVec.ofNat 64 63)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 63 % 2 ^ 64 < 2 ^ 6)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [h, decide_false, Bool.not_false, h63, Bool.and_true, Bool.true_and]
    rw [show 6 + (i - 6) = i by omega, BitVec.getLsbD_eq_getElem hi]
theorem bitclear63_toNat (x : BitVec 64) : (x &&& ~~~(BitVec.ofNat 64 63)).toNat = 64 * (x.toNat / 64) := by
  rw [bitclear63, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have := x.isLt
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- Big-endian bytes are the little-endian ones reversed. -/
theorem u32Le_rev (v : w32) : (u32Le v).reverse = bytes32 v := by
  simp only [u32Le, u32LeDef, LittleEndian.split, bytes32, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, Nat.div_div_eq_div_mul]
theorem u64Le_rev (v : w64) : (u64Le v).reverse = bytes64 v := by
  simp only [u64Le, u64LeDef, LittleEndian.split, bytes64, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, Nat.div_div_eq_div_mul]
  simp [List.range_succ]

theorem w64_mod64 (L : Nat) : (W64 (L : Int) % W64 64).toNat = L % 64 := by
  rw [BitVec.toNat_umod]
  have h1 : (W64 (L : Int)).toNat = L % 2 ^ 64 := by simp [W64]
  have h2 : (W64 64).toNat = 64 := rfl
  rw [h1, h2, Nat.mod_mod_of_dvd _ (by decide)]
theorem w64_shl3 (L : Nat) : W64 (L : Int) <<< W64 3 = BitVec.ofNat 64 (L * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have h1 : (W64 (L : Int)).toNat = L % 2 ^ 64 := by simp [W64]
  have h2 : (W64 3).toNat = 3 := rfl
  rw [h1, h2, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_mul_mod]

/-- `checkSum`'s padding is FIPS 180-4's. -/
theorem pad_go (m : List w8) :
    m ++ ((W8 128 :: List.replicate ((119 - m.length % 64) % 64) (W8 0)) ++
      bytes64 (BitVec.ofNat 64 (m.length * 8))) = pad m := by
  simp only [pad, List.append_assoc, List.singleton_append]
  rfl

/-- The padding buffer `tmp[:t+8]` with `tmp[0] = 0x80`. -/
theorem tmp_take (tN : Nat) (h : tN + 8 ≤ 72) :
    ((List.replicate 72 (W8 0)).set 0 (W8 128)).take (tN + 8) =
      W8 128 :: List.replicate (tN + 7) (W8 0) := by
  rw [show (72 : Nat) = 71 + 1 from rfl, List.replicate_succ, List.set_cons_zero,
    show tN + 8 = (tN + 7) + 1 by omega, List.take_succ_cons, List.take_replicate]
  congr 2; omega

theorem tmp_split (tN : Nat) (h1 : 1 ≤ tN) :
    (W8 128 :: List.replicate (tN + 7) (W8 0)).take tN = W8 128 :: List.replicate (tN - 1) (W8 0) ∧
    (W8 128 :: List.replicate (tN + 7) (W8 0)).drop tN = List.replicate 8 (W8 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, tN = k + 1 := ⟨tN - 1, by omega⟩
  simp only [List.take_succ_cons, List.drop_succ_cons, List.take_replicate, List.drop_replicate,
    Nat.add_sub_cancel]
  constructor <;> congr 2 <;> omega

/-- Go's big-endian word of four bytes (`uint32(b0)<<24 | uint32(b1)<<16 | uint32(b2)<<8 |
uint32(b3)`) is `be32At`'s. -/
theorem be32_go (w0 w1 w2 w3 : w8) :
    (W32 (uint.Z w0) <<< W64 24 ||| W32 (uint.Z w1) <<< W64 16 ||| W32 (uint.Z w2) <<< W64 8 |||
      W32 (uint.Z w3)) = be32At [w0, w1, w2, w3] 0 := by
  have h := encoding.binary.leToU32_4 w3 w2 w1 w0
  have e : ∀ a b c d : w32, a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
    intro a b c d; ac_rfl
  rw [e, ← h, leToU32, leToU32Def, be32At, List.drop_zero]
  congr 1
  simp only [LittleEndian.combine, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil]
  omega

/-- The four bytes of `l` at `i`, as `be32At` reads them. -/
theorem be32At_eq (l : List w8) (i : Nat) (w0 w1 w2 w3 : w8) (h0 : l[i]? = some w0)
    (h1 : l[i + 1]? = some w1) (h2 : l[i + 2]? = some w2) (h3 : l[i + 3]? = some w3) :
    be32At l i = be32At [w0, w1, w2, w3] 0 := by
  have : (l.drop i).take 4 = [w0, w1, w2, w3] := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, List.getElem?_drop]
    rcases j with _ | _ | _ | _ | j
    · simpa using h0
    · simpa [Nat.add_comm] using h1
    · simpa [Nat.add_comm] using h2
    · simpa [Nat.add_comm] using h3
    · simp only [show ¬ (j + 1 + 1 + 1 + 1 < 4) by omega, if_false]; simp
  simp only [be32At, this, List.drop_zero, List.take]

/-- One step of `blockGeneric`'s first loop: `w[i]` gets the `i`-th big-endian word of the
block, the schedule's word `i`. -/
theorem wfill_step (l : List w8) (i : Nat) (hi : i < 16) (wl : List w32)
    (Hwlen : wl.length = 16) (Hwl : ∀ t, t < i → wl[t]! = sched (l.take 64) t)
    (b0 b1 b2 b3 : w8) (hb0 : l[4 * i + 0]? = some b0) (hb1 : l[4 * i + 1]? = some b1)
    (hb2 : l[4 * i + 2]? = some b2) (hb3 : l[4 * i + 3]? = some b3) :
    (wl.set i (W32 (uint.Z b0) <<< W64 24 ||| W32 (uint.Z b1) <<< W64 16 |||
        W32 (uint.Z b2) <<< W64 8 ||| W32 (uint.Z b3))).length = 16 ∧
    ∀ t, t < i + 1 → (wl.set i (W32 (uint.Z b0) <<< W64 24 ||| W32 (uint.Z b1) <<< W64 16 |||
        W32 (uint.Z b2) <<< W64 8 ||| W32 (uint.Z b3)))[t]! = sched (l.take 64) t := by
  refine ⟨by simp [Hwlen], fun t ht => ?_⟩
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split
  · rename_i h; subst h
    simp only [show i < wl.length by omega, ite_true, Option.getD_some]
    rw [be32_go, sched_lt _ _ hi, ← be32At_eq (l.take 64) (4 * i) b0 b1 b2 b3
      (by rw [List.getElem?_take]; simp only [show 4 * i < 64 by omega, ite_true]; simpa using hb0)
      (by rw [List.getElem?_take]; simp only [show 4 * i + 1 < 64 by omega, ite_true]; exact hb1)
      (by rw [List.getElem?_take]; simp only [show 4 * i + 2 < 64 by omega, ite_true]; exact hb2)
      (by rw [List.getElem?_take]; simp only [show 4 * i + 3 < 64 by omega, ite_true]; exact hb3)]
  · rw [← List.getElem!_eq_getElem?_getD]; exact Hwl t (by omega)

/-- `n & 15` of a small `int` `n` is `n mod 16`. -/
theorem sint_and15 (n : Nat) (h : n < 2 ^ 63) :
    sint.Z (W64 (n : Int) &&& W64 15) = ((n % 16 : Nat) : Int) := by
  have hx : (W64 (n : Int) &&& W64 15).toNat = n % 16 := by
    rw [BitVec.toNat_and]
    have : (W64 (n : Int)).toNat = n := by
      simp only [W64, BitVec.toNat_ofInt]; omega
    rw [this]
    show n &&& 15 = n % 16
    exact Nat.and_two_pow_sub_one_eq_mod n 4
  have hlt : 2 * (W64 (n : Int) &&& W64 15).toNat < 2 ^ 64 := by rw [hx]; omega
  simp only [sint.Z]
  rw [BitVec.toInt_eq_toNat_of_lt hlt, hx]

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- Load an element of an array through its address. -/
theorem wp_load_array_elem {t : go.GoType} [IntoValTyped (GF := GF) V t] (l : Loc) (n : Int)
    (vs : List V) (j : Nat) (v : V) (hv : vs[j]? = some v) :
    {{ (typedPointsto l (array.mk n vs) (DFrac.own 1) : IProp GF) }}
      (App (Val (GoInstruction (GoLoad t))) (Val #(arrayIndexRef V (j : Int) l)))
    {{ RET #v; typedPointsto l (array.mk n vs) (DFrac.own 1) }} := by
  wp_start as Hl
  icases array_acc (V := V) l (j : Int) _ n (array.mk n vs) v (by omega)
    (by rw [Int.toNat_natCast]; exact hv) $$ Hl with ⟨He, Hl⟩
  wp_apply IntoValTyped.wp_load (t := t) _ _ _ $$ He as He
  iapply HΦ
  ihave Hl := Hl $$ %v He
  rw [Int.toNat_natCast, list_set_lookup_self vs j v hv]
  iexact Hl

/-- Store an element of an array through its address. -/
theorem wp_store_array_elem {t : go.GoType} [IntoValTyped (GF := GF) V t] (l : Loc) (n : Int)
    (vs : List V) (j : Nat) (hj : j < vs.length) (v' : V) :
    {{ (typedPointsto l (array.mk n vs) (DFrac.own 1) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #(arrayIndexRef V (j : Int) l) #v')))
    {{ RET #(); typedPointsto l (array.mk n (vs.set j v')) (DFrac.own 1) }} := by
  wp_start as Hl
  obtain ⟨v, hv⟩ : ∃ v, vs[j]? = some v := ⟨_, List.getElem?_eq_getElem hj⟩
  icases array_acc (V := V) l (j : Int) _ n (array.mk n vs) v (by omega)
    (by rw [Int.toNat_natCast]; exact hv) $$ Hl with ⟨He, Hl⟩
  wp_apply IntoValTyped.wp_store (t := t) _ _ _ $$ He as He
  iapply HΦ
  ihave Hl := Hl $$ %v' He
  rw [Int.toNat_natCast]
  iexact Hl

/-- Store an element of an array through its address (an integer index). -/
theorem wp_store_array_elem_int {t : go.GoType} [IntoValTyped (GF := GF) V t] (l : Loc) (n : Int)
    (vs : List V) (i : Int) (hi : 0 ≤ i ∧ i.toNat < vs.length) (v' : V) :
    {{ (typedPointsto l (array.mk n vs) (DFrac.own 1) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #(arrayIndexRef V i l) #v')))
    {{ RET #(); typedPointsto l (array.mk n (vs.set i.toNat v')) (DFrac.own 1) }} := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi.1
  simp only [Int.toNat_natCast] at hi ⊢
  exact wp_store_array_elem (GF := GF) (V := V) (t := t) l n vs m hi.2 v'

/-- Load an element of an array through its address (an integer index). -/
theorem wp_load_array_elem_int {t : go.GoType} [IntoValTyped (GF := GF) V t] (l : Loc) (n : Int)
    (vs : List V) (i : Int) (v : V) (hi : 0 ≤ i) (hv : vs[i.toNat]? = some v) :
    {{ (typedPointsto l (array.mk n vs) (DFrac.own 1) : IProp GF) }}
      (App (Val (GoInstruction (GoLoad t))) (Val #(arrayIndexRef V i l)))
    {{ RET #v; typedPointsto l (array.mk n vs) (DFrac.own 1) }} := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  simp only [Int.toNat_natCast] at hv
  exact wp_load_array_elem (GF := GF) (V := V) (t := t) l n vs m v hv

/-- An array is a slice of its whole length. -/
theorem slice_of_array (l : Loc) (n : Nat) (hn : n < 2 ^ 63) (vs : List V) (dq : DFrac) (c : w64)
    (hc : sint.Z (W64 (n : Int)) ≤ sint.Z c) :
    typedPointsto (GF := GF) l (array.mk (n : Int) vs) dq ⊢ slice.mk l (W64 (n : Int)) c ↦*{dq} vs := by
  iintro H
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  have : sint.Z (W64 (n : Int)) = (n : Int) := by
    simp only [sint.Z, W64, BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
  simp only
  rw [this]
  iframe H
  ipureintro; omega

/-- A non-nil slice's elements are an array. -/
theorem array_of_slice (l : Loc) (n : Nat) (hn : n < 2 ^ 63) (vs : List V) (dq : DFrac) (c : w64)
    (hl : l ≠ null) :
    (slice.mk l (W64 (n : Int)) c ↦*{dq} vs : IProp GF) ⊢ typedPointsto l (array.mk (n : Int) vs) dq := by
  iintro H
  rw [ownSlice_unseal]; unfold ownSliceDef
  have : sint.Z (W64 (n : Int)) = (n : Int) := by
    simp only [sint.Z, W64, BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
  icases H with (%H | ⟨H, -⟩)
  · exact absurd (congrArg GoSlice.ptr H.1) hl
  · rw [this]
    iexact H

/-- `slice_of_array`, at an integer length. -/
theorem slice_of_array_int (l : Loc) (n : Int) (hn : 0 ≤ n ∧ n < 2 ^ 63) (vs : List V) (dq : DFrac)
    (c : w64) (hc : n ≤ sint.Z c) :
    typedPointsto (GF := GF) l (array.mk n vs) dq ⊢ slice.mk l (W64 n) c ↦*{dq} vs := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.1
  exact slice_of_array l k (by omega) vs dq c (by
    have : sint.Z (W64 (k : Int)) = (k : Int) := by
      simp only [sint.Z, W64, BitVec.toInt_ofInt]; apply Int.bmod_eq_of_le <;> omega
    omega)

/-- `array_of_slice`, at an integer length. -/
theorem array_of_slice_int (l : Loc) (n : Int) (hn : 0 ≤ n ∧ n < 2 ^ 63) (vs : List V) (dq : DFrac)
    (c : w64) (hl : l ≠ null) :
    (slice.mk l (W64 n) c ↦*{dq} vs : IProp GF) ⊢ typedPointsto l (array.mk n vs) dq := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.1
  exact array_of_slice l k (by omega) vs dq c hl

/-- Join an array split at `k` back together. -/
theorem array_join (l : Loc) (k : w64) (n : Int) (vs1 vs2 : List V) (dq : DFrac)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ n) (h1 : vs1.length = sint.nat k) :
    typedPointsto (GF := GF) l (array.mk (sint.Z k) vs1) dq ∗
      typedPointsto (arrayIndexRef V (sint.Z k) l) (array.mk (n - sint.Z k) vs2) dq ⊢
    typedPointsto l (array.mk n (vs1 ++ vs2)) dq := by
  have e := (array_split (V := V) (GF := GF) k l dq n (array.mk n (vs1 ++ vs2)) hk).2
  simp only [List.take_left' h1, List.drop_left' h1] at e
  exact e

end wps

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.sha1 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.sha1 :=
  build_get_is_pkg_init_wf

end defs

end crypto.sha1

end Perennial
