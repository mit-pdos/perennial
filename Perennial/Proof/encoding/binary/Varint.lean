/-
**The varint encoding of `encoding/binary`** (`varint.go`), the vocabulary of the specs of
`PutUvarint`, `PutVarint`, `ReadUvarint` and `ReadVarint`.

* `uvarintEnc n`: the bytes `PutUvarint` writes for `n`, 7 bits at a time, low group first, the
  high bit of each byte set on all but the last; `uvarintDec V`: the value of the 7-bit groups
  of `V`, low first. `uvarintDec (uvarintEnc n) = n` (`uvarintDec_enc`).
* `zigzag x`: the `uint64` `PutVarint` encodes for the `int64` `x`: `2x` for `x ≥ 0`, `-2x - 1`
  for `x < 0`.
* `uvarintOk V`: `V` is a varint `ReadUvarint` accepts: continuation bytes, then a last byte
  below `0x80`, at most ten bytes, the tenth at most `1`. Such a `V` comparable with the
  encoding of `n` (one a prefix of the other) is that encoding (`uvarintOk_eq_enc`): `ReadUvarint`
  accepts non-minimal encodings (`[0x80, 0x00]`), so this is how a client whose stream holds
  `uvarintEnc n` learns that it read exactly those bytes.
* `uvarintOverflow V`: the ten bytes after which `ReadUvarint` reports `errOverflow`: nine
  continuation bytes, then a tenth above `1`.
* `uvarintRes`: what `ReadUvarint` returns after reading `V` (see its definition).
-/
module

public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace encoding.binary

/-- The bytes `PutUvarint` writes for `n` (see the file header). -/
def uvarintEnc (n : Nat) : List w8 :=
  if n < 128 then [BitVec.ofNat 8 n]
  else BitVec.ofNat 8 (n % 128 + 128) :: uvarintEnc (n / 128)
termination_by n
decreasing_by omega

/-- The value of a little-endian base-128 byte list (each byte's low 7 bits). -/
def uvarintDec : List w8 → Nat
  | [] => 0
  | b :: bs => b.toNat % 128 + 128 * uvarintDec bs

/-- Every byte has the continuation bit. -/
def contBytes (V : List w8) : Prop := ∀ b ∈ V, 128 ≤ b.toNat

/-- A varint `ReadUvarint` accepts (see the file header). -/
def uvarintOk (V : List w8) : Prop :=
  ∃ V' c, V = V' ++ [c] ∧ contBytes V' ∧ c.toNat < 128 ∧ V'.length ≤ 9 ∧
    (V'.length = 9 → c.toNat ≤ 1)

/-- The bytes after which `ReadUvarint` reports `errOverflow`: nine continuation bytes, then a
tenth above `1` (`varint.go:142`, or a tenth continuation byte, `varint.go:150`). -/
def uvarintOverflow (V : List w8) : Prop :=
  ∃ V' c, V = V' ++ [c] ∧ V'.length = 9 ∧ contBytes V' ∧ 1 < c.toNat

/-- Go's zigzag (`PutVarint`: `ux := uint64(x) << 1; if x < 0 { ux = ^ux }`), on an `int64`
value `x`: `2x` for `x ≥ 0`, `-2x - 1` for `x < 0`. -/
def zigzag (x : Int) : Nat := if 0 ≤ x then (2 * x).toNat else (-2 * x - 1).toNat

theorem uvarintDec_append (V W : List w8) :
    uvarintDec (V ++ W) = uvarintDec V + 128 ^ V.length * uvarintDec W := by
  induction V with
  | nil => simp [uvarintDec]
  | cons b bs ih =>
    simp only [List.cons_append, uvarintDec, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 128 (128 ^ bs.length)]
    omega

theorem uvarintDec_lt (V : List w8) : uvarintDec V < 128 ^ V.length := by
  induction V with
  | nil => simp [uvarintDec]
  | cons b bs ih =>
    simp only [uvarintDec, List.length_cons, Nat.pow_succ]
    have : b.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    have h2 : 128 * uvarintDec bs + 128 ≤ 128 * 128 ^ bs.length := by
      have := Nat.mul_le_mul_left 128 (show uvarintDec bs + 1 ≤ 128 ^ bs.length by omega)
      rw [Nat.mul_add] at this; omega
    rw [Nat.mul_comm (128 ^ bs.length)]
    omega

/-- The shape of `uvarintEnc n`: continuation bytes holding `n`'s low groups, then the top
group. -/
theorem uvarintEnc_spec (n : Nat) : ∃ V' c, uvarintEnc n = V' ++ [c] ∧ contBytes V' ∧
    c.toNat < 128 ∧ c.toNat = n / 128 ^ V'.length ∧ (0 < V'.length → 128 ^ V'.length ≤ n) ∧
    uvarintDec V' = n % 128 ^ V'.length := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [uvarintEnc]
    by_cases h : n < 128
    · simp only [h, ↓reduceIte]
      refine ⟨[], BitVec.ofNat 8 n, rfl, by simp [contBytes], ?_, ?_, by simp,
        by simp [uvarintDec, Nat.mod_one]⟩
      · simp; omega
      · simp; omega
    · simp only [h, ↓reduceIte]
      obtain ⟨V', c, he, hc, hc1, hc2, hc3, hc4⟩ := ih (n / 128) (by omega)
      refine ⟨BitVec.ofNat 8 (n % 128 + 128) :: V', c, by rw [he]; rfl, ?_, hc1, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · simp; omega
        · exact hc _ hb
      · rw [hc2, List.length_cons, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · intro _
        simp only [List.length_cons, Nat.pow_succ]
        rcases Nat.eq_zero_or_pos V'.length with h0 | h0
        · rw [h0]; simp only [Nat.pow_zero, Nat.one_mul]; omega
        · have h3 := hc3 h0
          have h4 := Nat.div_mul_le_self n 128
          have h5 : 128 ^ V'.length * 128 ≤ n / 128 * 128 := Nat.mul_le_mul_right 128 h3
          omega
      · simp only [uvarintDec, List.length_cons, hc4]
        have h1 : (BitVec.ofNat 8 (n % 128 + 128)).toNat % 128 = n % 128 := by
          simp
        rw [h1, Nat.pow_succ, Nat.mul_comm (128 ^ V'.length) 128, Nat.mod_mul]

theorem uvarintDec_enc (n : Nat) : uvarintDec (uvarintEnc n) = n := by
  obtain ⟨V', c, he, -, hc1, hc2, -, hc4⟩ := uvarintEnc_spec n
  rw [he, uvarintDec_append, hc4]
  simp only [uvarintDec, Nat.mod_eq_of_lt hc1, Nat.mul_zero, Nat.add_zero]
  rw [hc2]
  exact Nat.mod_add_div n _

theorem uvarintEnc_inj {a b : Nat} (h : uvarintEnc a = uvarintEnc b) : a = b := by
  rw [← uvarintDec_enc a, ← uvarintDec_enc b, h]

/-- The encoding of a `uint64` is a varint `ReadUvarint` accepts: at most 10 bytes, the tenth at
most `1`. -/
theorem uvarintOk_enc (n : Nat) (hn : n < 2 ^ 64) : uvarintOk (uvarintEnc n) := by
  obtain ⟨V', c, he, hc, hc1, hc2, hc3, -⟩ := uvarintEnc_spec n
  have hl : V'.length ≤ 9 := by
    rcases Nat.lt_or_ge 9 V'.length with hlt | hlt
    · have h1 := hc3 (by omega)
      have h2 : 128 ^ 10 ≤ 128 ^ V'.length := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hlt
  refine ⟨V', c, he, hc, hc1, hl, fun h9 => ?_⟩
  rw [hc2, h9]
  have : n / 128 ^ 9 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  omega

/-- What `ReadUvarint` accepts decodes to a `uint64`. -/
theorem uvarintOk_dec_lt {V : List w8} (h : uvarintOk V) : uvarintDec V < 2 ^ 64 := by
  obtain ⟨V', c, rfl, -, hc, hl, h9⟩ := h
  rw [uvarintDec_append]
  simp only [uvarintDec, Nat.mul_zero, Nat.add_zero]
  have hd := uvarintDec_lt V'
  rcases Nat.lt_or_ge V'.length 9 with hlt | hge
  · have h1 : 128 ^ V'.length * 128 ≤ 128 ^ 9 := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 128 ^ V'.length * (c.toNat % 128) ≤ 128 ^ V'.length * 127 :=
      Nat.mul_le_mul_left _ (by omega)
    have : (128 : Nat) ^ 9 < 2 ^ 64 := by decide
    omega
  · have h9' := h9 (by omega)
    rw [show V'.length = 9 by omega] at hd ⊢
    have h2 : 128 ^ 9 * (c.toNat % 128) ≤ 128 ^ 9 * 1 := Nat.mul_le_mul_left _ (by omega)
    have : (128 : Nat) ^ 9 * 2 ≤ 2 ^ 64 := by decide
    omega

/-- **What `ReadUvarint` accepts, comparable with an encoding, is that encoding.** -/
theorem uvarintOk_eq_enc {V : List w8} (n : Nat) (hV : uvarintOk V)
    (h : V <+: uvarintEnc n ∨ uvarintEnc n <+: V) : V = uvarintEnc n := by
  have term : ∀ {A B : List w8}, (∃ A' a, A = A' ++ [a] ∧ a.toNat < 128) →
      (∃ B' b, B = B' ++ [b] ∧ contBytes B') → A <+: B → A = B := by
    intro A B hA hB h
    obtain ⟨C, rfl⟩ := h
    obtain ⟨A', a, rfl, ha⟩ := hA
    obtain ⟨B', b, he, hB'⟩ := hB
    by_cases hC : C = []
    · simp [hC]
    · exfalso
      have h1 : (A' ++ [a] ++ C).dropLast = B' := by
        rw [he]; exact List.dropLast_concat
      rw [List.dropLast_append_of_ne_nil hC] at h1
      have h2 : a ∈ B' := by rw [← h1]; simp
      have := hB' a h2
      omega
  obtain ⟨V', c, hVe, hVc, hc, -⟩ := hV
  obtain ⟨E', e, hEe, hEc, he, -⟩ := uvarintEnc_spec n
  rcases h with h | h
  · exact term ⟨V', c, hVe, hc⟩ ⟨E', e, hEe, hEc⟩ h
  · exact (term ⟨E', e, hEe, he⟩ ⟨V', c, hVe, hVc⟩ h).symm

theorem uvarintDec_snoc (V : List w8) (c : w8) :
    uvarintDec (V ++ [c]) = uvarintDec V + c.toNat % 128 * 2 ^ (7 * V.length) := by
  rw [uvarintDec_append]
  simp only [uvarintDec, Nat.mul_zero, Nat.add_zero, Nat.pow_mul]
  rw [Nat.mul_comm]

theorem w64_or_shl (d b k : Nat) (hd : d < 2 ^ k) (hk : k < 64) (hs : d + b * 2 ^ k < 2 ^ 64) :
    W64 (d : Int) ||| W64 (b : Int) <<< W64 (k : Int) = W64 ((d + b * 2 ^ k : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hb : b ≤ b * 2 ^ k := Nat.le_mul_of_pos_right b h1
  simp only [W64, BitVec.ofInt_natCast, BitVec.toNat_or, BitVec.shiftLeft_eq',
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have hk' : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [hk', Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : b * 2 ^ k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : d + b * 2 ^ k < 2 ^ 64), Nat.mul_comm b, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hd, Nat.add_comm]

theorem or128 (a : Nat) (h : a < 256) : a ||| 128 = a % 128 + 128 := by
  have hr : a % 128 < 2 ^ 7 := Nat.mod_lt _ (by decide)
  have e : 2 ^ 7 * 1 + a % 128 = 2 ^ 7 * 1 ||| a % 128 := Nat.two_pow_add_eq_or_of_lt hr 1
  rw [show (2 : Nat) ^ 7 * 1 = 128 from rfl] at e
  rcases Nat.lt_or_ge a 128 with h1 | h1
  · have ha : a % 128 = a := Nat.mod_eq_of_lt h1
    rw [ha] at e ⊢
    rw [Nat.or_comm]; omega
  · have ha : a = 128 + a % 128 := by omega
    conv => lhs; rw [ha]
    rw [e, Nat.or_comm (128 ||| _), ← Nat.or_assoc, Nat.or_self, ← e]
    omega

theorem byte_or_128 (xv : w64) :
    (W8 (uint.Z xv) ||| W8 128) = BitVec.ofNat 8 (xv.toNat % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (W8 (uint.Z xv)).toNat = xv.toNat % 256 := by
    simp [W8, uint.Z]
  have h2 : (W8 128).toNat = 128 := rfl
  rw [BitVec.toNat_or, h1, h2, or128 _ (by omega), BitVec.toNat_ofNat]
  omega

theorem uvarintEnc_step (xv : w64) (h : 128 ≤ uint.nat xv) :
    uvarintEnc (uint.nat xv) =
      BitVec.ofNat 8 (xv.toNat % 128 + 128) :: uvarintEnc (uint.nat (xv >>> W64 7)) := by
  rw [uvarintEnc]
  simp only [show ¬ uint.nat xv < 128 by omega, ↓reduceIte]
  congr 2
  simp [uint.nat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem uvarintEnc_last (xv : w64) (h : uint.nat xv < 128) :
    uvarintEnc (uint.nat xv) = [W8 (uint.Z xv)] := by
  rw [uvarintEnc]
  simp only [h, ↓reduceIte]
  simp [W8, uint.Z, uint.nat]

theorem pow128 (n : Nat) : 128 ^ n = 2 ^ (7 * n) := by
  rw [Nat.pow_mul]

/-- `ReadUvarint`'s last byte: `x | uint64(b) << s` (`varint.go:145`). -/
theorem uvarint_last_val (V : List w8) (c : w8) (hc : c.toNat < 128) (hl : V.length ≤ 9)
    (h9 : V.length = 9 → c.toNat ≤ 1) :
    uint.nat (W64 (uvarintDec V : Int) ||| W64 (uint.Z c) <<< W64 (7 * (V.length : Int))) =
      uvarintDec (V ++ [c]) := by
  have h2 : 7 * (V.length : Int) = ((7 * V.length : Nat) : Int) := by push_cast; rfl
  rw [h2, show uint.Z c = ((c.toNat : Nat) : Int) from rfl]
  have hd := uvarintDec_lt V
  rw [pow128] at hd
  have hs : uvarintDec V + c.toNat * 2 ^ (7 * V.length) < 2 ^ 64 := by
    rcases Nat.lt_or_ge V.length 9 with hlt | hge
    · have h1 : 2 ^ (7 * V.length) * 128 ≤ 2 ^ 63 := by
        rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      have : c.toNat * 2 ^ (7 * V.length) ≤ 127 * 2 ^ (7 * V.length) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · have h9' := h9 (by omega)
      rw [show 7 * V.length = 63 by omega] at hd ⊢
      have : c.toNat * 2 ^ 63 ≤ 1 * 2 ^ 63 := Nat.mul_le_mul_right _ h9'
      omega
  rw [w64_or_shl _ _ _ hd (by omega) hs, uvarintDec_snoc, Nat.mod_eq_of_lt hc]
  simp only [uint.nat, W64, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hs

/-- `ReadUvarint`'s step on a continuation byte: `x |= uint64(b&0x7f) << s` (`varint.go:147`). -/
theorem uvarint_acc (V : List w8) (c : w8) (hl : V.length + 1 ≤ 9) :
    W64 (uvarintDec V : Int) ||| W64 (uint.Z (c &&& W8 127)) <<< W64 (7 * (V.length : Int)) =
      W64 (uvarintDec (V ++ [c]) : Int) := by
  have h1 : uint.Z (c &&& W8 127) = ((c.toNat % 128 : Nat) : Int) := by
    simp only [uint.Z, W8]
    congr 1
    have : (c &&& BitVec.ofInt 8 127) = c &&& 127#8 := rfl
    rw [this, BitVec.toNat_and]
    show c.toNat &&& 127 = c.toNat % 128
    exact Nat.and_two_pow_sub_one_eq_mod c.toNat 7
  have h2 : 7 * (V.length : Int) = ((7 * V.length : Nat) : Int) := by push_cast; rfl
  rw [h1, h2, uvarintDec_snoc]
  have hd := uvarintDec_lt V
  rw [pow128] at hd
  have hc : c.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  have h3 : 2 ^ (7 * V.length) * 128 ≤ 2 ^ 63 := by
    rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply w64_or_shl _ _ _ hd (by omega)
  have : c.toNat % 128 * 2 ^ (7 * V.length) ≤ 127 * 2 ^ (7 * V.length) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- `PutVarint`'s `ux` is the zigzag of `x`. -/
theorem zigzag_go (x : w64) :
    uint.nat (if sint.Z x < 0 then ~~~ (x <<< W64 1) else x <<< W64 1) = zigzag (sint.Z x) := by
  unfold zigzag
  have h1 : (W64 1 : w64).toNat = 1 := rfl
  by_cases hx : sint.Z x < 0
  · simp only [hx, ↓reduceIte, show ¬ (0 ≤ sint.Z x) by omega]
    simp only [uint.nat, sint.Z] at hx ⊢
    rw [BitVec.toNat_not, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    rw [BitVec.toInt_eq_toNat_cond] at hx ⊢
    have := x.isLt
    split at hx <;> rename_i hc
    · omega
    · simp only [hc, ↓reduceIte]
      omega
  · simp only [hx, ↓reduceIte, show 0 ≤ sint.Z x by omega]
    simp only [uint.nat, sint.Z] at hx ⊢
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    rw [BitVec.toInt_eq_toNat_cond] at hx ⊢
    have := x.isLt
    split at hx <;> rename_i hc
    · simp only [hc, ↓reduceIte]
      omega
    · omega

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **What `ReadUvarint` returns after reading `V`** from a byte reader that had delivered `r`,
with the reader's errors' evidence `E` (`io.byteReaderOk`), `eof`, `ueof` and `ovf` the values
of `io.EOF`, `io.ErrUnexpectedEOF` and `errOverflow`: a varint it accepts, its value `x` and
`nil`; or ten bytes that overflow and `errOverflow`; or fewer than ten continuation bytes
and the reader's error `e` (with its evidence `E (r ++ V) e`), but `ErrUnexpectedEOF` in place of
`EOF` when some bytes came first. -/
def uvarintRes (E : List w8 → GoInterface → IProp GF) (eof ueof ovf : GoInterface)
    (r V : List w8) (x : w64) (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil ∧ uvarintOk V ∧ uint.nat x = uvarintDec V⌝ ∨
    ⌜err = ovf ∧ uvarintOverflow V⌝ ∨
    ∃ e : GoInterface, ⌜V.length < 10 ∧ contBytes V ∧ e ≠ interface.nil ∧
      (e = eof ∧ V ≠ [] → err = ueof) ∧ (¬ (e = eof ∧ V ≠ []) → err = e)⌝ ∗ □ E (r ++ V) e)

instance uvarintRes_persistent (E : List w8 → GoInterface → IProp GF)
    (eof ueof ovf : GoInterface) (r V : List w8) (x : w64) (err : GoInterface) :
    Persistent (uvarintRes E eof ueof ovf r V x err) := by
  unfold uvarintRes; infer_instance

end res

end encoding.binary

end Perennial
