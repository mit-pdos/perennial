/-
The byte layout of Go values, for a byte-addressed memory (a map from `w64`
addresses to `w8` bytes). `ByteRepr V` gives the size, alignment and encoding
of the values of a Go type `V`, following Go's layout on amd64: little-endian
integers, and structs laid out field by field with each field at an offset
that is a multiple of its alignment.

`decode` is partial: a byte string that is not the layout of any value (a
bool byte other than 0 or 1) decodes to `none`, so the model is less defined
than Go there. It may accept several byte strings for one value, since padding
bytes are ignored; `encode` is the canonical encoding, with zero padding.
-/
module

public import Perennial.Std.Word
public import Perennial.Std.LittleEndian

@[expose] public section

namespace Perennial

/-- The byte representation of the values of a Go type (its memory layout). -/
class ByteRepr (V : Type) where
  size : Nat
  align : Nat
  encode : V → List w8
  decode : List w8 → Option V
  align_pos : 0 < align
  /-- Go's alignments are powers of two, and a type's size is a multiple of its
  alignment (so array elements stay aligned). -/
  align_pow2 : ∃ k, align = 2 ^ k
  align_dvd_size : align ∣ size
  length_encode : ∀ v, (encode v).length = size
  decode_encode : ∀ v, decode (encode v) = some v
  length_of_decode : ∀ bs v, decode bs = some v → bs.length = size

namespace ByteRepr

theorem decode_inj_of_eq {V : Type} [ByteRepr V] {bs : List w8} {v1 v2 : V}
    (h1 : decode bs = some v1) (h2 : decode bs = some v2) : v1 = v2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-! ## Machine words -/

/-- The `n`-byte little-endian encoding of a word. -/
def wordEncode (n : Nat) {m : Nat} (w : BitVec m) : List w8 :=
  LittleEndian.split n w.toNat

/-- Decode an `n`-byte little-endian word. -/
def wordDecode (n m : Nat) (bs : List w8) : Option (BitVec m) :=
  if bs.length = n then some (BitVec.ofNat m (LittleEndian.combine bs)) else none

theorem wordEncode_length (n : Nat) {m : Nat} (w : BitVec m) :
    (wordEncode n w).length = n :=
  LittleEndian.length_split n _

theorem wordDecode_encode (n : Nat) {m : Nat} (hm : m = n * 8) (w : BitVec m) :
    wordDecode n m (wordEncode n w) = some w := by
  simp only [wordDecode, wordEncode, LittleEndian.length_split, ite_true,
    LittleEndian.combine_split, ← hm, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp

theorem wordDecode_length (n m : Nat) (bs : List w8) (w : BitVec m)
    (h : wordDecode n m bs = some w) : bs.length = n := by
  unfold wordDecode at h; split at h
  · assumption
  · cases h

theorem wordDecode_iff (n : Nat) {m : Nat} (hm : m = n * 8) (bs : List w8) (w : BitVec m) :
    wordDecode n m bs = some w ↔ bs = wordEncode n w := by
  constructor
  · intro h
    have hlen := wordDecode_length n m bs w h
    unfold wordDecode at h
    simp only [hlen, ite_true, Option.some.injEq] at h
    subst h
    have hb := LittleEndian.combine_bound bs
    have : (BitVec.ofNat m (LittleEndian.combine bs)).toNat = LittleEndian.combine bs := by
      rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
      rw [hlen] at hb; rw [hm, Nat.mul_comm]; exact hb
    rw [wordEncode, this, LittleEndian.split_combine n bs hlen]
  · rintro rfl; exact wordDecode_encode n hm w

instance instW8 : ByteRepr w8 where
  size := 1
  align := 1
  encode := wordEncode 1
  decode := wordDecode 1 8
  align_pos := by decide
  align_pow2 := ⟨0, rfl⟩
  align_dvd_size := Nat.dvd_refl _
  length_encode := wordEncode_length 1
  decode_encode := wordDecode_encode 1 rfl
  length_of_decode := wordDecode_length 1 8

instance instW16 : ByteRepr w16 where
  size := 2
  align := 2
  encode := wordEncode 2
  decode := wordDecode 2 16
  align_pos := by decide
  align_pow2 := ⟨1, rfl⟩
  align_dvd_size := Nat.dvd_refl _
  length_encode := wordEncode_length 2
  decode_encode := wordDecode_encode 2 rfl
  length_of_decode := wordDecode_length 2 16

instance instW32 : ByteRepr w32 where
  size := 4
  align := 4
  encode := wordEncode 4
  decode := wordDecode 4 32
  align_pos := by decide
  align_pow2 := ⟨2, rfl⟩
  align_dvd_size := Nat.dvd_refl _
  length_encode := wordEncode_length 4
  decode_encode := wordDecode_encode 4 rfl
  length_of_decode := wordDecode_length 4 32

instance instW64 : ByteRepr w64 where
  size := 8
  align := 8
  encode := wordEncode 8
  decode := wordDecode 8 64
  align_pos := by decide
  align_pow2 := ⟨3, rfl⟩
  align_dvd_size := Nat.dvd_refl _
  length_encode := wordEncode_length 8
  decode_encode := wordDecode_encode 8 rfl
  length_of_decode := wordDecode_length 8 64

theorem w8_decode_iff_eq_encode (bs : List w8) (v : w8) :
    decode bs = some v ↔ bs = encode v := wordDecode_iff 1 rfl bs v

theorem w16_decode_iff_eq_encode (bs : List w8) (v : w16) :
    decode bs = some v ↔ bs = encode v := wordDecode_iff 2 rfl bs v

theorem w32_decode_iff_eq_encode (bs : List w8) (v : w32) :
    decode bs = some v ↔ bs = encode v := wordDecode_iff 4 rfl bs v

theorem w64_decode_iff_eq_encode (bs : List w8) (v : w64) :
    decode bs = some v ↔ bs = encode v := wordDecode_iff 8 rfl bs v

/-! ## Booleans -/

/-- A Go bool is one byte, 0 or 1. Any other byte is not a bool (Go leaves it
undefined), so it does not decode. -/
def boolDecode : List w8 → Option Bool
  | [b] => if b = 0 then some false else if b = 1 then some true else none
  | _ => none

instance instBool : ByteRepr Bool where
  size := 1
  align := 1
  encode b := [if b then 1 else 0]
  decode := boolDecode
  align_pos := by decide
  align_pow2 := ⟨0, rfl⟩
  align_dvd_size := Nat.dvd_refl _
  length_encode _ := rfl
  decode_encode b := by cases b <;> decide
  length_of_decode bs v h := by
    match bs, h with
    | [_], _ => rfl

theorem bool_decode_iff_eq_encode (bs : List w8) (v : Bool) :
    decode bs = some v ↔ bs = encode v := by
  constructor
  · intro h
    match bs, h with
    | [b], h =>
      change boolDecode [b] = some v at h
      simp only [boolDecode] at h
      change [b] = [if v then 1 else 0]
      split at h
      · subst_vars; cases h; rfl
      · split at h
        · subst_vars; cases h; rfl
        · cases h
  · rintro rfl; exact decode_encode v

/-! ## Headers of strings and slices (interface values: `Golang/Defn/StaticImage.lean`) -/

end ByteRepr

/-- A Go string: a pointer to its bytes and its length (16 bytes). -/
structure GoStrHdr where
  ptr : w64
  len : w64
deriving DecidableEq

/-- A Go slice: a pointer to the elements, its length and its capacity. -/
structure GoSliceHdr where
  ptr : w64
  len : w64
  cap : w64
deriving DecidableEq

namespace ByteRepr

/-- Decode two consecutive `w64`s. -/
def decodePair (bs : List w8) : Option (w64 × w64) :=
  match decode (V := w64) (bs.take 8), decode (V := w64) (bs.drop 8) with
  | some a, some b => some (a, b)
  | _, _ => none

theorem decodePair_iff (bs : List w8) (a b : w64) :
    decodePair bs = some (a, b) ↔ bs = encode a ++ encode b := by
  unfold decodePair
  constructor
  · intro h
    split at h
    · rename_i a' b' ha hb
      cases h
      rw [w64_decode_iff_eq_encode] at ha hb
      rw [← ha, ← hb, List.take_append_drop]
    · cases h
  · rintro rfl
    have hl : (encode a).length = 8 := length_encode a
    simp only [List.take_left' hl, List.drop_left' hl, decode_encode]

theorem decodePair_length (bs : List w8) (p : w64 × w64) (h : decodePair bs = some p) :
    bs.length = 16 := by
  obtain ⟨a, b⟩ := p
  rw [decodePair_iff] at h; subst h
  simp [length_encode]; rfl

instance instGoStrHdr : ByteRepr GoStrHdr where
  size := 16
  align := 8
  encode h := encode h.ptr ++ encode h.len
  decode bs := (decodePair bs).map fun p => ⟨p.1, p.2⟩
  align_pos := by decide
  align_pow2 := ⟨3, rfl⟩
  align_dvd_size := by decide
  length_encode h := by simp [length_encode]; rfl
  decode_encode h := by simp [(decodePair_iff _ h.ptr h.len).mpr rfl]
  length_of_decode bs v h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, _⟩ := h
    exact decodePair_length bs p hp

theorem goStrHdr_decode_iff_eq_encode (bs : List w8) (v : GoStrHdr) :
    decode bs = some v ↔ bs = encode v := by
  change (decodePair bs).map _ = some v ↔ bs = encode v.ptr ++ encode v.len
  rw [← decodePair_iff]
  obtain ⟨p, l⟩ := v
  constructor
  · intro h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, hp, he⟩ := h
    cases he; exact hp
  · intro h; simp [h]

/-- Decode a slice header: a `w64` followed by two more. -/
def sliceHdrDecode (bs : List w8) : Option GoSliceHdr :=
  match decode (V := w64) (bs.take 8), decodePair (bs.drop 8) with
  | some p, some (l, c) => some ⟨p, l, c⟩
  | _, _ => none

theorem sliceHdrDecode_iff (bs : List w8) (v : GoSliceHdr) :
    sliceHdrDecode bs = some v ↔ bs = encode v.ptr ++ encode v.len ++ encode v.cap := by
  unfold sliceHdrDecode
  rw [List.append_assoc]
  constructor
  · intro h
    split at h
    · rename_i p l c hp hlc
      cases h
      rw [w64_decode_iff_eq_encode] at hp
      rw [decodePair_iff] at hlc
      rw [← hp, ← hlc, List.take_append_drop]
    · cases h
  · rintro rfl
    have hl : (encode v.ptr).length = 8 := length_encode _
    simp only [List.take_left' hl, List.drop_left' hl, decode_encode,
      (decodePair_iff _ v.len v.cap).mpr rfl]

instance instGoSliceHdr : ByteRepr GoSliceHdr where
  size := 24
  align := 8
  encode h := encode h.ptr ++ encode h.len ++ encode h.cap
  decode := sliceHdrDecode
  align_pos := by decide
  align_pow2 := ⟨3, rfl⟩
  align_dvd_size := by decide
  length_encode h := by simp [length_encode]; rfl
  decode_encode h := (sliceHdrDecode_iff _ h).mpr rfl
  length_of_decode bs v h := by
    rw [sliceHdrDecode_iff] at h; subst h
    simp [length_encode]; rfl

theorem goSliceHdr_decode_iff_eq_encode (bs : List w8) (v : GoSliceHdr) :
    decode bs = some v ↔ bs = encode v :=
  sliceHdrDecode_iff bs v

/-! ## Structs

A struct with two fields `A` and `B` is laid out as Go does: the first field
at offset 0, the second at the first multiple of `align B` past the first, and
the total size rounded up to a multiple of the struct's alignment, the larger
of the fields' alignments. Larger structs nest pairs. -/

/-- The least multiple of `a` that is at least `n` (for `0 < a`). -/
def roundUp (n a : Nat) : Nat := (n + a - 1) / a * a

theorem le_roundUp (n a : Nat) (ha : 0 < a) : n ≤ roundUp n a := by
  unfold roundUp
  have h1 := Nat.div_add_mod (n + a - 1) a
  have h2 := Nat.mod_lt (n + a - 1) ha
  rw [Nat.mul_comm]
  omega

theorem roundUp_mod (n a : Nat) : roundUp n a % a = 0 := by
  unfold roundUp; exact Nat.mul_mod_left _ _

/-- The offset of the second field of a struct of an `A` and a `B`. -/
def fieldOffset2 (A B : Type) [ByteRepr A] [ByteRepr B] : Nat :=
  roundUp (size A) (align B)

/-- The padding byte Go adds after a zero-size last field of a non-zero-size
struct (`cmd/compile`'s `CalcStructSize`, Go issue 9401), so that the field's
address does not point to the next object. -/
def trailingPad (end_ lastSize : Nat) : Nat :=
  if lastSize = 0 ∧ 0 < end_ then 1 else 0

/-- The size of a struct of an `A` and a `B`, padding included. -/
def prodSize (A B : Type) [ByteRepr A] [ByteRepr B] : Nat :=
  roundUp (fieldOffset2 A B + size B + trailingPad (fieldOffset2 A B + size B) (size B))
    (max (align A) (align B))

section prod
variable {A B : Type} [ByteRepr A] [ByteRepr B]

theorem fieldOffset2_ge : size A ≤ fieldOffset2 A B :=
  le_roundUp _ _ (align_pos (V := B))

theorem fieldOffset2_mod : fieldOffset2 A B % align B = 0 := roundUp_mod _ _

theorem fieldOffset2_add_le : fieldOffset2 A B + size B ≤ prodSize A B :=
  Nat.le_trans (Nat.le_add_right _ _)
    (le_roundUp _ _ (Nat.lt_of_lt_of_le (align_pos (V := A)) (Nat.le_max_left _ _)))

/-- Decode a struct of an `A` and a `B`: the fields' bytes are at `[0, size A)`
and `[fieldOffset2, fieldOffset2 + size B)`; the padding is ignored. -/
def prodDecode (A B : Type) [ByteRepr A] [ByteRepr B] (bs : List w8) : Option (A × B) :=
  if bs.length = prodSize A B then
    match decode (V := A) (bs.take (size A)),
        decode (V := B) ((bs.drop (fieldOffset2 A B)).take (size B)) with
    | some x, some y => some (x, y)
    | _, _ => none
  else none

theorem prodDecode_iff (bs : List w8) (x : A) (y : B) :
    prodDecode A B bs = some (x, y) ↔
      bs.length = prodSize A B ∧ decode (bs.take (size A)) = some x ∧
        decode ((bs.drop (fieldOffset2 A B)).take (size B)) = some y := by
  unfold prodDecode
  constructor
  · intro h
    split at h
    · rename_i hlen
      split at h
      · rename_i x' y' hx hy
        cases h; exact ⟨hlen, hx, hy⟩
      · cases h
    · cases h
  · rintro ⟨hlen, hx, hy⟩
    simp [hlen, hx, hy]

/-- The layout of a Go struct with exactly two fields, `A` then `B` (Go's layout
of `struct { a A; b B }`). Nested pairs are **not** the layout of a struct with
more fields: Go lays fields out one after the other, aligning each, while an
inner pair is padded and aligned as a whole (`struct { a, b byte; c int64 }`
has size 16, `(byte × (byte × int64))` 24). Such structs need an n-ary layout. -/
instance instProd : ByteRepr (A × B) where
  size := prodSize A B
  align := max (align A) (align B)
  encode p := encode p.1 ++ List.replicate (fieldOffset2 A B - size A) 0 ++ encode p.2 ++
    List.replicate (prodSize A B - (fieldOffset2 A B + size B)) 0
  decode := prodDecode A B
  align_pos := Nat.lt_of_lt_of_le (align_pos (V := A)) (Nat.le_max_left _ _)
  align_pow2 := by
    rw [Nat.max_def]; split
    · exact align_pow2 (V := B)
    · exact align_pow2 (V := A)
  align_dvd_size := Nat.dvd_of_mod_eq_zero (roundUp_mod _ _)
  length_encode p := by
    have := fieldOffset2_ge (A := A) (B := B)
    have := fieldOffset2_add_le (A := A) (B := B)
    simp only [List.length_append, List.length_replicate, length_encode]
    omega
  decode_encode p := by
    obtain ⟨x, y⟩ := p
    have h1 := fieldOffset2_ge (A := A) (B := B)
    have h2 := fieldOffset2_add_le (A := A) (B := B)
    rw [prodDecode_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, length_encode]; omega
    · rw [List.append_assoc, List.append_assoc,
        List.take_left' (length_encode x), decode_encode]
    · have hl : (encode x ++ List.replicate (fieldOffset2 A B - size A) (0 : w8)).length =
          fieldOffset2 A B := by
        simp only [List.length_append, List.length_replicate, length_encode]; omega
      rw [List.append_assoc _ (encode y), List.drop_left' hl,
        List.take_left' (length_encode y), decode_encode]
  length_of_decode bs v h := by
    obtain ⟨x, y⟩ := v
    exact ((prodDecode_iff bs x y).mp h).1

theorem prod_size : size (A × B) = prodSize A B := rfl

theorem prod_align : align (A × B) = max (align A) (align B) := rfl

theorem prod_decode_iff (bs : List w8) (x : A) (y : B) :
    decode (V := A × B) bs = some (x, y) ↔
      bs.length = size (A × B) ∧ decode (bs.take (size A)) = some x ∧
        decode ((bs.drop (fieldOffset2 A B)).take (size B)) = some y :=
  prodDecode_iff bs x y

theorem prod_encode (x : A) (y : B) :
    encode (x, y) = encode x ++ List.replicate (fieldOffset2 A B - size A) 0 ++ encode y ++
      List.replicate (size (A × B) - (fieldOffset2 A B + size B)) 0 := rfl

theorem prod_fieldOffset2_ge : size A ≤ fieldOffset2 A B := fieldOffset2_ge

theorem prod_fieldOffset2_add_le : fieldOffset2 A B + size B ≤ size (A × B) :=
  fieldOffset2_add_le

theorem prod_fieldOffset2_mod : fieldOffset2 A B % align B = 0 := fieldOffset2_mod

end prod

end ByteRepr

end Perennial
