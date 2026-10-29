/-
Byte views of plain values, for proofs about `unsafe` views over byte memory
(`docs/design/unsafe-memory.md`, sections 3 and 9).

A plain value is only bytes: `ByteEncoding V n` gives the `n` bytes of a value of the Lean
representation `V` and decodes any `n` bytes back to one, and `BytesView V` says that the typed
points-to of `V` at a positive address is the byte points-to of its encoding. With them, the bytes
of a `[]byte` (or of any slice of plain elements) are viewed at an offset as a typed points-to of
another plain type, which the generated machinery (`wp_load`, field loads and stores, whole-struct
stores) then uses, and the view is given back as bytes:

* `typedPointsto_zero_byte_array`, `typedPointsto_byte_array`, `typedPointsto_zero_array_bytes`,
  `ownSlice_bytes_acc`: an array or slice of plain elements as the bytes of its elements (the
  bytes of `make([]T, n)` are where a proof starts);
* `bytesPointsto_view` / `bytesPointsto_view_at`: the bytes from `l`, viewed at offset `k` as a
  `V`, at the program's address `l'` for it (`sliceIndexRef_byte_W64`, `sliceIndexRef_plain`,
  ...); storing `v` through the view leaves `replaceBytes bs k (encode v)`;
* `bytesPointsto_view_read`: the same for reading only, giving the bytes back unchanged;
* `ownSlice_byte_view`, `ownSlice_plain_view`: views straight from a slice points-to.

Views of disjoint byte ranges can be open at once after splitting the bytes with
`bytesPointsto_app`; overlapping views are opened one after the other. `replaceBytes_single`,
`replaceBytes_flatMap_set` and `flatMap_encode_take_drop` relate stores and loads of whole
elements to the bytes.

Encodings and views of the scalars are here; a plain struct's encoding is the concatenation of its
fields' (`ByteEncoding.prod`, `ByteEncoding.ofEquiv`), and its view (`BytesView`) is proved from
the struct's field offsets (`structFieldRef_offset`) with `bytesView_field`,
`bytesView_last_field` and `bytesView_of_def`; `go.PlainLayout.struct'` and
`go.PlainFields.cons_` are the layout rules in a form for `apply` (the tactics
`solve_plain_struct_layout` and `solve_plain_field_offset` of the `unsafememory` example's
`Layout.lean`, which does all of this for its types, use them).
-/
module

public import Perennial.Golang.Theory.Bytes
public import Perennial.Golang.Theory.Slice

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

/-! ## Little-endian bytes of numbers -/

section nat_bytes
variable [GooseExts]

theorem bytesNat_lt (bs : List w8) : bytesNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bytesNat]
  | cons b bs ih =>
    simp only [bytesNat, List.length_cons, Nat.pow_succ]
    have := b.isLt
    simp only [show (2 : Nat) ^ 8 = 256 from rfl] at this
    omega

/-- Any list of bytes is the `natBytes` of the number it encodes. -/
theorem natBytes_bytesNat (bs : List w8) : natBytes bs.length (bytesNat bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, natBytes, bytesNat]
    have hb := b.isLt
    simp only [show (2 : Nat) ^ 8 = 256 from rfl] at hb
    rw [show (b.toNat + 256 * bytesNat bs) / 256 = bytesNat bs by omega, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 8 = 256 from rfl]
    omega

theorem natBytes_bytesNat_of_length (w : Nat) (bs : List w8) (h : bs.length = w) :
    natBytes w (bytesNat bs) = bs := h ▸ natBytes_bytesNat bs

/-- Any `w` bytes are the bytes of the `8 * w`-bit word they encode. -/
theorem natBytes_ofNat_bytesNat (w : Nat) (bs : List w8) (h : bs.length = w) :
    natBytes w (BitVec.ofNat (8 * w) (bytesNat bs)).toNat = bs := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, natBytes_bytesNat_of_length w bs h]
  have := bytesNat_lt bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

theorem natBytes_append (w w' m : Nat) :
    natBytes (w + w') m = natBytes w m ++ natBytes w' (m / 256 ^ w) := by
  induction w generalizing m with
  | zero => simp [natBytes]
  | succ w ih =>
    rw [show w + 1 + w' = (w + w') + 1 by omega]
    simp only [natBytes, ih, List.cons_append, Nat.div_div_eq_div_mul, Nat.pow_succ]
    rw [Nat.mul_comm 256 (256 ^ w)]

end nat_bytes

/-! ## Byte encodings -/

/-- `ByteEncoding V n`: a value of the Lean representation `V` of a plain type is `n` bytes, and
any `n` bytes decode to one. -/
class ByteEncoding (V : Type) (n : outParam Nat) where
  encode : V → List w8
  decode : List w8 → V
  encode_length : ∀ v, (encode v).length = n
  decode_encode : ∀ v, decode (encode v) = v
  encode_decode : ∀ bs, bs.length = n → encode (decode bs) = bs

export ByteEncoding (encode decode)

namespace ByteEncoding

attribute [simp] encode_length decode_encode

theorem encode_ne_nil {V : Type} {n : Nat} [ByteEncoding V n] (v : V) (h : 0 < n) :
    encode v ≠ [] := by
  intro he; have := encode_length v; rw [he] at this; simp at this; omega

theorem encode_inj {V : Type} {n : Nat} [ByteEncoding V n] {v w : V}
    (h : encode v = encode w) : v = w := by
  rw [← decode_encode v, h, decode_encode]

/-- The bytes of a pair: the first component's, then the second's. -/
instance prod {A B : Type} {n m : Nat} [ByteEncoding A n] [ByteEncoding B m] :
    ByteEncoding (A × B) (n + m) where
  encode p := encode p.1 ++ encode p.2
  decode bs := (decode (bs.take n), decode (bs.drop n))
  encode_length p := by simp
  decode_encode p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    constructor
    · rw [List.take_left' (encode_length a), decode_encode]
    · rw [List.drop_left' (encode_length a), decode_encode]
  encode_decode bs h := by
    simp only
    rw [encode_decode _ (by simp; omega), encode_decode _ (by simp; omega), List.take_append_drop]

/-- The encoding of `V` through a bijection with `W` (a struct through the tuple of its
fields). -/
@[reducible] def ofEquiv {V W : Type} {n : Nat} [ByteEncoding W n] (f : V → W) (g : W → V)
    (gf : ∀ v, g (f v) = v) (fg : ∀ w, f (g w) = w) : ByteEncoding V n where
  encode v := encode (f v)
  decode bs := g (decode bs)
  encode_length v := encode_length (f v)
  decode_encode v := by simp [gf]
  encode_decode bs h := by simp only [fg]; exact encode_decode bs h

theorem prod_encode {A B : Type} {n m : Nat} [ByteEncoding A n] [ByteEncoding B m] (a : A)
    (b : B) : encode (a, b) = encode a ++ encode b := rfl

theorem prod_decode {A B : Type} {n m : Nat} [ByteEncoding A n] [ByteEncoding B m]
    (bs : List w8) : (decode bs : A × B) = (decode (bs.take n), decode (bs.drop n)) := rfl

end ByteEncoding

section scalar_encodings
variable [GooseExts]

/-- A byte is itself. -/
instance byteEncoding_w8 : ByteEncoding w8 1 where
  encode b := [b]
  decode bs := bs.headD 0
  encode_length _ := rfl
  decode_encode _ := rfl
  encode_decode bs h := by
    match bs, h with
    | [b], _ => rfl

/-- An `8 * w`-bit word is its `w` little-endian bytes. -/
@[reducible] def bitVecEncoding (w : Nat) : ByteEncoding (BitVec (8 * w)) w where
  encode v := natBytes w v.toNat
  decode bs := BitVec.ofNat (8 * w) (bytesNat bs)
  encode_length v := natBytes_length w _
  decode_encode v := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat (8 * w) (bytesNat (natBytes w v.toNat))).toNat = v.toNat
    rw [BitVec.toNat_ofNat, bytesNat_natBytes, show (256 : Nat) ^ w = 2 ^ (8 * w) by
      rw [Nat.pow_mul], Nat.mod_mod, Nat.mod_eq_of_lt v.isLt]
  encode_decode bs h := natBytes_ofNat_bytesNat w bs h

instance byteEncoding_w16 : ByteEncoding w16 2 := bitVecEncoding 2
instance byteEncoding_w32 : ByteEncoding w32 4 := bitVecEncoding 4
instance byteEncoding_w64 : ByteEncoding w64 8 := bitVecEncoding 8

theorem encode_w8 (b : w8) : encode b = [b] := rfl
theorem encode_w16 (v : w16) : encode v = natBytes 2 v.toNat := rfl
theorem encode_w32 (v : w32) : encode v = natBytes 4 v.toNat := rfl
theorem encode_w64 (v : w64) : encode v = natBytes 8 v.toNat := rfl
theorem decode_w8 (bs : List w8) : (decode bs : w8) = bs.headD 0 := rfl
theorem decode_w16 (bs : List w8) : (decode bs : w16) = BitVec.ofNat 16 (bytesNat bs) := rfl
theorem decode_w32 (bs : List w8) : (decode bs : w32) = BitVec.ofNat 32 (bytesNat bs) := rfl
theorem decode_w64 (bs : List w8) : (decode bs : w64) = BitVec.ofNat 64 (bytesNat bs) := rfl

/-- The bytes of a list of bytes are the list. -/
@[simp] theorem flatMap_encode_w8 (bs : List w8) : bs.flatMap encode = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, encode_w8, ih]

end scalar_encodings

/-! ## Replacing bytes at an offset -/

section replace
variable [GooseExts]

/-- `bs` with the bytes from offset `k` on replaced by `new`. -/
def replaceBytes (bs : List w8) (k : Nat) (new : List w8) : List w8 :=
  bs.take k ++ new ++ bs.drop (k + new.length)

theorem replaceBytes_length (bs : List w8) (k : Nat) (new : List w8)
    (h : k + new.length ≤ bs.length) : (replaceBytes bs k new).length = bs.length := by
  simp [replaceBytes]; omega

/-- Replacing bytes by the bytes already there changes nothing. -/
theorem replaceBytes_self (bs : List w8) (k n : Nat) :
    replaceBytes bs k ((bs.drop k).take n) = bs := by
  unfold replaceBytes
  by_cases h : k + n ≤ bs.length
  · have hl : ((bs.drop k).take n).length = n := by simp; omega
    rw [hl, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  · have e : bs.drop (k + (bs.drop k).length) = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [List.take_of_length_le (l := bs.drop k) (by simp; omega), e, List.append_nil,
      List.take_append_drop]

/-- Replacing one byte is `List.set`. -/
theorem replaceBytes_single (bs : List w8) (k : Nat) (b : w8) (hk : k < bs.length) :
    replaceBytes bs k [b] = bs.set k b := by
  unfold replaceBytes
  rw [List.set_eq_take_append_cons_drop]; simp [hk]

theorem replaceBytes_drop_take (bs : List w8) (k : Nat) (new : List w8)
    (h : k + new.length ≤ bs.length) :
    ((replaceBytes bs k new).drop k).take new.length = new := by
  unfold replaceBytes
  rw [List.append_assoc, List.drop_left' (by simp; omega), List.take_left' rfl]

theorem replaceBytes_append_left (a bs : List w8) (k : Nat) (new : List w8) :
    replaceBytes (a ++ bs) (a.length + k) new = a ++ replaceBytes bs k new := by
  unfold replaceBytes
  rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
    show a.length + k + new.length = a.length + (k + new.length) by omega,
    List.drop_append, List.drop_of_length_le (l := a) (by omega), Nat.add_sub_cancel_left]
  simp

/-- Replacing the bytes of element `i` of the bytes of a list is `List.set`. -/
theorem replaceBytes_flatMap_set {V : Type} {n : Nat} [ByteEncoding V n] (vs : List V) (i : Nat)
    (v : V) (hi : i < vs.length) :
    replaceBytes (vs.flatMap encode) (i * n) (encode v) = (vs.set i v).flatMap encode := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp [replaceBytes, List.flatMap_cons, List.drop_left' (ByteEncoding.encode_length x)]
    | succ i =>
      simp only [List.flatMap_cons, List.set_cons_succ]
      rw [show (i + 1) * n = (encode x).length + i * n by simp [Nat.succ_mul]; omega,
        replaceBytes_append_left, ih i (by simpa using hi)]

omit [GooseExts] in
/-- The bytes of element `i` of the bytes of a list. -/
theorem flatMap_encode_take_drop {V : Type} {n : Nat} [ByteEncoding V n] (vs : List V) (i : Nat)
    (hi : i < vs.length) : ((vs.flatMap encode).drop (i * n)).take n = encode vs[i] := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.flatMap_cons, List.take_left' (ByteEncoding.encode_length x)]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [show (i + 1) * n = (encode x).length + i * n by simp [Nat.succ_mul]; omega,
        List.drop_append, List.drop_of_length_le (by omega), Nat.add_sub_cancel_left,
        List.nil_append, ih i (by simpa using hi)]

end replace

/-! ## Byte views of typed points-tos -/

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
open ProofMode

/-- `BytesView V`: the typed points-to of `V` at a positive address is the byte points-to of the
value's encoding. -/
class BytesView (V : Type) {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V] : Prop where
  typedPointsto_bytes : ∀ (l : Loc) (v : V) (dq : DFrac), 0 < l.addr →
    typedPointsto (GF := GF) l v dq ⊣⊢ bytesPointsto l dq (encode v)

/-- `BytesView.typedPointsto_bytes`, with its instances found from `V`. -/
theorem typedPointsto_bytes {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [h : BytesView (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) (hl : 0 < l.addr) :
    typedPointsto (GF := GF) l v dq ⊣⊢ bytesPointsto l dq (encode v) :=
  h.typedPointsto_bytes l v dq hl

theorem bytesPointsto_one (l : Loc) (dq : DFrac) (b : w8) :
    bytesPointsto (GF := GF) l dq [b] ⊣⊢ heapPointsto l dq (LitV (LitByte b)) := by
  unfold bytesPointsto bytesPointsto
  exact ⟨by iintro ⟨H, _⟩; iexact H, by iintro H; iframe H⟩

instance bytesView_w8 : BytesView (GF := GF) w8 where
  typedPointsto_bytes l b dq _ := by
    rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    simp only [typedPointstoDef_heap, go.intoVal_unfold w8, encode_w8]
    unfold bytesPointsto bytesPointsto
    constructor
    · iintro ⟨H, _⟩; iframe H
    · iintro ⟨H, _⟩
      icases heapPointsto_non_null l dq _ $$ H with %Hnn
      iframe H; ipureintro; exact Hnn

/-- The view of the integer and float words: `typedPointstoDef_bytes` and non-nullness. -/
theorem bytesView_bitVec (w : Nat) (hw : 0 < w) (l : Loc) (v : BitVec (8 * w)) (dq : DFrac) :
    @typedPointsto GF _ (bytesTypedPointsto w) l v dq ⊣⊢
      bytesPointsto l dq (natBytes w v.toNat) := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  rw [typedPointstoDef_bytes]
  constructor
  · iintro ⟨H, _⟩; iexact H
  · iintro H
    icases bytesPointsto_non_null l dq _
      (by intro h; have := natBytes_length w v.toNat; rw [h] at this; simp at this; omega) $$ H
      with ⟨H, %Hnn⟩
    iframe H; ipureintro; exact Hnn

instance bytesView_w16 : BytesView (GF := GF) w16 where
  typedPointsto_bytes l v dq _ := bytesView_bitVec 2 (by decide) l v dq
instance bytesView_w32 : BytesView (GF := GF) w32 where
  typedPointsto_bytes l v dq _ := bytesView_bitVec 4 (by decide) l v dq
instance bytesView_w64 : BytesView (GF := GF) w64 where
  typedPointsto_bytes l v dq _ := bytesView_bitVec 8 (by decide) l v dq

/-- `PointstoPos V`: a typed points-to of `V` is at a positive address. The scalars have it (their
points-to is heap points-tos); a struct's need not, since its field addresses are concrete only at
positive addresses. -/
class PointstoPos (V : Type) [TypedPointsto (GF := GF) V] : Prop where
  typedPointsto_pos : ∀ (l : Loc) (v : V) (dq : DFrac), typedPointsto (GF := GF) l v dq ⊢ ⌜0 < l.addr⌝

export PointstoPos (typedPointsto_pos)

instance pointstoPos_w8 : PointstoPos (GF := GF) w8 where
  typedPointsto_pos l b dq := by
    rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    simp only [typedPointstoDef_heap]
    iintro ⟨H, _⟩
    iapply heapPointsto_pos l dq _ $$ H

theorem pointstoPos_bitVec (w : Nat) (hw : 0 < w) (l : Loc) (v : BitVec (8 * w)) (dq : DFrac) :
    @typedPointsto GF _ (bytesTypedPointsto w) l v dq ⊢ ⌜0 < l.addr⌝ :=
  (bytesView_bitVec w hw l v dq).1.trans (bytesPointsto_pos l dq _
    (by intro h; have := natBytes_length w v.toNat; rw [h] at this; simp at this; omega))

instance pointstoPos_w16 : PointstoPos (GF := GF) w16 := ⟨pointstoPos_bitVec 2 (by decide)⟩
instance pointstoPos_w32 : PointstoPos (GF := GF) w32 := ⟨pointstoPos_bitVec 4 (by decide)⟩
instance pointstoPos_w64 : PointstoPos (GF := GF) w64 := ⟨pointstoPos_bitVec 8 (by decide)⟩

/-- Bytes of the right length decode to a value whose typed points-to they are. -/
theorem bytesPointsto_typed {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (l : Loc) (dq : DFrac) (bs : List w8) (h : bs.length = n)
    (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq bs ⊣⊢ typedPointsto l (decode bs : V) dq := by
  have := typedPointsto_bytes (GF := GF) (V := V) l (decode bs) dq hl
  rw [ByteEncoding.encode_decode bs h] at this
  exact ⟨this.2, this.1⟩

/-- Rewrite the bytes of a byte points-to by an equal list (e.g. a computed literal). -/
theorem bytesPointsto_congr (l : Loc) (dq : DFrac) (bs bs' : List w8) (h : bs = bs') :
    bytesPointsto (GF := GF) l dq bs ⊢ bytesPointsto l dq bs' := h ▸ .rfl

/-- The bytes of `replaceBytes bs k new`, in three parts. -/
theorem bytesPointsto_replaceBytes (l : Loc) (dq : DFrac) (bs : List w8) (k : Nat)
    (new : List w8) (hk : k ≤ bs.length) :
    bytesPointsto (GF := GF) l dq (replaceBytes bs k new) ⊣⊢
      bytesPointsto l dq (bs.take k) ∗ bytesPointsto (l +ₗ (k : Int)) dq new ∗
        bytesPointsto (l +ₗ ((k + new.length : Nat) : Int)) dq (bs.drop (k + new.length)) := by
  unfold replaceBytes
  have hlen : (bs.take k).length = k := by simp; omega
  have h1 := bytesPointsto_app (GF := GF) l dq (bs.take k) (new ++ bs.drop (k + new.length))
  have h2 := bytesPointsto_app (GF := GF) (l +ₗ (k : Int)) dq new (bs.drop (k + new.length))
  rw [hlen] at h1
  rw [loc_add_assoc, show ((k : Int) + (new.length : Int)) = ((k + new.length : Nat) : Int) by
    omega] at h2
  rw [List.append_assoc]
  refine h1.trans ⟨?_, ?_⟩
  · iintro ⟨H1, H2⟩
    icases h2.1 $$ H2 with ⟨H2, H3⟩
    iframe
  · iintro ⟨H1, H2, H3⟩
    iframe H1
    iapply h2.2
    iframe

/-- The view at offset `k` of the bytes from `l` as a `V`: the bytes there decode to a value, and
storing any value through the view leaves its encoding in the bytes. -/
theorem bytesPointsto_view {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (l : Loc) (dq : DFrac) (bs : List w8) (k : Nat)
    (h : k + n ≤ bs.length) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq bs ⊢
      typedPointsto (l +ₗ (k : Int)) (decode ((bs.drop k).take n) : V) dq ∗
        ∀ v : V, typedPointsto (l +ₗ (k : Int)) v dq -∗
          bytesPointsto l dq (replaceBytes bs k (encode v)) := by
  have hmid : ((bs.drop k).take n).length = n := by simp; omega
  have hlk : 0 < (l +ₗ (k : Int)).addr := by simp [Loc.add]; omega
  have hsplit := bytesPointsto_replaceBytes (GF := GF) l dq bs k ((bs.drop k).take n) (by omega)
  rw [replaceBytes_self, hmid] at hsplit
  iintro Hb
  icases hsplit.1 $$ Hb with ⟨Hpre, Hv, Hpost⟩
  icases (bytesPointsto_typed (V := V) (l +ₗ (k : Int)) dq _ hmid hlk).1 $$ Hv with Hv
  iframe Hv
  iintro %v Hv
  icases (typedPointsto_bytes (l +ₗ (k : Int)) v dq hlk).1 $$ Hv with Hv
  iapply (bytesPointsto_replaceBytes l dq bs k (encode v) (by omega)).2
  rw [ByteEncoding.encode_length]
  iframe

/-- `bytesPointsto_view` at an address `l'` given as `l +ₗ k` (for instance an element address
of the program, `sliceIndexRef w8 i s`). -/
theorem bytesPointsto_view_at {V : Type} {n : Nat} [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (l : Loc) (dq : DFrac) (bs : List w8)
    (k : Nat) (l' : Loc) (hl' : l' = l +ₗ (k : Int)) (h : k + n ≤ bs.length) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq bs ⊢
      typedPointsto l' (decode ((bs.drop k).take n) : V) dq ∗
        ∀ v : V, typedPointsto l' v dq -∗ bytesPointsto l dq (replaceBytes bs k (encode v)) :=
  hl' ▸ bytesPointsto_view l dq bs k h hl

/-- A view for reading: the typed points-to gives the bytes back unchanged. -/
theorem bytesPointsto_view_read {V : Type} {n : Nat} [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (l : Loc) (dq : DFrac) (bs : List w8)
    (k : Nat) (l' : Loc) (hl' : l' = l +ₗ (k : Int)) (h : k + n ≤ bs.length) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq bs ⊢
      typedPointsto l' (decode ((bs.drop k).take n) : V) dq ∗
        (typedPointsto l' (decode ((bs.drop k).take n) : V) dq -∗ bytesPointsto l dq bs) := by
  have hmid : ((bs.drop k).take n).length = n := by simp; omega
  iintro Hb
  icases bytesPointsto_view_at (V := V) l dq bs k l' hl' h hl $$ Hb with ⟨Hv, Hb⟩
  iframe Hv
  iintro Hv
  have e : replaceBytes bs k (encode (decode ((bs.drop k).take n) : V)) = bs := by
    rw [ByteEncoding.encode_decode _ hmid, replaceBytes_self]
  iapply (show bytesPointsto (GF := GF) l dq (replaceBytes bs k
      (encode (decode ((bs.drop k).take n) : V))) ⊢ bytesPointsto l dq bs by rw [e])
  iapply Hb $$ Hv

section arrays
variable {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n] [TypedPointsto (GF := GF) V]
  [BytesView (GF := GF) V]

omit [ZeroVal V] [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] in
theorem flatMap_encode_length (vs : List V) : (vs.flatMap encode).length = vs.length * n := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [List.flatMap_cons, ih, Nat.succ_mul]; omega

/-- The elements of an array of plain `e` from a positive address are the bytes of the
elements. -/
theorem arrayElems_bytesView (e : go.GoType) [TypeRepr e V] {a : Nat} (hlay : go.PlainLayout e n a)
    (l : Loc) (vs : List V) (dq : DFrac) (hl : 0 < l.addr) :
    arrayElems (GF := GF) l vs dq ⊣⊢ bytesPointsto l dq (vs.flatMap encode) := by
  induction vs generalizing l with
  | nil =>
    unfold arrayElems
    simp only [List.flatMap_nil, bytesPointsto]
    exact ⟨by iintro _; itrivial, by iintro _; iapply BigSepL.bigSepL_nil.2; itrivial⟩
  | cons v vs ih =>
    have e0 : arrayIndexRef V 0 l = l := go.arrayIndexRef_0 _ _
    have e1 : arrayIndexRef V 1 l = l +ₗ (n : Int) := by
      have := go.arrayIndexRef_plain e V n a 1 l hlay hl (by decide)
      simpa using this
    have hl' : 0 < (l +ₗ (n : Int)).addr := by simp [Loc.add]; omega
    have happ := bytesPointsto_app (GF := GF) l dq (encode v) (vs.flatMap encode)
    rw [ByteEncoding.encode_length] at happ
    have ih' := ih _ hl'
    refine (arrayElems_cons l v vs dq).trans ?_
    rw [e0, e1, List.flatMap_cons]
    constructor
    · iintro ⟨Hv, Hvs⟩
      iapply happ.2
      isplitl [Hv]
      · iapply (typedPointsto_bytes l v dq hl).1 $$ Hv
      · iapply ih'.1 $$ Hvs
    · iintro Hb
      icases happ.1 $$ Hb with ⟨Hv, Hvs⟩
      isplitl [Hv]
      · iapply (typedPointsto_bytes l v dq hl).2 $$ Hv
      · iapply ih'.2 $$ Hvs

/-- An array of plain `e` at a positive address is the bytes of its elements. -/
theorem typedPointsto_array_bytes (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (l : Loc) (len : Int) (arr : GoArray V len) (dq : DFrac)
    (hl : 0 < l.addr) :
    typedPointsto (GF := GF) l arr dq ⊣⊢
      ⌜(arr.arr.length : Int) = len⌝ ∗ bytesPointsto l dq (arr.arr.flatMap encode) := by
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  have he := arrayElems_bytesView (GF := GF) e hlay l arr.arr dq hl
  constructor
  · iintro H
    icases typedPointsto_split _ _ _ $$ H with H
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨%Hlen, H⟩
    isplitr
    · ipureintro; exact Hlen
    · iapply he.1 $$ H
  · iintro ⟨%Hlen, H⟩
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    isplitr
    · ipureintro; exact Hlen
    · iapply he.2 $$ H

/-- A slice of plain `e` at a positive address is the bytes of its elements. -/
theorem ownSlice_bytes_acc (e : go.GoType) [TypeRepr e V] {a : Nat} (hlay : go.PlainLayout e n a)
    (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr) :
    (s ↦*{dq} vs : IProp GF) ⊢
      bytesPointsto s.ptr dq (vs.flatMap encode) ∗
        ∀ vs' : List V, ⌜vs'.length = vs.length⌝ -∗ bytesPointsto s.ptr dq (vs'.flatMap encode) -∗
          s ↦*{dq} vs' := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hcap⟩)
  · obtain ⟨Hs, Hvs⟩ := H
    subst Hs Hvs
    simp [slice.nil, null] at hl
  · icases typedPointsto_not_null _ _ _ $$ Hsl with %Hnn
    icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%Hlen, Hsl⟩
    icases (arrayElems_bytesView e hlay s.ptr vs dq hl).1 $$ Hsl with Hsl
    iframe Hsl
    iintro %vs' %Hvs' Hb
    iright
    isplitl [Hb]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; show ((vs'.length : Int)) = _; rw [Hvs']; exact Hlen
      · iapply (arrayElems_bytesView e hlay s.ptr vs' dq hl).2 $$ Hb
    · ipureintro; exact Hcap

omit [ByteEncoding V n] [BytesView (GF := GF) V] in
/-- A non-empty array of elements whose points-tos are at positive addresses is at a positive
address. -/
theorem typedPointsto_array_pos [PointstoPos (GF := GF) V] (l : Loc) (len : Int)
    (arr : GoArray V len) (dq : DFrac) (hne : arr.arr ≠ []) :
    typedPointsto (GF := GF) l arr dq ⊢ ⌜0 < l.addr⌝ := by
  obtain ⟨vs⟩ := arr
  cases vs with
  | nil => exact absurd rfl hne
  | cons v vs =>
    iintro H
    icases typedPointsto_split _ _ _ $$ H with H
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨_, H⟩
    icases (arrayElems_cons l v vs dq).1 $$ H with ⟨Hv, _⟩
    rw [go.arrayIndexRef_0]
    iapply typedPointsto_pos _ _ _ $$ Hv

/-- A new zeroed array of plain `e` with points-tos at positive addresses (`make([]T, n)`'s
backing array) is the bytes of `n` zero values at a positive address. -/
theorem typedPointsto_zero_array_bytes [PointstoPos (GF := GF) V] (e : go.GoType) [TypeRepr e V]
    {a : Nat} (hlay : go.PlainLayout e n a) (l : Loc) (len : Int) (k : Nat) (dq : DFrac)
    (hk : len = k) (hpos : 0 < k) :
    typedPointsto (GF := GF) l (zero_val (GoArray V len)) dq ⊢
      ⌜0 < l.addr⌝ ∗ bytesPointsto l dq ((List.replicate k (zero_val V)).flatMap encode) := by
  subst hk
  iintro H
  icases typedPointsto_array_pos l _ _ dq
    (by simp [zero_val, ZeroVal.zeroValDef]; omega) $$ H with %Hl
  icases (typedPointsto_array_bytes e hlay l _ _ dq Hl).1 $$ H with ⟨_, H⟩
  simp only [zero_val, ZeroVal.zeroValDef, Int.toNat_natCast]
  iframe H
  ipureintro; exact Hl

omit [ByteEncoding V n] [BytesView (GF := GF) V] in
/-- A non-empty slice of elements whose points-tos are at positive addresses is at a positive
address. -/
theorem ownSlice_ptr_pos [PointstoPos (GF := GF) V] (s : GoSlice) (vs : List V) (dq : DFrac)
    (hne : vs ≠ []) :
    (s ↦*{dq} vs : IProp GF) ⊢ ⌜0 < s.ptr.addr⌝ := by
  cases vs with
  | nil => exact absurd rfl hne
  | cons v vs =>
    rw [ownSlice_unseal]; unfold ownSliceDef
    iintro (%H | ⟨Hsl, _⟩)
    · simp at H
    · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
      try simp only [TypedPointsto.typedPointstoDef]
      icases Hsl with ⟨_, Hsl⟩
      icases (arrayElems_cons s.ptr v vs dq).1 $$ Hsl with ⟨Hv, _⟩
      rw [go.arrayIndexRef_0]
      iapply typedPointsto_pos _ _ _ $$ Hv

/-- The view at byte offset `k` of a slice of plain `e` as a `W` (`(*T)(unsafe.Pointer(p))` with
`p` pointing `k` bytes into the slice's elements). Storing a value through the view leaves a
slice whose elements' bytes are `replaceBytes`'s. -/
theorem ownSlice_plain_view (e : go.GoType) [TypeRepr e V] {a : Nat} (hlay : go.PlainLayout e n a)
    {W : Type} {m : Nat} [ByteEncoding W m] [TypedPointsto (GF := GF) W] [BytesView (GF := GF) W]
    (s : GoSlice) (vs : List V) (dq : DFrac) (k : Nat) (h : k + m ≤ vs.length * n)
    (hl : 0 < s.ptr.addr) :
    (s ↦*{dq} vs : IProp GF) ⊢
      typedPointsto (s.ptr +ₗ (k : Int)) (decode (((vs.flatMap encode).drop k).take m) : W) dq ∗
        ∀ (w : W) (vs' : List V), ⌜vs'.length = vs.length⌝ -∗
          ⌜vs'.flatMap encode = replaceBytes (vs.flatMap encode) k (encode w)⌝ -∗
          typedPointsto (s.ptr +ₗ (k : Int)) w dq -∗ s ↦*{dq} vs' := by
  iintro Hs
  icases ownSlice_bytes_acc e hlay s vs dq hl $$ Hs with ⟨Hb, Hs⟩
  icases bytesPointsto_view (V := W) s.ptr dq _ k (by rw [flatMap_encode_length]; omega) hl $$ Hb
    with ⟨Hw, Hb⟩
  iframe Hw
  iintro %w %vs' %Hlen %Heq Hw
  iapply Hs $$ %vs' %Hlen
  rw [Heq]
  iapply Hb $$ Hw

end arrays

/-- An array of bytes is its bytes. -/
theorem typedPointsto_byte_array (l : Loc) (len : Int) (arr : GoArray w8 len) (dq : DFrac)
    (hne : arr.arr ≠ []) :
    typedPointsto (GF := GF) l arr dq ⊣⊢ ⌜(arr.arr.length : Int) = len⌝ ∗ bytesPointsto l dq arr.arr := by
  constructor
  · iintro H
    icases typedPointsto_byte_array_bounds l len arr dq hne $$ H with %Hb
    have h := typedPointsto_array_bytes (GF := GF) go.uint8 (.scalar _ _ .isPlainScalar_uint8)
      l len arr dq Hb.1
    rw [flatMap_encode_w8] at h
    iapply h.1 $$ H
  · iintro ⟨%Hlen, H⟩
    icases bytesPointsto_pos l dq _ hne $$ H with %Hl
    have h := typedPointsto_array_bytes (GF := GF) go.uint8 (.scalar _ _ .isPlainScalar_uint8)
      l len arr dq Hl
    rw [flatMap_encode_w8] at h
    iapply h.2
    iframe H; ipureintro; exact Hlen

/-- A new zeroed byte array (`make([]byte, n)`'s backing array) is `n` zero bytes at a positive
address. -/
theorem typedPointsto_zero_byte_array (l : Loc) (len : Int) (n : Nat) (dq : DFrac)
    (hn : len = n) (hlen : 0 < n) :
    typedPointsto (GF := GF) l (zero_val (GoArray w8 len)) dq ⊢
      ⌜0 < l.addr⌝ ∗ bytesPointsto l dq (List.replicate n 0) := by
  subst hn
  have hne : (zero_val (GoArray w8 (n : Int))).arr ≠ [] := by
    simp [zero_val, ZeroVal.zeroValDef]; omega
  iintro H
  icases (typedPointsto_byte_array l _ _ dq hne).1 $$ H with ⟨_, H⟩
  icases bytesPointsto_pos l dq _ hne $$ H with %Hl
  simp only [zero_val, ZeroVal.zeroValDef, Int.toNat_natCast]
  iframe H
  ipureintro; exact Hl

/-- The view at offset `k` of a `[]byte` as a `V`: `(*T)(unsafe.Pointer(&buf[k]))`. -/
theorem ownSlice_byte_view {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (s : GoSlice) (vs : List w8) (dq : DFrac) (k : Nat)
    (h : k + n ≤ vs.length) (hn : 0 < n) :
    (s ↦*{dq} vs : IProp GF) ⊢
      typedPointsto (sliceIndexRef w8 (k : Int) s) (decode ((vs.drop k).take n) : V) dq ∗
        ∀ v : V, typedPointsto (sliceIndexRef w8 (k : Int) s) v dq -∗
          s ↦*{dq} (replaceBytes vs k (encode v)) := by
  iintro Hs
  icases ownSlice_ptr_pos s vs dq (by intro h'; subst h'; simp at h; omega) $$ Hs with %Hl
  have hidx : sliceIndexRef w8 (k : Int) s = s.ptr +ₗ (k : Int) := by
    have := go.arrayIndexRef_plain go.uint8 w8 1 1 k s.ptr (.scalar _ _ .isPlainScalar_uint8) Hl
      (by omega)
    simpa [sliceIndexRef] using this
  rw [hidx]
  icases ownSlice_plain_view (V := w8) (W := V) go.uint8 (.scalar _ _ .isPlainScalar_uint8) s vs dq
    k (by simpa using h) Hl $$ Hs with ⟨Hv, Hs⟩
  simp only [flatMap_encode_w8]
  iframe Hv
  iintro %v Hv
  iapply Hs $$ %v %(replaceBytes vs k (encode v))
  · ipureintro; exact replaceBytes_length vs k _ (by simp; omega)
  · ipureintro; simp
  · iexact Hv

/-! ### Struct views

A plain struct's typed points-to is its fields' points-tos at `structFieldRef V f l`, which is
`l +ₗ off` for the field's offset (`structFieldRef_plain`). After rewriting the field addresses,
`bytesView_field` and `bytesView_last_field` peel the fields off one at a time, and
`bytesView_of_def` adds the non-null part of `typedPointsto`. -/

theorem bytesView_field {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (l : Loc) (off : Nat) (v : V) (dq : DFrac) (name : String)
    (R : IProp GF) (bs : List w8) (hl : 0 < l.addr)
    (h : R ⊣⊢ bytesPointsto (l +ₗ ((off + n : Nat) : Int)) dq bs) :
    iprop(named name (typedPointsto (l +ₗ (off : Int)) v dq) ∗ R) ⊣⊢
      bytesPointsto (l +ₗ (off : Int)) dq (encode v ++ bs) := by
  have hlo : 0 < (l +ₗ (off : Int)).addr := by simp [Loc.add]; omega
  have happ := bytesPointsto_app (GF := GF) (l +ₗ (off : Int)) dq (encode v) bs
  rw [ByteEncoding.encode_length, loc_add_assoc,
    show (off : Int) + (n : Int) = ((off + n : Nat) : Int) by omega] at happ
  have hv := typedPointsto_bytes (GF := GF) (l +ₗ (off : Int)) v dq hlo
  unfold named
  constructor
  · iintro ⟨Hv, HR⟩
    iapply happ.2
    isplitl [Hv]
    · iapply hv.1 $$ Hv
    · iapply h.1 $$ HR
  · iintro Hb
    icases happ.1 $$ Hb with ⟨Hv, HR⟩
    isplitl [Hv]
    · iapply hv.2 $$ Hv
    · iapply h.2 $$ HR

theorem bytesView_last_field {V : Type} {n : Nat} [ByteEncoding V n] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (l : Loc) (off : Nat) (v : V) (dq : DFrac) (name name' : String)
    (hl : 0 < l.addr) :
    iprop(named name (typedPointsto (l +ₗ (off : Int)) v dq) ∗ named name' iprop(True)) ⊣⊢
      bytesPointsto (l +ₗ (off : Int)) dq (encode v) := by
  have h := bytesView_field (GF := GF) l off v dq name (named name' iprop(True)) [] hl
    ⟨by iintro _; unfold bytesPointsto; itrivial, by iintro _; unfold named; itrivial⟩
  rw [List.append_nil] at h
  exact h

/-- A typed points-to is the bytes its definition is (with the struct's first field at
`l +ₗ ((0 : Nat) : Int)`, as `structFieldRef_offset` gives it). -/
theorem bytesView_of_def {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac)
    (bs : List w8) (hne : bs ≠ [])
    (h : typedPointstoDef (GF := GF) l v dq ⊣⊢ bytesPointsto (l +ₗ ((0 : Nat) : Int)) dq bs) :
    typedPointsto (GF := GF) l v dq ⊣⊢ bytesPointsto l dq bs := by
  rw [show l +ₗ ((0 : Nat) : Int) = l by simp] at h
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  constructor
  · iintro ⟨H, _⟩; iapply h.1 $$ H
  · iintro H
    icases bytesPointsto_non_null l dq bs hne $$ H with ⟨H, %Hnn⟩
    isplitl [H]
    · iapply h.2 $$ H
    · ipureintro; exact Hnn

end views

/-! ## Concrete addresses -/

theorem sint_Z_W64_nat (i : Nat) (hi : i < 2 ^ 63) : sint.Z (W64 (i : Int)) = i := by
  simp only [sint.Z, W64, BitVec.toInt_ofInt]
  rw [Int.bmod_def]
  split <;> omega

section addresses
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- The address of element `i` of an array of plain `e` at a positive address. -/
theorem arrayIndexRef_plain_eq {V : Type} {n : Nat} [ZeroVal V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (l : Loc) (i : Int) (hl : 0 < l.addr) (hi : 0 ≤ i) :
    arrayIndexRef V i l = l +ₗ i * (n : Int) :=
  go.arrayIndexRef_plain e V n a i l hlay hl hi

/-- The address of element `i` of a slice of plain `e`, for the literal index `W64 i` of the
program. -/
theorem sliceIndexRef_plain_W64 {V : Type} {n : Nat} [ZeroVal V] (e : go.GoType) [TypeRepr e V]
    {a : Nat} (hlay : go.PlainLayout e n a) (s : GoSlice) (i : Nat) (hl : 0 < s.ptr.addr)
    (hi : i < 2 ^ 63) :
    sliceIndexRef V (sint.Z (W64 (i : Int))) s = s.ptr +ₗ ((i * n : Nat) : Int) := by
  simp only [sliceIndexRef]
  rw [sint_Z_W64_nat i hi, arrayIndexRef_plain_eq e hlay s.ptr i hl (by omega)]
  norm_cast

/-- The address of element `i` of a slice of plain `e`, for an index `i` of the program. -/
theorem sliceIndexRef_plain {V : Type} {n : Nat} [ZeroVal V] (e : go.GoType) [TypeRepr e V]
    {a : Nat} (hlay : go.PlainLayout e n a) (s : GoSlice) (i : w64) (hl : 0 < s.ptr.addr)
    (hi : 0 ≤ sint.Z i) :
    sliceIndexRef V (sint.Z i) s = s.ptr +ₗ ((sint.nat i * n : Nat) : Int) := by
  simp only [sliceIndexRef]
  rw [arrayIndexRef_plain_eq e hlay s.ptr _ hl hi]
  congr 1; simp only [sint.nat]; push_cast; rw [Int.toNat_of_nonneg hi]

/-- The address of byte `i` of a byte array at a positive address. -/
theorem arrayIndexRef_byte (l : Loc) (i : Int) (hl : 0 < l.addr) (hi : 0 ≤ i) :
    arrayIndexRef w8 i l = l +ₗ i := by
  have := go.arrayIndexRef_plain go.uint8 w8 1 1 i l (.scalar _ _ .isPlainScalar_uint8) hl hi
  simpa using this

/-- The address of byte `i` of a slice at a positive address. -/
theorem sliceIndexRef_byte (s : GoSlice) (i : Int) (hl : 0 < s.ptr.addr) (hi : 0 ≤ i) :
    sliceIndexRef w8 i s = s.ptr +ₗ i :=
  arrayIndexRef_byte s.ptr i hl hi

/-- The address of byte `i` of a slice, for the literal index `W64 i` of the program. -/
theorem sliceIndexRef_byte_W64 (s : GoSlice) (i : Nat) (hl : 0 < s.ptr.addr) (hi : i < 2 ^ 63) :
    sliceIndexRef w8 (sint.Z (W64 (i : Int))) s = s.ptr +ₗ (i : Int) := by
  rw [sint_Z_W64_nat i hi]
  exact sliceIndexRef_byte s i hl (by omega)

/-- A field of a plain struct at a positive address is at its offset. -/
theorem structFieldRef_offset (fds : List go.field_decl) (V : Type) [ZeroVal V]
    [TypeRepr (go.StructType fds) V] {s a : Nat} (hlay : go.PlainLayout (go.StructType fds) s a)
    (f : GoString) (off : Nat) (hoff : go.PlainFieldOffset fds 0 f off) (l : Loc) (hl : 0 < l.addr) :
    structFieldRef V f l = l +ₗ ((off : Nat) : Int) :=
  go.structFieldRef_plain fds V s a f off l hlay hoff hl

end addresses

/-! ## Layout rules for `apply` -/

/-- `go.PlainLayout.struct` with the alignment the fields compute checked by an equation. -/
theorem go.PlainLayout.struct' [GooseExts] [GoSemanticsFunctions] (fds : List go.field_decl)
    (s a a' : Nat) (hne : fds ≠ []) (hf : go.PlainFields fds 0 s a') (hd : a' ∣ s) (ha : a' = a) :
    go.PlainLayout (go.StructType fds) s a := ha ▸ .struct fds s a' hne hf hd

/-- `go.PlainFields.cons` with named premises, for `apply`. -/
theorem go.PlainFields.cons_ [GooseExts] [GoSemanticsFunctions] {fd : go.field_decl}
    {fds : List go.field_decl} {off s a stop a' : Nat}
    (hl : go.PlainLayout (go.fieldDeclType fd) s a) (hb : go.isBlankField (go.fieldDeclName fd) = false)
    (hd : a ∣ off) (hr : go.PlainFields fds (off + s) stop a') :
    go.PlainFields (fd :: fds) off stop (Nat.max a a') := .cons fd fds off s a stop a' hl hb hd hr

end Perennial
