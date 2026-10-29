/-
Facts for `Meta` of the `unsafememory` example (`meta.go`): FNV-1a, the checksum `sum64` computes
over the bytes of a `Meta` before its `checksum` field. Each step `h ↦ (h ^ c) * prime` is
injective in `c` for a fixed `h` and in `h` for a fixed `c` (the prime is odd, so multiplying by
it is invertible mod `2^64`), so changing one byte of the input changes the hash
(`fnv64_set_ne`).

`metaSum v` is `sum64`'s result: FNV-1a over the first 56 bytes of `v`. It does not depend on the
checksum (`metaSum_with_checksum`), and changing a byte before the checksum of a `Meta` with a
valid checksum leaves an invalid one (`Meta.set_checksum_ne`). `[56]byte`, the array `sum64`
views the `Meta` as, is plain (`byteArray56.isPlain`), and `Meta.wp_alloc_pos` allocates a `Meta`
at a positive address, where it has a byte view.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-! ## FNV-1a -/

/-- FNV-1a's 64-bit prime. -/
def fnvPrime : BitVec 64 := 1099511628211

/-- FNV-1a's 64-bit offset basis, the hash of no bytes. -/
def fnvOffset : BitVec 64 := 14695981039346656037

/-- One step of FNV-1a: `h ^= uint64(c); h *= prime`. -/
def fnvStep (h : BitVec 64) (c : BitVec 8) : BitVec 64 := (h ^^^ c.setWidth 64) * fnvPrime

/-- FNV-1a over `bs` from `h`. -/
def fnvFrom (h : BitVec 64) (bs : List (BitVec 8)) : BitVec 64 := bs.foldl fnvStep h

/-- FNV-1a's 64-bit hash of `bs`. -/
def fnv64 (bs : List (BitVec 8)) : BitVec 64 := fnvFrom fnvOffset bs

/-- `Meta.sum64`'s result for a `Meta` `v`: FNV-1a over its bytes before `checksum` (56 of its
64). -/
def metaSum [GooseExts] (v : Meta) : w64 := fnv64 ((encode v).take 56)

/-- The inverse of `fnvPrime` mod `2^64`. -/
def fnvPrimeInv : BitVec 64 := 14886173955864302971

theorem fnvPrime_mul_inv : fnvPrime * fnvPrimeInv = 1 := by
  apply BitVec.eq_of_toNat_eq
  rfl

theorem mul_fnvPrime_inj {a b : BitVec 64} (h : a * fnvPrime = b * fnvPrime) : a = b := by
  have e := congrArg (· * fnvPrimeInv) h
  simp only [BitVec.mul_assoc, fnvPrime_mul_inv] at e
  simpa using e

theorem setWidth_8_64_inj {c c' : BitVec 8} (h : c.setWidth 64 = c'.setWidth 64) : c = c' := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at e
  rwa [Nat.mod_eq_of_lt (by have := c.isLt; omega),
    Nat.mod_eq_of_lt (by have := c'.isLt; omega)] at e

theorem xor_left_inj' {h x y : BitVec 64} (e : h ^^^ x = h ^^^ y) : x = y := by
  have e' := congrArg (h ^^^ ·) e
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using e'

/-- A step is injective in the hash. -/
theorem fnvStep_inj_left {h h' : BitVec 64} {c : BitVec 8} (e : fnvStep h c = fnvStep h' c) :
    h = h' := by
  have e1 := mul_fnvPrime_inj e
  have e2 := congrArg (· ^^^ c.setWidth 64) e1
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using e2

/-- A step is injective in the byte. -/
theorem fnvStep_inj_right {h : BitVec 64} {c c' : BitVec 8} (e : fnvStep h c = fnvStep h c') :
    c = c' :=
  setWidth_8_64_inj (xor_left_inj' (mul_fnvPrime_inj e))

/-- FNV-1a over a fixed list of bytes is injective in its starting hash. -/
theorem fnvFrom_inj_left (bs : List (BitVec 8)) {h h' : BitVec 64}
    (e : fnvFrom h bs = fnvFrom h' bs) : h = h' := by
  induction bs generalizing h h' with
  | nil => exact e
  | cons c bs ih => exact fnvStep_inj_left (ih e)

/-- Changing one byte changes the hash. -/
theorem fnvFrom_ne (h : BitVec 64) (a b : List (BitVec 8)) {c c' : BitVec 8} (hc : c ≠ c') :
    fnvFrom h (a ++ c :: b) ≠ fnvFrom h (a ++ c' :: b) := by
  intro e
  simp only [fnvFrom, List.foldl_append, List.foldl_cons] at e
  exact hc (fnvStep_inj_right (fnvFrom_inj_left b e))

/-- Changing byte `i` of `bs` changes its FNV-1a hash. -/
theorem fnv64_set_ne (bs : List (BitVec 8)) (i : Nat) (c : BitVec 8) (hi : i < bs.length)
    (hc : bs[i] ≠ c) : fnv64 (bs.set i c) ≠ fnv64 bs := by
  have e1 : bs = bs.take i ++ bs[i] :: bs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have e2 : bs.set i c = bs.take i ++ c :: bs.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop]; simp [hi]
  rw [e2]
  conv => rhs; rw [e1]
  exact fun e => fnvFrom_ne fnvOffset _ _ hc e.symm

/-- Flipping the low bit changes a byte. -/
theorem w8_ne_xor_one (c : BitVec 8) : c ≠ c ^^^ 1#8 := by
  intro h
  have e := congrArg (c ^^^ ·) h
  simp only [BitVec.xor_self, ← BitVec.xor_assoc] at e
  exact absurd e (by decide)

/-! ## The checksum of a `Meta` -/

section meta_bytes
variable [GooseExts]

/-- The bytes of a `Meta` before its checksum are those of its other fields. -/
theorem Meta.encode_take (v : Meta) :
    (encode v).take 56 = encode (v.magic', v.version', v.pageSize', v.flags', v.root',
      v.freelist', v.pgid', v.txid') := by
  have e : encode v = encode (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist',
      v.pgid', v.txid') ++ encode v.checksum' := by
    show encode (v.magic', v.version', v.pageSize', v.flags', v.root', v.freelist', v.pgid',
      v.txid', v.checksum') = _
    simp only [ByteEncoding.prod_encode, List.append_assoc]
  rw [e, List.take_left' (by rw [ByteEncoding.encode_length])]

/-- The checksum does not cover itself. -/
theorem metaSum_with_checksum (v : Meta) (c : w64) :
    metaSum { v with checksum' := c } = metaSum v := by
  simp only [metaSum, Meta.encode_take]

/-- The checksum of the `Meta` decoded from `bs` is its last 8 bytes. -/
theorem Meta.decode_checksum (bs : List w8) :
    (decode bs : Meta).checksum' = decode (bs.drop 56) := by
  have e : (decode bs : Meta).checksum' = decode ((((((((bs.drop 4).drop 4).drop 4).drop 4).drop
      16).drop 8).drop 8).drop 8) := rfl
  rw [e]
  simp only [List.drop_drop]

/-- Changing a byte of a `Meta` before its checksum makes a valid checksum invalid. -/
theorem Meta.set_checksum_ne (v : Meta) (i : Nat) (b : w8) (hi : i < 56)
    (hb : (encode v)[i]'(by rw [ByteEncoding.encode_length]; omega) ≠ b)
    (hv : v.checksum' = metaSum v) :
    (decode ((encode v).set i b) : Meta).checksum' ≠ metaSum (decode ((encode v).set i b)) := by
  have hlen : ((encode v).set i b).length = 64 := by simp
  rw [Meta.decode_checksum, List.drop_set_of_lt (by omega), ← Meta.decode_checksum,
    ByteEncoding.decode_encode, hv]
  unfold metaSum
  rw [ByteEncoding.encode_decode _ hlen, List.take_set]
  exact (fnv64_set_ne _ i b (by simp; omega) (by simpa using hb)).symm

end meta_bytes

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-! ## Allocation of a struct at a positive address

`struct_wp_alloc` (the allocation of a struct, `IntoValTyped.wp_alloc`) keeps only `l ≠ null` of
the address `GoPrealloc` gives; a byte view of the new struct (`BytesView`) needs `0 < l.addr`,
which `GoPrealloc` also gives (`wp_GoPrealloc_pos`). -/

section alloc_pos
open Iris Iris.BI Iris.ProgramLogic Iris.Std
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem struct_wp_alloc_pos {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (v : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜0 < l.addr⌝ }} := by
  iintro %Φ _ HΦ
  have hpw : PureWp (hlc := hlc) (GF := GF) ((#v : val).isPanic = false)
      (App (Val (GoInstruction (GoAlloc t))) (Val #v))
      (allocStructRaw fds #v fds_unsealed) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) (by simp))
  inext
  rw [allocStructRaw_eq]
  wp_bind (GoPrealloc #())
  iapply wp_GoPrealloc_pos
  · itrivial
  inext
  iintro %l %Hl
  wp_pures
  rw [subst_allocFields]
  wp_bind (List.foldr _ _ _)
  iapply (struct_alloc_fields' v l s E fds_unsealed fs hfs)
  iintro Hfs
  wp_pures
  iapply HΦ
  isplitl [Hfs]
  · rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    isplitl [Hfs]
    · iapply (hdef l v _).2
      iexact Hfs
    · ipureintro; intro h; subst h; simp [null] at Hl
  · ipureintro; exact Hl.1

end alloc_pos

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-- `[56]byte`, the bytes `sum64` views (`(*[unsafe.Offsetof(Meta{}.checksum)]byte)(...)`), is
plain. -/
instance byteArray56.isPlain [GooseExts] [GoSemanticsFunctions] :
    go.IsPlain (go.ArrayType 56 go.byte) 56 :=
  ⟨1, .array 56 go.byte 1 1 (.scalar _ _ .isPlainScalar_uint8) (by decide)⟩

section meta_alloc
open Iris Iris.BI Iris.ProgramLogic Iris.Std
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- `&Meta{...}` is at a positive address, so its bytes can be viewed (`Meta.bytesView`). -/
theorem Meta.wp_alloc_pos {s : Stuckness} {E : CoPset} (v : Meta) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc Meta.ty))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v ∗ ⌜0 < l.addr⌝ }} := by
  refine struct_wp_alloc_pos (fds := Meta.fields) (fds_unsealed := Meta.fieldsUnsealed)
    [StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"magic" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"version" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"pageSize" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"flags" go.uint32 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"root" InBucket.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"freelist" Pgid.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"pgid" Pgid.ty _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"txid" go.uint64 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance),
      StructFieldDesc.mk (V := Meta) (T := go.StructType Meta.fields) go!"checksum" go.uint64 _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance)]
    ?_ ?_ v
  · simp only [FieldsMatch, fieldDeclName, fieldDeclType, and_self]
  · intro _ _ _; exact .rfl

end meta_alloc

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

end Perennial
