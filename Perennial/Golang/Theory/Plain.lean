/-
Facts about plain layouts (`Golang/Defn/Plain.lean`): examples that check the definitions
against gc's layout, and the positive address of a byte points-to, which the axioms of
`go.PlainSemantics` need.
-/
module

public import Perennial.Golang.Theory.Predeclared
public import Perennial.Golang.Theory.Array

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section examples
variable [GooseExts] [GoSemanticsFunctions]

/-- `struct { a uint32; b uint32 }` is plain, 8 bytes, aligned 4, and `b` is at offset 4 (gc:
`unsafe.Sizeof` 8, `unsafe.Offsetof(.b)` 4). -/
example : go.PlainLayout
    (go.StructType [go.FieldDecl go!"a" go.uint32, go.FieldDecl go!"b" go.uint32]) 8 4 :=
  .struct _ 8 4 (by simp)
    (.cons _ _ 0 4 4 8 4 (.scalar _ _ .isPlainScalar_uint32) rfl (Nat.dvd_zero 4)
      (.cons _ _ 4 4 4 8 1 (.scalar _ _ .isPlainScalar_uint32) rfl (Nat.dvd_refl 4)
        (.nil 8)))
    (by decide)

example : go.PlainFieldOffset [go.FieldDecl go!"a" go.uint32, go.FieldDecl go!"b" go.uint32] 0
    go!"b" 4 :=
  .there _ _ 0 4 4 _ 4 (by decide) (.scalar _ _ .isPlainScalar_uint32) (.here _ _ 4)

/-- `[3]uint16` is plain, 6 bytes, aligned 2. -/
example : go.PlainLayout (go.ArrayType 3 go.uint16) 6 2 :=
  .array 3 _ 2 2 (.scalar _ _ .isPlainScalar_uint16) (by decide)

end examples

section instances
variable [GooseExts] [GoSemanticsFunctions]

/-- A plain scalar is plain. -/
instance isPlain_scalar (t : go.GoType) (w : Nat) [h : go.IsPlainScalar t w] : go.IsPlain t w :=
  ⟨w, .scalar t w h⟩

end instances

section pos
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
open ProofMode

/-- A points-to of at least one byte is at a positive address. -/
theorem bytesPointsto_pos (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr⌝ := by
  cases bs with
  | nil => exact absurd rfl h
  | cons b bs =>
    unfold bytesPointsto
    iintro ⟨Hb, _⟩
    iapply heapPointsto_pos l dq _ $$ Hb

/-- The element points-tos of at least one byte from `l` lie in `(0, maxAddr]`: each is a heap
points-to, and consecutive bytes are at consecutive addresses (`arrayIndexRef_plain`). -/
theorem arrayElems_bytes_bounds [GoSemanticsFunctions] [go.PreSemantics] (l : Loc) (bs : List w8)
    (dq : DFrac) (h : bs ≠ []) :
    arrayElems (GF := GF) l bs dq ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  have head : ∀ (l : Loc) (b : w8), typedPointsto (GF := GF) (arrayIndexRef w8 0 l) b dq ⊢
      ⌜0 < l.addr ∧ l.addr < maxAddr⌝ := by
    intro l b
    rw [go.arrayIndexRef_0, typedPointsto_unseal]
    unfold typedPointstoWrap
    simp only [typedPointstoDef_heap]
    iintro ⟨Hb, _⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    ipureintro; exact ⟨H1, H2⟩
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    iintro He
    icases (arrayElems_cons l b bs dq).1 $$ He with ⟨Hb, Hbs⟩
    icases head l b $$ Hb with %Hl
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      have e1 : arrayIndexRef w8 1 l = l +ₗ 1 := by
        have := go.arrayIndexRef_plain go.uint8 w8 1 1 1 l (.scalar _ _ .isPlainScalar_uint8)
          Hl.1 (by decide)
        simpa using this
      rw [e1]
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %Ht
      ipureintro
      simp only [Loc.add, List.length_cons] at Ht ⊢
      omega

/-- An array of `n ≥ 1` bytes at `l` lies in `(0, maxAddr]`. -/
theorem typedPointsto_byte_array_bounds [GoSemanticsFunctions] [go.PreSemantics] (l : Loc)
    (n : Int) (a : GoArray w8 n) (dq : DFrac) (h : a.arr ≠ []) :
    typedPointsto (GF := GF) l a dq ⊢ ⌜0 < l.addr ∧ l.addr + n ≤ maxAddr⌝ := by
  obtain ⟨arr⟩ := a
  iintro H
  icases typedPointsto_split l _ dq $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨%Hlen, He⟩
  icases arrayElems_bytes_bounds l arr dq h $$ He with %Hb
  ipureintro
  omega

/-- The pointer addition of `unsafe.Add`, for a result in `[0, maxAddr]`. -/
theorem wp_pointer_plus [GoSemanticsFunctions] [go.PreSemantics] {s : Stuckness} {E : CoPset}
    (t : go.GoType) (l : Loc) (x : w64)
    (h : 0 ≤ (l +ₗ sint.Z x).addr ∧ (l +ₗ sint.Z x).addr ≤ maxAddr) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoOp GoPlus (go.PointerType t)))) (Val (PairV #l #x))) @ s; E
    {{ RET #(l +ₗ sint.Z x); True }} := by
  haveI := go.tagged_steps _ _ _ _ (go.is_go_op_pointer_plus t l x h)
  iintro %Φ _ HΦ
  iapply wp_go_step_receipt' _ _ _ Φ rfl
  inext
  iintro _ _
  iapply wp_value'
  iapply HΦ
  itrivial

end pos

end Perennial
