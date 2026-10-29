/-
Facts about plain layouts (`Golang/Defn/Plain.lean`): examples that check the definitions
against gc's layout, and the positive address of a byte points-to, which the axioms of
`go.PlainSemantics` need.
-/
module

public import Perennial.Golang.Theory.Predeclared

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

end pos

end Perennial
