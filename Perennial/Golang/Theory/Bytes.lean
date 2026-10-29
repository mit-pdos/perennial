/-
Byte memory for proofs about `unsafe` views (`docs/design/unsafe-memory.md`, section 9): the
elements of a `[]byte` (or `[n]byte`) as the byte points-to `bytesPointsto` from its address,
and splitting a byte points-to at an offset.
-/
module

public import Perennial.Golang.Theory.Plain

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
open ProofMode

/-- The element points-tos of bytes from a positive address are its byte points-to. -/
theorem arrayElems_bytes (l : Loc) (bs : List w8) (dq : DFrac) (hpos : 0 < l.addr) :
    arrayElems (GF := GF) l bs dq ⊣⊢ bytesPointsto l dq bs := by
  induction bs generalizing l with
  | nil =>
    unfold arrayElems bytesPointsto
    exact ⟨by iintro _; itrivial, by iintro _; iapply BigSepL.bigSepL_nil.2; itrivial⟩
  | cons b bs ih =>
    have e0 : arrayIndexRef w8 0 l = l := go.arrayIndexRef_0 _ _
    have e1 : arrayIndexRef w8 1 l = l +ₗ 1 := by
      have := go.arrayIndexRef_plain go.uint8 w8 1 1 1 l (.scalar _ _ .isPlainScalar_uint8)
        hpos (by decide)
      simpa using this
    have hpos' : 0 < (l +ₗ 1).addr := by simp [Loc.add]; omega
    have ih' := ih (l +ₗ 1) hpos'
    refine (arrayElems_cons l b bs dq).trans ?_
    rw [e0, e1]
    unfold bytesPointsto
    rw [typedPointsto_unseal]
    unfold typedPointstoWrap
    simp only [typedPointstoDef_heap, go.intoVal_unfold w8]
    constructor
    · iintro ⟨⟨Hb, _⟩, Hbs⟩
      iframe Hb
      iapply ih'.1 $$ Hbs
    · iintro ⟨Hb, Hbs⟩
      icases heapPointsto_non_null l dq _ $$ Hb with %Hnn
      iframe Hb
      isplitr
      · ipureintro; exact Hnn
      · iapply ih'.2 $$ Hbs

/-- A byte points-to splits at the end of a prefix. -/
theorem bytesPointsto_app (l : Loc) (dq : DFrac) (bs1 bs2 : List w8) :
    bytesPointsto (GF := GF) l dq (bs1 ++ bs2) ⊣⊢
      bytesPointsto l dq bs1 ∗ bytesPointsto (l +ₗ (bs1.length : Int)) dq bs2 := by
  induction bs1 generalizing l with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
    unfold bytesPointsto
    exact ⟨by iintro H; iframe H, by iintro ⟨_, H⟩; iexact H⟩
  | cons b bs1 ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show ((bs1.length + 1 : Nat) : Int) = 1 + (bs1.length : Int) by omega, ← loc_add_assoc]
    have := ih (l +ₗ 1)
    simp only [bytesPointsto]
    constructor
    · iintro ⟨Hb, H⟩
      icases this.1 $$ H with ⟨H1, H2⟩
      isplitl [Hb H1]
      · iframe
      · iexact H2
    · iintro ⟨⟨Hb, H1⟩, H2⟩
      isplitl [Hb]
      · iexact Hb
      · iapply this.2
        iframe

end bytes

end Perennial
