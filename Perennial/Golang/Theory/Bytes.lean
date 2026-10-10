/-
The byte view of memory: `bytesPointsto l dq bs`, the cells from `l` on hold the bytes `bs`.
Integers, byte arrays and byte slices are views of their bytes (`typedPointsto_w64_bytes`,
`ownSlice_bytes`, ...), so code that reinterprets memory through `unsafe.Pointer` (a page
of a memory-mapped file read as a struct) is verified by moving between the views; the
bytes of a region split at any offset (`bytesPointsto_app`).
-/
module

public import Perennial.Golang.Theory.Slice
public import Perennial.Golang.Theory.Predeclared

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProofMode goose_heap

section bytes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- The cells from `l` on hold the bytes `bs`. -/
noncomputable def bytesPointsto (l : Loc) (dq : DFrac) (bs : List w8) : IProp GF :=
  pointstoVals l dq (byteVals bs)

instance bytesPointsto_timeless (l : Loc) (dq : DFrac) (bs : List w8) :
    Timeless (bytesPointsto (GF := GF) l dq bs) := by
  unfold bytesPointsto; infer_instance

instance bytesPointsto_dfractional (l : Loc) (bs : List w8) :
    DFractional (fun dq => bytesPointsto (GF := GF) l dq bs) := by
  unfold bytesPointsto pointstoVals; infer_instance

theorem bytesPointsto_nil (l : Loc) (dq : DFrac) :
    bytesPointsto (GF := GF) l dq [] ⊣⊢ emp := by
  unfold bytesPointsto pointstoVals byteVals
  simp only [List.map_nil]
  exact BigSepL.bigSepL_nil

/-- The bytes of a region split at any offset. -/
theorem bytesPointsto_app (l : Loc) (dq : DFrac) (bs1 bs2 : List w8) :
    bytesPointsto (GF := GF) l dq (bs1 ++ bs2) ⊣⊢
      bytesPointsto l dq bs1 ∗ bytesPointsto (l +ₗ (bs1.length : Int)) dq bs2 := by
  unfold bytesPointsto pointstoVals byteVals
  rw [List.map_append]
  refine BigSepL.bigSepL_append.trans ?_
  refine sep_congr .rfl ?_
  rw [BigSepL.bigSepL_eq_of_forall_eq (Ψ := fun j v =>
    heapPointsto ((l +ₗ (bs1.length : Int)) +ₗ (j : Int)) dq v)
    (fun {j _} => by
      rw [loc_add_assoc, List.length_map,
        show ((j + bs1.length : Nat) : Int) = (bs1.length : Int) + (j : Int) by omega])]
  exact .rfl

theorem bytesPointsto_cons (l : Loc) (dq : DFrac) (b : w8) (bs : List w8) :
    bytesPointsto (GF := GF) l dq (b :: bs) ⊣⊢
      heapPointsto l dq (LitV (LitByte b)) ∗ bytesPointsto (l +ₗ 1) dq bs := by
  refine (bytesPointsto_app l dq [b] bs).trans (sep_congr ?_ ?_)
  · unfold bytesPointsto pointstoVals byteVals
    simp only [List.map_cons, List.map_nil]
    refine BigSepL.bigSepL_singleton.trans ?_
    rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
    exact .rfl
  · exact .rfl

/-- Bytes held at `l` mean `l` is in a block (not null). -/
theorem bytesPointsto_car (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜l.locCar ≠ 0⌝ := by
  unfold bytesPointsto
  exact pointstoVals_car l dq _ (by simpa [byteVals] using h)

theorem loc_ne_null_of_car (l : Loc) (h : l.locCar ≠ 0) : l ≠ null := by
  intro e; subst e; exact h rfl

/-- The typed points-to with the null check dropped, for a nonempty byte view. -/
theorem typedPointsto_of_def_bytes {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V)
    (dq : DFrac) (bs : List w8) (hne : bs ≠ [])
    (hdef : TypedPointsto.typedPointstoDef (GF := GF) (V := V) l v dq ⊣⊢ bytesPointsto l dq bs) :
    typedPointsto (GF := GF) l v dq ⊣⊢ bytesPointsto l dq bs := by
  rw [typedPointsto_unseal_eq]
  constructor
  · iintro ⟨H, -⟩
    iapply hdef.1 $$ H
  · iintro H
    ihave %Hc := bytesPointsto_car l dq bs hne $$ H
    isplitl [H]
    · iapply hdef.2 $$ H
    · ipureintro; exact loc_ne_null_of_car l Hc

/-- A 64-bit integer is its 8 little-endian bytes. -/
theorem typedPointsto_w64_bytes (l : Loc) (w : w64) (dq : DFrac) :
    l ↦{dq} w ⊣⊢ bytesPointsto (GF := GF) l dq (leBytes 8 w.toNat) :=
  typedPointsto_of_def_bytes l w dq _ (by simp [leBytes]) .rfl

theorem typedPointsto_w32_bytes (l : Loc) (w : w32) (dq : DFrac) :
    l ↦{dq} w ⊣⊢ bytesPointsto (GF := GF) l dq (leBytes 4 w.toNat) :=
  typedPointsto_of_def_bytes l w dq _ (by simp [leBytes]) .rfl

theorem typedPointsto_w16_bytes (l : Loc) (w : w16) (dq : DFrac) :
    l ↦{dq} w ⊣⊢ bytesPointsto (GF := GF) l dq (leBytes 2 w.toNat) :=
  typedPointsto_of_def_bytes l w dq _ (by simp [leBytes]) .rfl

theorem typedPointsto_w8_bytes [go.IntoValUnfold w8 (fun x => LitV (LitByte x))]
    (l : Loc) (b : w8) (dq : DFrac) :
    l ↦{dq} b ⊣⊢ bytesPointsto (GF := GF) l dq [b] := by
  refine typedPointsto_of_def_bytes l b dq [b] (by simp) ?_
  refine (Iris.BI.BiEntails.trans ?_ (bytesPointsto_cons l dq b []).symm)
  rw [typedPointstoDef_heap, go.intoVal_unfold w8]
  exact (sep_emp.symm).trans (sep_congr .rfl (bytesPointsto_nil _ _).symm)

theorem typedPointsto_w8_heap [go.IntoValUnfold w8 (fun x => LitV (LitByte x))]
    (l : Loc) (b : w8) (dq : DFrac) :
    l ↦{dq} b ⊣⊢ heapPointsto (GF := GF) l dq (LitV (LitByte b)) :=
  (typedPointsto_w8_bytes l b dq).trans ((bytesPointsto_cons l dq b []).trans
    ((sep_congr .rfl (bytesPointsto_nil _ _)).trans sep_emp))

include hG preSem in
/-- Element `i` of a byte array in a block is the cell `i` after its start. -/
theorem arrayIndexRef_w8 (l : Loc) (i : Int) (h : l.locCar ≠ 0) :
    arrayIndexRef w8 i l = l +ₗ i := by
  unfold arrayIndexRef
  rw [ite_eq_right_of_eq_false _ _ (eq_false h), go.typeSize_w8, Int.mul_one]

theorem arrayElems_bytes [go.IntoValUnfold w8 (fun x => LitV (LitByte x))]
    (l : Loc) (bs : List w8) (dq : DFrac) (h : l.locCar ≠ 0) :
    arrayElems (GF := GF) l bs dq ⊣⊢ bytesPointsto l dq bs := by
  unfold arrayElems bytesPointsto pointstoVals byteVals
  rw [BigSepL.bigSepL_map]
  constructor
  · exact BigSepL.bigSepL_mono fun {k b} _ => by
      rw [arrayIndexRef_w8 (hG := hG) l k h]; exact (typedPointsto_w8_heap _ b dq).1
  · exact BigSepL.bigSepL_mono fun {k b} _ => by
      rw [arrayIndexRef_w8 (hG := hG) l k h]; exact (typedPointsto_w8_heap _ b dq).2

/-- A nonempty byte slice is the bytes at its pointer. -/
theorem ownSlice_bytes [go.IntoValUnfold w8 (fun x => LitV (LitByte x))]
    (s : GoSlice) (bs : List w8) (dq : DFrac) (hne : bs ≠ []) :
    s ↦*{dq} bs ⊣⊢ (bytesPointsto (GF := GF) s.ptr dq bs ∗
      ⌜(bs.length : Int) = sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  constructor
  · iintro (%H | ⟨⟨⟨%Hlen, H⟩, %Hnn⟩, %Hcap⟩)
    · exact absurd H.2 hne
    · obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_ne_nil hne
      icases (arrayElems_cons s.ptr b bs' dq).1 $$ H with ⟨H0, H⟩
      icases (typedPointsto_w8_heap _ b dq).1 $$ H0 with H0
      ihave %Hc0 := heapPointsto_car _ _ _ $$ H0
      have Hc : s.ptr.locCar ≠ 0 := by
        intro e; apply Hc0; unfold arrayIndexRef; rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact e
      isplitl [H0 H]
      · iapply (arrayElems_bytes s.ptr (b :: bs') dq Hc).1
        iapply (arrayElems_cons s.ptr b bs' dq).2
        isplitl [H0]
        · iapply (typedPointsto_w8_heap _ b dq).2 $$ H0
        · iexact H
      · ipureintro; exact ⟨by simpa using Hlen, Hcap⟩
  · iintro ⟨H, %Hlen, %Hcap⟩
    ihave %Hc := bytesPointsto_car s.ptr dq bs hne $$ H
    iright
    isplitl [H]
    · isplitl [H]
      · isplit
        · ipureintro; simpa using Hlen
        · iapply (arrayElems_bytes s.ptr bs dq Hc).2 $$ H
      · ipureintro; exact loc_ne_null_of_car _ Hc
    · ipureintro; exact Hcap

end bytes

end Perennial
