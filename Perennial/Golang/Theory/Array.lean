/-
Port of `new/golang/theory/array.v`: the typed points-to for arrays
(`l ↦{dq} (a : array.t V n)` is the points-to of every element at
`array_index_ref V i l`), and lemmas to access and split it.

`into_val_typed_array` is `Admitted` in Rocq and is `sorry` here.
-/
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Defn.Array

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std BigSepL

/-- `go.index_ref_array` with the `ZeroVal V` instance determined by
`TypeRepr elem_type V` (see `go_zero_val_step'`). -/
instance (priority := high) index_ref_array' [ffi_syntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (n : Int) (elem_type : go.type) (i : w64) (l : loc)
    {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦IndexRef (go.ArrayType n elem_type), (#l, #i)⟧ ⤳[under]
      (if sint.Z i < n then #(array_index_ref V (sint.Z i) l) else Panic "index out of range") :=
  go.index_ref_array n elem_type i l

instance (priority := high) slice_array_step' [ffi_syntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (n : Int) (elem_type : go.type) (p : loc)
    (low high : w64) {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦Slice (go.ArrayType n elem_type), (#p, #low, #high)⟧ ⤳
       (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ n then
          #(slice.mk (array_index_ref V (sint.Z low) p) (high - low) (W64 n - low))
        else Panic "slice bounds out of range") :=
  go.slice_array_step n elem_type p low high

section lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- The element points-tos of a list of values starting at `l`. -/
abbrev array_elems (l : loc) (vs : List V) (dq : DFrac) : IProp GF :=
  iprop([∗list] i ↦ ve ∈ vs, typed_pointsto (array_index_ref V (i : Int) l) ve dq)

include preSem in
theorem array_elems_cons (l : loc) (v : V) (vs : List V) (dq : DFrac) :
    array_elems (GF := GF) l (v :: vs) dq ⊣⊢
      iprop(typed_pointsto (array_index_ref V 0 l) v dq ∗
        array_elems (array_index_ref V 1 l) vs dq) := by
  unfold array_elems
  refine bigSepL_cons.trans ?_
  have h : ∀ k : Nat, array_index_ref V ((k + 1 : Nat) : Int) l =
      array_index_ref V (k : Int) (array_index_ref V 1 l) := by
    intro k
    rw [← go.array_index_ref_add]; congr 1; omega
  simp only [h]
  exact .rfl

include preSem in
theorem array_elems_agree (l : loc) (vs1 vs2 : List V) (dq1 dq2 : DFrac)
    (hlen : vs1.length = vs2.length) :
    array_elems (GF := GF) l vs1 dq1 ⊢ array_elems l vs2 dq2 -∗ ⌜vs1 = vs2⌝ := by
  induction vs1 generalizing l vs2 with
  | nil =>
    cases vs2 with
    | nil => iintro _ _; ipureintro; rfl
    | cons _ _ => simp at hlen
  | cons v1 vs1 ih =>
    cases vs2 with
    | nil => simp at hlen
    | cons v2 vs2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      iintro H1 H2
      icases (array_elems_cons l v1 vs1 dq1).1 $$ H1 with ⟨Hx1, H1⟩
      icases (array_elems_cons l v2 vs2 dq2).1 $$ H2 with ⟨Hx2, H2⟩
      icombine Hx1 Hx2 gives %Heq
      icases ih (array_index_ref V 1 l) vs2 hlen $$ H1 H2 with %Heq'
      ipureintro
      rw [Heq, Heq']

noncomputable instance typed_pointsto_array (n : Int) : TypedPointsto (GF := GF) (array.t V n) where
  typed_pointsto_def l v dq :=
    iprop(⌜(v.arr.length : Int) = n⌝ ∗ array_elems l v.arr dq)
  typed_pointsto_def_dfractional l v := by
    unfold array_elems; infer_instance
  typed_pointsto_def_timeless l v dq := by
    unfold array_elems; infer_instance
  typed_pointsto_agree l dq1 dq2 v1 v2 := by
    obtain ⟨vs1⟩ := v1
    obtain ⟨vs2⟩ := v2
    iintro ⟨%Hlen1, H1⟩ ⟨%Hlen2, H2⟩
    icases array_elems_agree l vs1 vs2 dq1 dq2 (by simp at Hlen1 Hlen2; omega) $$ H1 H2 with %Heq
    ipureintro
    rw [Heq]

theorem array_len (ptr : loc) (dq : DFrac) (n : Int) (vs : List V) :
    typed_pointsto (GF := GF) ptr (array.mk n vs) dq ⊢ ⌜n = (vs.length : Int)⌝ := by
  rw [typed_pointsto_unseal]; unfold typed_pointsto_wrap
  simp only [TypedPointsto.typed_pointsto_def]
  iintro ⟨⟨%H, _⟩, _⟩
  ipureintro
  exact H.symm

theorem array_empty (ptr : loc) (dq : DFrac) (h : ptr ≠ null) :
    ⊢ typed_pointsto (GF := GF) ptr (array.mk 0 ([] : List V)) dq := by
  rw [typed_pointsto_unseal]; unfold typed_pointsto_wrap
  simp only [TypedPointsto.typed_pointsto_def]
  isplit
  · isplit
    · ipureintro; rfl
    · unfold array_elems; iapply bigSepL_nil.2; iempintro
  · ipureintro; exact h

theorem array_acc (p : loc) (i : Int) (dq : DFrac) (n : Int) (a : array.t V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typed_pointsto (GF := GF) p a dq ⊢
      iprop(typed_pointsto (array_index_ref V i p) v dq ∗
        (∀ v', typed_pointsto (array_index_ref V i p) v' dq -∗
          typed_pointsto p (array.mk n (a.arr.set i.toNat v')) dq)) := by
  iintro Harr
  icases typed_pointsto_not_null_dup _ _ _ $$ Harr with ⟨Harr, %Hnn⟩
  icases typed_pointsto_split _ _ _ $$ Harr with Harr
  simp only [TypedPointsto.typed_pointsto_def]
  icases Harr with ⟨%Hlen, Harr⟩
  unfold array_elems
  icases bigSepL_insert_acc (Φ := fun (k : Nat) (ve : V) =>
      typed_pointsto (GF := GF) (array_index_ref V (k : Int) p) ve dq) hlookup $$ Harr
    with ⟨Hptsto, Harr⟩
  have hi : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hpos
  simp only [hi]
  iframe Hptsto
  iintro %v' Hptsto
  ihave Harr := Harr $$ %v' [Hptsto]
  · iexact Hptsto
  iapply typed_pointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typed_pointsto_def]
  isplit
  · ipureintro; simp [Hlen]
  · iexact Harr

include preSem in
theorem array_elems_app (l : loc) (vs1 vs2 : List V) (dq : DFrac) :
    array_elems (GF := GF) l (vs1 ++ vs2) dq ⊣⊢
      iprop(array_elems l vs1 dq ∗
        array_elems (array_index_ref V (vs1.length : Int) l) vs2 dq) := by
  unfold array_elems
  refine bigSepL_append.trans ?_
  have h : ∀ k : Nat, array_index_ref V ((k + vs1.length : Nat) : Int) l =
      array_index_ref V (k : Int) (array_index_ref V (vs1.length : Int) l) := by
    intro k
    rw [← go.array_index_ref_add]; congr 1; omega
  simp only [h]
  exact .rfl

include preSem in
theorem array_split (k : w64) (l : loc) (dq : DFrac) (n : Int) (a : array.t V n)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ n) :
    typed_pointsto (GF := GF) l a dq ⊣⊢
      iprop(typed_pointsto l (array.mk (sint.Z k) (a.arr.take (sint.nat k))) dq ∗
        typed_pointsto (array_index_ref V (sint.Z k) l)
          (array.mk (n - sint.Z k) (a.arr.drop (sint.nat k))) dq) := by
  obtain ⟨arr⟩ := a
  have hk' : ((sint.nat k : Nat) : Int) = sint.Z k := by word
  have e := array_elems_app (GF := GF) l (arr.take (sint.nat k)) (arr.drop (sint.nat k)) dq
  rw [List.take_append_drop] at e
  rw [typed_pointsto_unseal]; unfold typed_pointsto_wrap
  simp only [TypedPointsto.typed_pointsto_def]
  constructor
  · iintro ⟨⟨%Hlen, H⟩, %Hnn⟩
    have Hl : (arr.take (sint.nat k)).length = sint.nat k := by
      simp only [List.length_take]; omega
    rw [Hl, hk'] at e
    icases e.1 $$ H with ⟨H1, H2⟩
    iframe H1 H2
    have Hnn' : array_index_ref V (sint.Z k) l ≠ null :=
      fun h => Hnn (go.array_index_ref_null_inv _ _ _ h)
    repeat' (first | (ipureintro; first | exact Hnn | exact Hnn' | (simp at Hlen ⊢; omega)) | isplit)
  · iintro ⟨⟨⟨%Hlen1, H1⟩, %Hnn⟩, ⟨⟨%Hlen2, H2⟩, _⟩⟩
    simp only [List.length_take, List.length_drop] at Hlen1 Hlen2 ⊢
    have Hl : (arr.take (sint.nat k)).length = sint.nat k := by
      simp only [List.length_take]; omega
    rw [Hl, hk'] at e
    ihave H := e.2 $$ [H1 H2]
    · iframe H1 H2
    iframe H
    isplit
    · ipureintro; omega
    · ipureintro; exact Hnn

end lemmas

section into_val
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

instance into_val_typed_array (t : go.type) [IntoValTyped (GF := GF) V t] (n : Int) :
    IntoValTypedUnderlying (GF := GF) (array.t V n) (go.ArrayType n t) :=
  sorry -- Rocq: Admitted

end into_val

end Perennial
