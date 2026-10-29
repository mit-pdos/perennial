/-
Shared definitions of the proofs of the `unsafememory` page helpers (`page.go`): the inodes a page
holds (`InodeM`), the bytes of a leaf or branch page laid out by `writeInodeToPage` (`pageBody`),
the ownership of an `[]inode` (`inodesOwn`), and byte points-to lemmas (bounds, persistence,
byte slices over a byte points-to).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Layout

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-! ## The layout of a page -/

section model
variable [GooseExts]

/-- An inode as a page stores it: flags, page id, key and value bytes. -/
structure InodeM where
  flags : w32
  pgid : w64
  key : List w8
  value : List w8
deriving DecidableEq

/-- The bytes of an inode's key and value, as they are laid out in the data area. -/
def InodeM.kv (m : InodeM) : List w8 := m.key ++ m.value

/-- The data area of a page: each inode's key and value, in order. -/
def dataBytes (ms : List InodeM) : List w8 := ms.flatMap InodeM.kv

/-- The offset (from the page) of inode `i`'s key: after the header, the elements and the earlier
inodes' data. -/
def dataOff (ms : List InodeM) (i : Nat) : Nat :=
  16 + 16 * ms.length + (dataBytes (ms.take i)).length

/-- The leaf elements `writeInodeToPage` writes: element `i` is at `16 + 16 i`, and its key `pos`
bytes past it. -/
def leafElems (ms : List InodeM) : List leafPageElement :=
  ms.mapIdx fun i m => ⟨m.flags, W32 ((dataOff ms i - (16 + 16 * i) : Nat) : Int),
    W32 (m.key.length : Int), W32 (m.value.length : Int)⟩

/-- The branch elements `writeInodeToPage` writes. -/
def branchElems (ms : List InodeM) : List branchPageElement :=
  ms.mapIdx fun i m => ⟨W32 ((dataOff ms i - (16 + 16 * i) : Nat) : Int),
    W32 (m.key.length : Int), m.pgid⟩

/-- The bytes of the elements of a leaf or a branch page. -/
def elemBytes (leaf : Bool) (ms : List InodeM) : List w8 :=
  if leaf then (leafElems ms).flatMap encode else (branchElems ms).flatMap encode

/-- The bytes of a page after its header: the elements, then the data area. -/
def pageBody (leaf : Bool) (ms : List InodeM) : List w8 := elemBytes leaf ms ++ dataBytes ms

/-- Whether a page header says the page is a leaf (`p.flags&leafPageFlag != 0`). -/
def pageIsLeaf (hdr : Page) : Bool := decide (hdr.flags' &&& W16 2 ≠ W16 0)

/-- What `readInodeFromPage` reads back from a page holding `ms`: a leaf page does not store page
ids, a branch page neither flags nor values. -/
def readBack (leaf : Bool) (ms : List InodeM) : List InodeM :=
  if leaf then ms.map fun m => { m with pgid := 0 }
  else ms.map fun m => { m with flags := 0, value := [] }

/-- A page can hold `ms`: the count fits a `uint16`, offsets a `uint32`, and keys are not empty
(as in bbolt). -/
def pageFits (ms : List InodeM) : Prop :=
  ms.length < 2 ^ 16 ∧ 16 + (pageBody true ms).length < 2 ^ 32 ∧ ∀ m ∈ ms, m.key ≠ []

/-- The header `writeLeaf` leaves on a zeroed page. -/
def leafHeader (ms : List InodeM) : Page := ⟨0, W16 2, W16 (ms.length : Int), 0⟩

/-- The inodes of `leafInodes()`. -/
def leafModel : List InodeM :=
  [⟨0, 0, go!"apple", go!"1"⟩, ⟨0, 0, go!"banana", go!"22"⟩, ⟨0, 0, go!"cherry", []⟩]

theorem flatMap_encode_length' {V : Type} {n : Nat} [ByteEncoding V n] (vs : List V) :
    (vs.flatMap encode).length = vs.length * n := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp [List.flatMap_cons, ih, ByteEncoding.encode_length, Nat.succ_mul]; omega

theorem leafElems_length (ms : List InodeM) : (leafElems ms).length = ms.length := by
  simp [leafElems]

theorem branchElems_length (ms : List InodeM) : (branchElems ms).length = ms.length := by
  simp [branchElems]

theorem elemBytes_length (leaf : Bool) (ms : List InodeM) :
    (elemBytes leaf ms).length = 16 * ms.length := by
  unfold elemBytes
  split
  · rw [flatMap_encode_length', leafElems_length]; omega
  · rw [flatMap_encode_length', branchElems_length]; omega

theorem dataBytes_take_succ (ms : List InodeM) (i : Nat) (h : i < ms.length) :
    dataBytes (ms.take (i + 1)) = dataBytes (ms.take i) ++ ms[i].kv := by
  simp only [dataBytes, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton]

theorem dataBytes_length_le (ms : List InodeM) (i : Nat) :
    (dataBytes (ms.take i)).length ≤ (dataBytes ms).length := by
  conv => rhs; rw [← List.take_append_drop i ms]
  simp only [dataBytes, List.flatMap_append, List.length_append]
  omega

/-- The data of inode `i` in the data area. -/
theorem dataBytes_drop_take (ms : List InodeM) (i : Nat) (h : i < ms.length) :
    ((dataBytes ms).drop (dataBytes (ms.take i)).length).take ms[i].kv.length = ms[i].kv := by
  have e : dataBytes ms = dataBytes (ms.take i) ++ ms[i].kv ++ dataBytes (ms.drop (i + 1)) := by
    conv => lhs; rw [← List.take_append_drop (i + 1) ms]
    rw [show dataBytes (ms.take (i + 1) ++ ms.drop (i + 1)) =
      dataBytes (ms.take (i + 1)) ++ dataBytes (ms.drop (i + 1)) by
        simp only [dataBytes, List.flatMap_append],
      dataBytes_take_succ ms i h]
  rw [e, List.append_assoc, List.drop_left, List.take_left]

theorem take_drop_append_left {α : Type} (A B : List α) (k n : Nat) (h : k + n ≤ A.length) :
    ((A ++ B).drop k).take n = (A.drop k).take n := by
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- Element `i` of the elements of a page. -/
theorem elems_take_drop {V : Type} [ByteEncoding V 16] (es : List V) (B : List w8) (i : Nat)
    (h : i < es.length) : ((es.flatMap encode ++ B).drop (16 * i)).take 16 = encode es[i] := by
  rw [take_drop_append_left _ _ _ _ (by rw [flatMap_encode_length']; omega), Nat.mul_comm,
    flatMap_encode_take_drop _ _ h]

/-- Element `i` of the leaf elements in a page's bytes. -/
theorem pageBody_leaf_elem (ms : List InodeM) (tail : List w8) (i : Nat) (h : i < ms.length) :
    ((pageBody true ms ++ tail).drop (16 * i)).take 16 =
      encode ((leafElems ms)[i]'(by rw [leafElems_length]; exact h)) := by
  simp only [pageBody, elemBytes, ite_true, List.append_assoc]
  exact elems_take_drop _ _ _ _

/-- Element `i` of the branch elements in a page's bytes. -/
theorem pageBody_branch_elem (ms : List InodeM) (tail : List w8) (i : Nat) (h : i < ms.length) :
    ((pageBody false ms ++ tail).drop (16 * i)).take 16 =
      encode ((branchElems ms)[i]'(by rw [branchElems_length]; exact h)) := by
  simp only [pageBody, elemBytes, Bool.false_eq_true, ite_false, List.append_assoc]
  exact elems_take_drop _ _ _ _

/-- The key and value of inode `i` in a page's bytes (from the end of the header). -/
theorem pageBody_kv (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat)
    (h : i < ms.length) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16)).take ms[i].kv.length = ms[i].kv := by
  have hd : dataOff ms i - 16 = (elemBytes leaf ms).length + (dataBytes (ms.take i)).length := by
    simp only [dataOff, elemBytes_length]; omega
  have hle : (dataBytes (ms.take i)).length + ms[i].kv.length ≤ (dataBytes ms).length := by
    have := dataBytes_length_le ms (i + 1)
    rw [dataBytes_take_succ ms i h, List.length_append] at this
    exact this
  rw [hd, pageBody, List.append_assoc, ← List.drop_drop, List.drop_left,
    take_drop_append_left _ _ _ _ hle, dataBytes_drop_take ms i h]

/-- Writing element `i` of `es` over zeros. -/
theorem elems_step {V : Type} [ByteEncoding V 16] (es : List V) (i : Nat) (h : i < es.length)
    (C : List w8) :
    replaceBytes ((es.take i).flatMap encode ++ List.replicate (16 * (es.length - i)) 0 ++ C)
        (16 * i) (encode es[i]) =
      (es.take (i + 1)).flatMap encode ++ List.replicate (16 * (es.length - (i + 1))) 0 ++ C := by
  have hA : ((es.take i).flatMap encode).length = 16 * i := by
    rw [flatMap_encode_length', List.length_take]; rw [Nat.min_eq_left (by omega)]; omega
  have he : (encode es[i]).length = 16 := ByteEncoding.encode_length _
  have hR : List.replicate (16 * (es.length - i)) (0 : w8) =
      List.replicate 16 0 ++ List.replicate (16 * (es.length - (i + 1))) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  have e1 : ((es.take i).flatMap encode ++ List.replicate (16 * (es.length - i)) 0 ++ C).take
      (16 * i) = (es.take i).flatMap encode := by
    rw [List.append_assoc, List.take_left' hA]
  have e2 : ((es.take i).flatMap encode ++ List.replicate (16 * (es.length - i)) 0 ++ C).drop
      (16 * i + 16) = List.replicate (16 * (es.length - (i + 1))) 0 ++ C := by
    rw [List.append_assoc, ← List.drop_drop, ← hA, List.drop_left, hR, List.append_assoc,
      List.drop_left' (by simp)]
  unfold replaceBytes
  rw [he, e1, e2, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton, List.append_assoc, List.append_assoc,
    List.append_assoc]

/-- The elements written by the first `j` iterations of `writeInodeToPage`. -/
def elemsPrefix (leaf : Bool) (ms : List InodeM) (j : Nat) : List w8 :=
  if leaf then ((leafElems ms).take j).flatMap encode else ((branchElems ms).take j).flatMap encode

theorem elemsPrefix_zero (leaf : Bool) (ms : List InodeM) : elemsPrefix leaf ms 0 = [] := by
  unfold elemsPrefix; split <;> simp

theorem elemsPrefix_length (leaf : Bool) (ms : List InodeM) (j : Nat) (h : j ≤ ms.length) :
    (elemsPrefix leaf ms j).length = 16 * j := by
  unfold elemsPrefix
  split
  · rw [flatMap_encode_length', List.length_take, leafElems_length, Nat.min_eq_left h, Nat.mul_comm]
  · rw [flatMap_encode_length', List.length_take, branchElems_length, Nat.min_eq_left h,
      Nat.mul_comm]

theorem elemsPrefix_full (leaf : Bool) (ms : List InodeM) :
    elemsPrefix leaf ms ms.length = elemBytes leaf ms := by
  unfold elemsPrefix elemBytes
  split
  · rw [List.take_of_length_le (by rw [leafElems_length]; exact Nat.le_refl _)]
  · rw [List.take_of_length_le (by rw [branchElems_length]; exact Nat.le_refl _)]

theorem leafElems_getElem (ms : List InodeM) (j : Nat) (h : j < (leafElems ms).length) :
    (leafElems ms)[j] = ⟨(ms[j]'(by rw [leafElems_length] at h; exact h)).flags,
      W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 ((ms[j]'(by rw [leafElems_length] at h; exact h)).key.length : Int),
      W32 ((ms[j]'(by rw [leafElems_length] at h; exact h)).value.length : Int)⟩ := by
  simp [leafElems, List.getElem_mapIdx]

theorem branchElems_getElem (ms : List InodeM) (j : Nat) (h : j < (branchElems ms).length) :
    (branchElems ms)[j] = ⟨W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 ((ms[j]'(by rw [branchElems_length] at h; exact h)).key.length : Int),
      (ms[j]'(by rw [branchElems_length] at h; exact h)).pgid⟩ := by
  simp [branchElems, List.getElem_mapIdx]

theorem leafElems_getElem' (ms : List InodeM) (j : Nat) (m : InodeM) (hm : ms[j]? = some m)
    (h : j < (leafElems ms).length) :
    (leafElems ms)[j] = ⟨m.flags, W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 (m.key.length : Int), W32 (m.value.length : Int)⟩ := by
  rw [leafElems_getElem]
  have : ms[j]'(by rw [leafElems_length] at h; exact h) = m := by
    rw [List.getElem?_eq_getElem (by simpa [leafElems_length, branchElems_length] using h)] at hm
    exact Option.some.inj hm
  rw [this]

theorem branchElems_getElem' (ms : List InodeM) (j : Nat) (m : InodeM) (hm : ms[j]? = some m)
    (h : j < (branchElems ms).length) :
    (branchElems ms)[j] = ⟨W32 ((dataOff ms j - (16 + 16 * j) : Nat) : Int),
      W32 (m.key.length : Int), m.pgid⟩ := by
  rw [branchElems_getElem]
  have : ms[j]'(by rw [branchElems_length] at h; exact h) = m := by
    rw [List.getElem?_eq_getElem (by simpa [leafElems_length, branchElems_length] using h)] at hm
    exact Option.some.inj hm
  rw [this]

theorem elemsPrefix_step_leaf (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    replaceBytes (elemsPrefix true ms j ++ List.replicate (16 * (ms.length - j)) 0) (16 * j)
        (encode ((leafElems ms)[j]'(by rw [leafElems_length]; exact h))) =
      elemsPrefix true ms (j + 1) ++ List.replicate (16 * (ms.length - (j + 1))) 0 := by
  have := elems_step (leafElems ms) j (by rw [leafElems_length]; exact h) []
  simp only [List.append_nil, leafElems_length] at this
  simpa [elemsPrefix] using this

theorem elemsPrefix_step_branch (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    replaceBytes (elemsPrefix false ms j ++ List.replicate (16 * (ms.length - j)) 0) (16 * j)
        (encode ((branchElems ms)[j]'(by rw [branchElems_length]; exact h))) =
      elemsPrefix false ms (j + 1) ++ List.replicate (16 * (ms.length - (j + 1))) 0 := by
  have := elems_step (branchElems ms) j (by rw [branchElems_length]; exact h) []
  simp only [List.append_nil, branchElems_length] at this
  simpa [elemsPrefix] using this

theorem dataOff_succ (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    dataOff ms (j + 1) = dataOff ms j + ms[j].kv.length := by
  simp only [dataOff, dataBytes_take_succ ms j h, List.length_append]; omega

theorem dataOff_le (ms : List InodeM) (j : Nat) (h : j < ms.length) :
    dataOff ms j + ms[j].kv.length ≤ 16 + (pageBody true ms).length := by
  rw [← dataOff_succ ms j h]
  have := dataBytes_length_le ms (j + 1)
  simp only [dataOff, pageBody, List.length_append, elemBytes_length]; omega

theorem pageBody_length (leaf : Bool) (ms : List InodeM) :
    (pageBody leaf ms).length = 16 * ms.length + (dataBytes ms).length := by
  simp [pageBody, elemBytes_length]

theorem getElem_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    ∃ hi : i < l.length, l[i] = a := by
  rw [List.getElem?_eq_some_iff] at h; exact h

/-- The key of inode `m = ms[i]` in a page's bytes (from the end of the header). -/
theorem pageBody_key (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat) (m : InodeM)
    (hm : ms[i]? = some m) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16)).take m.key.length = m.key := by
  obtain ⟨hi, rfl⟩ := getElem_of_getElem? hm
  have h := congrArg (List.take ms[i].key.length) (pageBody_kv leaf ms tail i hi)
  rw [List.take_take, Nat.min_eq_left (by simp [InodeM.kv])] at h
  rw [h]; simp [InodeM.kv]

/-- The value of inode `m = ms[i]` in a page's bytes (from the end of the header). -/
theorem pageBody_value (leaf : Bool) (ms : List InodeM) (tail : List w8) (i : Nat) (m : InodeM)
    (hm : ms[i]? = some m) :
    ((pageBody leaf ms ++ tail).drop (dataOff ms i - 16 + m.key.length)).take m.value.length =
      m.value := by
  obtain ⟨hi, rfl⟩ := getElem_of_getElem? hm
  have h := congrArg (List.drop ms[i].key.length) (pageBody_kv leaf ms tail i hi)
  rw [List.drop_take] at h
  rw [← List.drop_drop]
  have hl : ms[i].kv.length - ms[i].key.length = ms[i].value.length := by simp [InodeM.kv]
  rw [hl] at h
  rw [h]; simp [InodeM.kv]

/-- The bytes of inode `m = ms[i]` end inside a page's bytes. -/
theorem dataOff_le' (ms : List InodeM) (i : Nat) (m : InodeM) (hm : ms[i]? = some m) :
    dataOff ms i + m.key.length + m.value.length ≤ 16 + (pageBody true ms).length := by
  obtain ⟨hi, rfl⟩ := getElem_of_getElem? hm
  have := dataOff_le ms i hi
  simp only [InodeM.kv, List.length_append] at this; omega

theorem dataOff_ge (ms : List InodeM) (i : Nat) : 16 + 16 * ms.length ≤ dataOff ms i := by
  simp [dataOff]

theorem set_append_replicate {α : Type} (xs : List α) (k : Nat) (z v : α) (hk : 0 < k) :
    (xs ++ List.replicate k z).set xs.length v = (xs ++ [v]) ++ List.replicate (k - 1) z := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ,
    List.set_cons_zero]
  simp

theorem readBack_length (leaf : Bool) (ms : List InodeM) : (readBack leaf ms).length = ms.length := by
  unfold readBack; split <;> simp

theorem readBack_leaf_getElem? (ms : List InodeM) (i : Nat) (m : InodeM) (hm : ms[i]? = some m) :
    (readBack true ms)[i]? = some { m with pgid := 0 } := by
  simp [readBack, hm]

theorem readBack_branch_getElem? (ms : List InodeM) (i : Nat) (m : InodeM) (hm : ms[i]? = some m) :
    (readBack false ms)[i]? = some { m with flags := 0, value := [] } := by
  simp [readBack, hm]

theorem take_succ_of_getElem? {α : Type} (l : List α) (i : Nat) (a : α) (h : l[i]? = some a) :
    l.take (i + 1) = l.take i ++ [a] := by
  rw [List.take_add_one, h]; rfl

/-- A word read as a non-negative natural number is that number's word. -/
theorem w64_of_sint_nat (w : w64) (n : Nat) (h : n = sint.nat w) (h0 : 0 ≤ sint.Z w) :
    w = W64 (n : Int) := by
  have hlt : sint.Z w < 2 ^ 63 := by have := w.toInt_lt; simp only [sint.Z]; omega
  simp only [sint.nat, sint.Z] at h h0 hlt
  apply BitVec.eq_of_toInt_eq
  rw [show (W64 (n : Int)).toInt = n from sint_Z_W64_nat _ (by omega)]
  omega

end model

/-! ## Byte points-tos -/

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open ProofMode

/-- The bytes of a non-empty byte points-to lie in `(0, maxAddr]`. -/
theorem bytesPointsto_bounds (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %H3
      ipureintro
      simp only [Loc.add, List.length_cons] at H3 ⊢
      omega

/-- `bytesPointsto_bounds` for bytes that may be empty. -/
theorem bytesPointsto_bounds_imp (l : Loc) (dq : DFrac) (bs : List w8) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜bs ≠ [] → 0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  by_cases h : bs = []
  · iintro _; ipureintro; intro h'; exact absurd h h'
  · iintro H
    icases bytesPointsto_bounds l dq bs h $$ H with %Hb
    ipureintro; intro _; exact Hb

instance bytesPointsto_discard_persistent (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l .discard bs) := by
  induction bs generalizing l <;> unfold bytesPointsto <;> infer_instance

theorem bytesPointsto_persist (l : Loc) (dq : DFrac) (bs : List w8) :
    bytesPointsto (GF := GF) l dq bs ⊢ |==> bytesPointsto l .discard bs := by
  induction bs generalizing l with
  | nil => unfold bytesPointsto; iintro _; imodintro; itrivial
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    imod heapPointsto_persist l dq _ $$ Hb with Hb
    imod ih (l +ₗ 1) $$ Hbs with Hbs
    imodintro
    iframe

/-- A typed points-to of an equal value. -/
theorem typedPointsto_of_eq {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v w : V) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ∗ ⌜v = w⌝ ⊢ typedPointsto l w dq := by
  iintro ⟨H, %h⟩
  rw [← h]
  iexact H

/-- A sub-range of persistent bytes. -/
theorem bytesPointsto_sub (l : Loc) (B X : List w8) (k : Nat) (hk : k + X.length ≤ B.length)
    (h : (B.drop k).take X.length = X) :
    bytesPointsto (GF := GF) l .discard B ⊢ bytesPointsto (l +ₗ (k : Int)) .discard X := by
  have e : B = B.take k ++ ((B.drop k).take X.length ++ (B.drop k).drop X.length) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hk' : (B.take k).length = k := by simp; omega
  iintro HB
  rw [e]
  icases (bytesPointsto_app l _ _ _).1 $$ HB with ⟨-, HB⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ HB with ⟨HX, -⟩
  rw [hk', h]
  iexact HX

/-- A byte points-to from a positive address is a byte slice there. -/
theorem bytesPointsto_ownSlice (l : Loc) (dq : DFrac) (bs : List w8) (hl : 0 < l.addr)
    (hlen : bs.length < 2 ^ 63) :
    bytesPointsto (GF := GF) l dq bs ⊣⊢
      slice.mk l (W64 (bs.length : Int)) (W64 (bs.length : Int)) ↦*{dq} bs := by
  have hz : sint.Z (W64 (bs.length : Int)) = bs.length := sint_Z_W64_nat _ hlen
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  rw [ownSlice_unseal]; unfold ownSliceDef
  dsimp only
  rw [hz]
  by_cases hbs : bs = []
  · subst hbs
    constructor
    · iintro _
      iright
      isplitl
      · iapply array_empty _ _ hnn
      · ipureintro; omega
    · iintro _; unfold bytesPointsto; itrivial
  · have ha := typedPointsto_byte_array (GF := GF) l (bs.length : Int) (array.mk _ bs) dq hbs
    constructor
    · iintro H
      iright
      isplitl
      · iapply ha.2; iframe H; ipureintro; rfl
      · ipureintro; omega
    · iintro (%H | ⟨H, _⟩)
      · exfalso; apply hnn; have := congrArg GoSlice.ptr H.1; simpa [slice.nil] using this
      · icases ha.1 $$ H with ⟨_, H⟩
        iexact H

end bytes

/-! ## Inodes -/

section inodes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The inode `x` holds `m`; its key and value are read-only. -/
def inodeOwn (x : inode) (m : InodeM) : IProp GF :=
  iprop(⌜x.flags' = m.flags ∧ x.pgid' = m.pgid⌝ ∗ x.key' ↦*□ m.key ∗ x.value' ↦*□ m.value)

/-- The `[]inode` `s` holds `ms`, read-only. -/
def inodesOwn (s : GoSlice) (ms : List InodeM) : IProp GF :=
  iprop(∃ xs : List inode, s ↦*□ xs ∗ [∗list] x;m ∈ xs;ms, inodeOwn x m)

instance inodeOwn_persistent (x : inode) (m : InodeM) : Persistent (inodeOwn (GF := GF) x m) := by
  unfold inodeOwn; infer_instance

instance inodesOwn_persistent (s : GoSlice) (ms : List InodeM) :
    Persistent (inodesOwn (GF := GF) s ms) := by
  unfold inodesOwn
  have : ∀ xs : List inode, Persistent ([∗list] x;m ∈ xs;ms, inodeOwn (GF := GF) x m) :=
    fun _ => BigSepL2.bigSepL2_persistent (fun _ _ _ _ _ => inferInstance)
  infer_instance

end inodes

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

end Perennial
