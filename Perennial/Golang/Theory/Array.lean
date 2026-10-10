/-
The typed points-to for arrays (`l ↦{dq} (a : GoArray V n)` is the points-to
of every element at `arrayIndexRef V i l`), and lemmas to access and split it.

`intoVal_typed_array` relies on the guarded, element-wise `go.store_array` of
`Perennial/Golang/Defn/Array.lean` (see there).
-/
module

public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Defn.Array

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std BigSepL

/-- `go.index_ref_array` with the `ZeroVal V` instance determined by
`TypeRepr elem_type V` (see `go_zero_val_step'`). -/
instance (priority := high) index_ref_array' [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (n : Int) (elem_type : go.GoType) (i : w64) (l : Loc)
    {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦IndexRef (go.ArrayType n elem_type), (#l, #i)⟧ ⤳[under]
      (if sint.Z i < n then #(arrayIndexRef V (sint.Z i) l) else Panic "index out of range") :=
  go.index_ref_array n elem_type i l

instance (priority := high) slice_array_step' [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] [go.PreSemantics] (n : Int) (elem_type : go.GoType) (p : Loc)
    (low high : w64) {V : Type} {zv : ZeroVal V} [TypeRepr elem_type V] :
    ⟦Slice (go.ArrayType n elem_type), (#p, #low, #high)⟧ ⤳
       (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ n then
          #(slice.mk (arrayIndexRef V (sint.Z low) p) (high - low) (W64 n - low))
        else Panic "slice bounds out of range") :=
  go.slice_array_step n elem_type p low high

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- The element points-tos of a list of values starting at `l`. -/
abbrev arrayElems (l : Loc) (vs : List V) (dq : DFrac) : IProp GF :=
  iprop([∗list] i ↦ ve ∈ vs, typedPointsto (arrayIndexRef V (i : Int) l) ve dq)

include preSem in
theorem arrayElems_cons (l : Loc) (v : V) (vs : List V) (dq : DFrac) :
    arrayElems (GF := GF) l (v :: vs) dq ⊣⊢
      iprop(typedPointsto (arrayIndexRef V 0 l) v dq ∗
        arrayElems (arrayIndexRef V 1 l) vs dq) := by
  unfold arrayElems
  refine bigSepL_cons.trans ?_
  have h : ∀ k : Nat, arrayIndexRef V ((k + 1 : Nat) : Int) l =
      arrayIndexRef V (k : Int) (arrayIndexRef V 1 l) := by
    intro k
    rw [← go.arrayIndexRef_add]; congr 1; omega
  simp only [h]
  exact .rfl

include preSem in
theorem arrayElems_agree (l : Loc) (vs1 vs2 : List V) (dq1 dq2 : DFrac)
    (hlen : vs1.length = vs2.length) :
    arrayElems (GF := GF) l vs1 dq1 ⊢ arrayElems l vs2 dq2 -∗ ⌜vs1 = vs2⌝ := by
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
      icases (arrayElems_cons l v1 vs1 dq1).1 $$ H1 with ⟨Hx1, H1⟩
      icases (arrayElems_cons l v2 vs2 dq2).1 $$ H2 with ⟨Hx2, H2⟩
      icombine Hx1 Hx2 gives %Heq
      icases ih (arrayIndexRef V 1 l) vs2 hlen $$ H1 H2 with %Heq'
      ipureintro
      rw [Heq, Heq']

noncomputable instance typedPointsto_array (n : Int) : TypedPointsto (GF := GF) (GoArray V n) where
  typedPointstoDef l v dq :=
    iprop(⌜(v.arr.length : Int) = n⌝ ∗ arrayElems l v.arr dq)
  typedPointstoDef_dfractional l v := by
    unfold arrayElems; infer_instance
  typedPointstoDef_timeless l v dq := by
    unfold arrayElems; infer_instance
  typedPointsto_agree l dq1 dq2 v1 v2 := by
    obtain ⟨vs1⟩ := v1
    obtain ⟨vs2⟩ := v2
    iintro ⟨%Hlen1, H1⟩ ⟨%Hlen2, H2⟩
    icases arrayElems_agree l vs1 vs2 dq1 dq2 (by simp at Hlen1 Hlen2; omega) $$ H1 H2 with %Heq
    ipureintro
    rw [Heq]

theorem array_len (ptr : Loc) (dq : DFrac) (n : Int) (vs : List V) :
    typedPointsto (GF := GF) ptr (array.mk n vs) dq ⊢ ⌜n = (vs.length : Int)⌝ := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  iintro ⟨⟨%H, _⟩, _⟩
  ipureintro
  exact H.symm

theorem array_empty (ptr : Loc) (dq : DFrac) (h : ptr ≠ null) :
    ⊢ typedPointsto (GF := GF) ptr (array.mk 0 ([] : List V)) dq := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  isplit
  · isplit
    · ipureintro; rfl
    · unfold arrayElems; iapply bigSepL_nil.2; iempintro
  · ipureintro; exact h

theorem array_acc (p : Loc) (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (∀ v', typedPointsto (arrayIndexRef V i p) v' dq -∗
          typedPointsto p (array.mk n (a.arr.set i.toNat v')) dq)) := by
  iintro Harr
  icases typedPointsto_not_null_dup _ _ _ $$ Harr with ⟨Harr, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Harr with Harr
  simp only [TypedPointsto.typedPointstoDef]
  icases Harr with ⟨%Hlen, Harr⟩
  unfold arrayElems
  icases bigSepL_insert_acc (Φ := fun (k : Nat) (ve : V) =>
      typedPointsto (GF := GF) (arrayIndexRef V (k : Int) p) ve dq) hlookup $$ Harr
    with ⟨Hptsto, Harr⟩
  have hi : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hpos
  simp only [hi]
  iframe Hptsto
  iintro %v' Hptsto
  ihave Harr := Harr $$ %v' [Hptsto]
  · iexact Hptsto
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  isplit
  · ipureintro; simp [Hlen]
  · iexact Harr

include preSem in
theorem arrayElems_app (l : Loc) (vs1 vs2 : List V) (dq : DFrac) :
    arrayElems (GF := GF) l (vs1 ++ vs2) dq ⊣⊢
      iprop(arrayElems l vs1 dq ∗
        arrayElems (arrayIndexRef V (vs1.length : Int) l) vs2 dq) := by
  unfold arrayElems
  refine bigSepL_append.trans ?_
  have h : ∀ k : Nat, arrayIndexRef V ((k + vs1.length : Nat) : Int) l =
      arrayIndexRef V (k : Int) (arrayIndexRef V (vs1.length : Int) l) := by
    intro k
    rw [← go.arrayIndexRef_add]; congr 1; omega
  simp only [h]
  exact .rfl

include preSem in
theorem array_split (k : w64) (l : Loc) (dq : DFrac) (n : Int) (a : GoArray V n)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ n) :
    typedPointsto (GF := GF) l a dq ⊣⊢
      iprop(typedPointsto l (array.mk (sint.Z k) (a.arr.take (sint.nat k))) dq ∗
        typedPointsto (arrayIndexRef V (sint.Z k) l)
          (array.mk (n - sint.Z k) (a.arr.drop (sint.nat k))) dq) := by
  obtain ⟨arr⟩ := a
  have hk' : ((sint.nat k : Nat) : Int) = sint.Z k := by word
  have e := arrayElems_app (GF := GF) l (arr.take (sint.nat k)) (arr.drop (sint.nat k)) dq
  rw [List.take_append_drop] at e
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  constructor
  · iintro ⟨⟨%Hlen, H⟩, %Hnn⟩
    have Hl : (arr.take (sint.nat k)).length = sint.nat k := by
      simp only [List.length_take]; omega
    rw [Hl, hk'] at e
    icases e.1 $$ H with ⟨H1, H2⟩
    iframe H1 H2
    have Hnn' : arrayIndexRef V (sint.Z k) l ≠ null :=
      fun h => Hnn (go.arrayIndexRef_null_inv _ _ _ h)
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

section intoVal
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

theorem list_take_drop_set {A : Type} (vs R : List A) (k : Nat) (ve : A)
    (hve : vs[k]? = some ve) (hR : k < R.length) :
    (vs.take k ++ R.drop k).set k ve = vs.take (k + 1) ++ R.drop (k + 1) := by
  have hk : k < vs.length := by
    rcases Nat.lt_or_ge k vs.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hve
  have hlt : (vs.take k).length = k := by simp; omega
  rw [List.set_append_right _ _ (by omega), hlt, Nat.sub_self]
  rw [List.drop_eq_getElem_cons hR, List.set_cons_zero]
  rw [List.take_add_one, hve]
  simp

theorem list_set_getElem?_self {A : Type} (vs : List A) (k : Nat) (ve : A)
    (hve : vs[k]? = some ve) : vs.set k ve = vs := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_set]
  split
  · subst_vars
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hve
    simp [h1, h2]
  · rfl

/-- The body of the recursive loop of `go.load_array`. -/
abbrev loadArrayBody (n : Int) (elem_type : go.GoType) (l : val) : Expr :=
  gl(if: "n" =⟨go.int⟩ #(W64 0) then GoZeroVal (go.ArrayType n elem_type) #()
            else let: "array_so_far" := "recur" ("n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) (l, "n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArraySet ("array_so_far", ("n" -⟨go.int⟩ #(W64 1), "elem_val")))

theorem wp_load_array_loop (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : Loc) (dq : DFrac) (vs : List V)
    (hlen : (vs.length : Int) = n) (hn : 0 ≤ n ∧ n < 2^63-1) (m : Nat) (hm : (m : Int) ≤ n) :
    {{ arrayElems (GF := GF) l vs dq }}
      (App (Val (RecV "recur" "n" (loadArrayBody n t #l))) (Val #(W64 m))) @ s; E
    {{ RET #(array.mk n (vs.take m ++ (List.replicate n.toNat (zero_val V)).drop m));
       arrayElems l vs dq }} := by
  induction m with
  | zero =>
    iintro %Φ Hl HΦ
    wp_pures
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    iapply HΦ
    iexact Hl
  | succ k ih =>
    iintro %Φ Hl HΦ
    wp_pures
    have hne : (W64 ((k + 1 : Nat) : Int) = W64 0) = False := by
      apply propext; constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; exact h.elim
    simp only [hne, decide_false]
    wp_pure
    wp_pure
    wp_pure
    have hsub : W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [hsub]
    wp_apply_core ih (by omega) $$ Hl
    iintro Hl
    wp_pures
    have hk : sint.Z (W64 (k : Int)) = (k : Int) := by word
    simp only [hsub, hk]
    simp only [show ((k : Int) < n) = True from eq_true (by omega), ↓reduceIte]
    obtain ⟨ve, hve⟩ : ∃ ve, vs[k]? = some ve :=
      ⟨vs[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    unfold arrayElems
    icases bigSepL_insert_acc (Φ := fun (j : Nat) (x : V) =>
        typedPointsto (GF := GF) (arrayIndexRef V (j : Int) l) x dq) hve $$ Hl
      with ⟨Hx, Hl⟩
    wp_pures
    wp_apply_core IntoValTyped.wp_load (t := t) _ _ _ $$ Hx
    iintro Hx
    ihave Hl := Hl $$ %ve [Hx]
    · iexact Hx
    wp_pures
    have hk' : sint.nat (W64 (k : Int)) = k := by word
    simp only [hsub, hk']
    rw [list_take_drop_set vs _ k ve hve (by simp; omega), list_set_getElem?_self _ _ _ hve]
    iapply HΦ
    iexact Hl

/-- One step of the loop of `go.store_array`. -/
abbrev storeArrayStep (n : Int) (elem_type : go.GoType) (l v : val) (str_so_far : Expr) (j : Int) :
    Expr :=
  gl(str_so_far ;;
    (let elem_addr := gl(IndexRef (go.ArrayType n elem_type) (l, #(W64 j)))
     let elem_val := gl(Index (go.ArrayType n elem_type) (v, #(W64 j)))
     gl(GoStore elem_type (elem_addr, elem_val))))

/-- The raw cells of elements `k, …, k + m - 1` of an array of `V`s at `l`. -/
noncomputable abbrev rawElems (l : Loc) (k m : Nat) : IProp GF :=
  iprop([∗list] _j ↦ i ∈ List.range' k m,
    rawCells (arrayIndexRef V ((i : Nat) : Int) l) (typeSize V))

theorem arrayIndexRef_zero' (l : Loc) : arrayIndexRef V 0 l = l := by
  unfold arrayIndexRef; split <;> simp

/-- An array's raw cells are its elements' (`l` in a block). -/
theorem rawCells_rawElems (l : Loc) (hc : l.locCar ≠ 0) (n : Nat) :
    rawCells l ((n : Int) * typeSize V) ⊢ rawElems (GF := GF) (V := V) l 0 n := by
  have hs := go.typeSize_nonneg V
  induction n with
  | zero =>
    iintro _
    unfold rawElems
    rw [show List.range' 0 0 = [] from rfl]
    iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    have e := rawCells_add (GF := GF) l ((n : Int) * typeSize V) (typeSize V)
      (Int.mul_nonneg (by omega) hs) hs
    rw [show (n : Int) * typeSize V + typeSize V = ((n + 1 : Nat) : Int) * typeSize V by
      push_cast; rw [Int.add_mul, Int.one_mul]] at e
    iintro H
    icases e.1 $$ H with ⟨H1, H2⟩
    unfold rawElems
    rw [List.range'_concat]
    iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iapply ih $$ H1
    · iapply BigSepL.bigSepL_singleton.2
      rw [arrayIndexRef_of_car _ _ _ hc, show (0 : Nat) + 1 * n = n by omega]
      iexact H2

theorem wp_store_array_loop_raw (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : Loc) (hc : l.locCar ≠ 0) (w : GoArray V n)
    (hwlen : (w.arr.length : Int) = n) (hn : 0 ≤ n ∧ n < 2^63-1) (k : Nat) (hk : (k : Int) ≤ n) :
    ⊢ ∀ Φ, rawElems (GF := GF) (V := V) l 0 n.toNat -∗
      (arrayElems l (w.arr.take k) (DFrac.own 1) ∗ rawElems (V := V) l k (n.toNat - k) -∗ Φ #()) -∗
      WP (List.foldl (storeArrayStep n t #l #w) (#() : Expr)
        ((List.range k).map (fun (i : Nat) => (i : Int)))) @ s; E {{ Φ }} := by
  induction k with
  | zero =>
    iintro %Φ Hl HΦ
    simp only [List.range_zero, List.map_nil, List.foldl_nil, List.take_zero]
    wp_pures
    iapply HΦ
    isplitl []
    · unfold arrayElems; iapply BigSepL.bigSepL_nil.2; itrivial
    · simp only [Nat.sub_zero]; iexact Hl
  | succ k ih =>
    iintro %Φ Hl HΦ
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    wp_apply_core ih (by omega) $$ Hl
    iintro ⟨Hdone, Hrest⟩
    wp_pures
    have hk' : sint.Z (W64 (k : Int)) = (k : Int) := by word
    have hk'' : sint.nat (W64 (k : Int)) = k := by word
    simp only [hk', show ((k : Int) < n) = True from eq_true (by omega), ↓reduceIte]
    obtain ⟨we, hwe⟩ : ∃ we, w.arr[k]? = some we :=
      ⟨w.arr[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    unfold rawElems
    rw [show n.toNat - k = (n.toNat - (k + 1)) + 1 by omega, List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hrest with ⟨Hk, Hrest⟩
    wp_pures
    simp only [hk'', hwe]
    wp_pures
    wp_apply_core wp_store_raw (V := V) (t := t) _ we $$ [Hk]
    · isplitl []
      · ipureintro; rw [arrayIndexRef_car]; exact hc
      · iexact Hk
    iintro Hx
    iapply HΦ
    isplitl [Hdone Hx]
    · rw [List.take_add_one, hwe, Option.toList_some]
      iapply (arrayElems_app l _ [we] _).2
      isplitl [Hdone]
      · iexact Hdone
      · unfold arrayElems
        iapply BigSepL.bigSepL_singleton.2
        rw [List.length_take, Nat.min_eq_left (by omega), Int.natCast_zero, arrayIndexRef_zero']
        iexact Hx
    · iexact Hrest

theorem wp_store_array_loop (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : Loc) (vs : List V) (w : GoArray V n)
    (hlen : (vs.length : Int) = n) (hwlen : (w.arr.length : Int) = n)
    (hn : 0 ≤ n ∧ n < 2^63-1) (k : Nat) (hk : (k : Int) ≤ n) :
    ⊢ ∀ Φ, arrayElems (GF := GF) l vs (DFrac.own 1) -∗
      (arrayElems l (w.arr.take k ++ vs.drop k) (DFrac.own 1) -∗ Φ #()) -∗
      WP (List.foldl (storeArrayStep n t #l #w) (#() : Expr)
        ((List.range k).map (fun (i : Nat) => (i : Int)))) @ s; E {{ Φ }} := by
  induction k with
  | zero =>
    iintro %Φ Hl HΦ
    simp only [List.range_zero, List.map_nil, List.foldl_nil, List.take_zero, List.drop_zero,
      List.nil_append]
    wp_pures
    iapply HΦ
    iexact Hl
  | succ k ih =>
    iintro %Φ Hl HΦ
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    wp_apply_core ih (by omega) $$ Hl
    iintro Hl
    wp_pures
    have hk' : sint.Z (W64 (k : Int)) = (k : Int) := by word
    have hk'' : sint.nat (W64 (k : Int)) = k := by word
    simp only [hk', show ((k : Int) < n) = True from eq_true (by omega), ↓reduceIte]
    obtain ⟨we, hwe⟩ : ∃ we, w.arr[k]? = some we :=
      ⟨w.arr[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ve, hve⟩ : ∃ ve, (w.arr.take k ++ vs.drop k)[k]? = some ve :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    unfold arrayElems
    icases bigSepL_insert_acc (Φ := fun (j : Nat) (x : V) =>
        typedPointsto (GF := GF) (arrayIndexRef V (j : Int) l) x (DFrac.own 1)) hve $$ Hl
      with ⟨Hx, Hl⟩
    wp_pures
    simp only [hk'', hwe]
    wp_pures
    wp_apply_core wp_store _ _ _ $$ Hx
    iintro Hx
    ihave Hl := Hl $$ %we [Hx]
    · iexact Hx
    rw [list_take_drop_set w.arr vs k we hwe (by omega)]
    iapply HΦ
    iexact Hl

theorem intoVal_typed_array_store_raw' (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} {t' : go.GoType} [t' ↓u go.ArrayType n t] (l : Loc)
    (w : GoArray V n) :
    {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l (typeSize (GoArray V n)) : IProp GF) }}
      (App (Val (GoInstruction (GoStore t'))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }} := by
  iintro %Φ ⟨%Hc, Hraw⟩ HΦ
  have _tagged := @go.tagged_internal_inst
  wp_pure
  clear _tagged
  by_cases hn : 0 ≤ n ∧ n < 2^63-1
  case neg =>
    simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = True from
      eq_true (fun h => hn ⟨h.1, h.2.1⟩), ↓reduceIte]
    iapply wp_AngelicExit
  by_cases hwlen : (w.arr.length : Int) = n
  case neg =>
    simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = True from
      eq_true (fun h => hwlen h.2.2), ↓reduceIte]
    iapply wp_AngelicExit
  simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = False from
      eq_false (fun h => h ⟨hn.1, hn.2, hwlen⟩), ↓reduceIte]
  have e : n * typeSize V = ((n.toNat : Nat) : Int) * typeSize V := by
    rw [Int.toNat_of_nonneg hn.1]
  rw [go.typeSize_array V n hn.1, e]
  ihave Hraw := rawCells_rawElems (V := V) l Hc n.toNat $$ Hraw
  iapply wp_store_array_loop_raw t n l Hc w hwlen hn n.toNat (by omega) $$ Hraw
  iintro ⟨Hl, -⟩
  have hws : w.arr.take n.toNat = w.arr := List.take_of_length_le (by omega)
  rw [hws]
  iapply HΦ
  iapply typedPointsto_combine _ _ _ (fun h => by subst h; exact Hc rfl)
  simp only [TypedPointsto.typedPointstoDef]
  isplit
  · ipureintro; exact hwlen
  · iexact Hl

theorem intoVal_typed_array_store_raw (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : Loc) (v : GoArray V n) :
    {{ (⌜l.locCar ≠ 0⌝ ∗ rawCells l (typeSize (GoArray V n)) : IProp GF) }}
      (App (Val (GoInstruction (GoStore (go.ArrayType n t)))) (Val (PairV #l #v))) @ s; E
    {{ RET #(); l ↦ v }} :=
  intoVal_typed_array_store_raw' t n l v

instance intoVal_typed_array (t : go.GoType) [IntoValTyped (GF := GF) V t] (n : Int) :
    IntoValTypedUnderlying (GF := GF) (GoArray V n) (go.ArrayType n t) := by
  constructor
  · intro s E t' _ v
    iintro %Φ _ HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    split
    · rename_i h
      iapply (wp_alloc_raw (go.ArrayType n t) (n * typeSize V)
        ⟨Int.mul_nonneg h.1 (go.typeSize_nonneg V), h.2⟩ #v (fun l => typedPointsto l v (DFrac.own 1))
        (fun l => by
          have := intoVal_typed_array_store_raw (GF := GF) (V := V) t n (s := s) (E := E) l v
          rw [go.typeSize_array V n h.1] at this
          exact this))
      · itrivial
      · inext; iexact HΦ
    · iapply wp_AngelicExit
  · intro s E t' _ l dq v
    iintro %Φ Hl HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    by_cases hn : 0 ≤ n ∧ n < 2^63-1
    case neg =>
      simp only [show (¬(0 ≤ n ∧ n < 2^63-1)) = True from eq_true hn, ↓reduceIte]
      iapply wp_AngelicExit
    simp only [show (¬(0 ≤ n ∧ n < 2^63-1)) = False from eq_false (fun h => h hn), ↓reduceIte]
    obtain ⟨vs⟩ := v
    icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨%Hlen, Hl⟩
    have hW : W64 n = W64 ((n.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg hn.1]
    rw [hW]
    wp_pure
    wp_apply_core wp_load_array_loop t n l dq vs Hlen hn n.toNat (by omega) $$ Hl
    iintro Hl
    have hvs : vs.take n.toNat ++ (List.replicate n.toNat (zero_val V)).drop n.toNat = vs := by
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by simp)]; simp
    rw [hvs]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    isplit
    · ipureintro; exact Hlen
    · iexact Hl
  · intro s E t' _ l v w
    iintro %Φ Hl HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    by_cases hn : 0 ≤ n ∧ n < 2^63-1
    case neg =>
      simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = True from
        eq_true (fun h => hn ⟨h.1, h.2.1⟩), ↓reduceIte]
      iapply wp_AngelicExit
    by_cases hwlen : (w.arr.length : Int) = n
    case neg =>
      simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = True from
        eq_true (fun h => hwlen h.2.2), ↓reduceIte]
      iapply wp_AngelicExit
    simp only [show (¬(0 ≤ n ∧ n < 2^63-1 ∧ (w.arr.length : Int) = n)) = False from
        eq_false (fun h => h ⟨hn.1, hn.2, hwlen⟩), ↓reduceIte]
    obtain ⟨vs⟩ := v
    icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨%Hlen, Hl⟩
    iapply wp_store_array_loop t n l vs w Hlen hwlen hn n.toNat (by omega) $$ Hl
    iintro Hl
    have hws : w.arr.take n.toNat ++ vs.drop n.toNat = w.arr := by
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp
    rw [hws]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    isplit
    · ipureintro; exact hwlen
    · iexact Hl
  · intro s E t' _ l w
    exact intoVal_typed_array_store_raw' t n l w
  · exact go.type_repr_array t V n

end intoVal

/-! ## `len` and `cap` of an array -/

section lenCap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `len` of an array is its length, which lives in the type rather than next
to the elements, so it needs no ownership of the array. The side condition
excludes array types that no Go program can have (see `go.len_array`); for the
literal lengths Goose emits it is discharged by `wp_pures`'s side-condition
solver.

Goose folds a constant `len`/`cap` itself, so these fire only when the operand
is not constant, e.g. `len(f())`. The operand is evaluated and discarded, which
is what Go does in that case. -/
instance pure_wp_array_len {st : go.GoType} {n : Int} {elem : go.GoType}
    [st ↓u go.ArrayType n elem] (v : val) :
    PureWp (G := G) (L := L) (0 ≤ n ∧ n < 2^63)
      (App (Val #(functions go.len [st])) (Val v)) (Val #(W64 n)) :=
  pure_wp_val _ (App (Val #(functions go.len [st])) (Val v)) #(W64 n) fun s E Φ hn => by
    rw [func_unfold]
    iintro HΦ
    wp_auto_lc 1
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    wp_pures
    iapply HΦ $$ Hlc1

/-- `cap` of an array; see `pure_wp_array_len`. -/
instance pure_wp_array_cap {st : go.GoType} {n : Int} {elem : go.GoType}
    [st ↓u go.ArrayType n elem] (v : val) :
    PureWp (G := G) (L := L) (0 ≤ n ∧ n < 2^63)
      (App (Val #(functions go.cap [st])) (Val v)) (Val #(W64 n)) :=
  pure_wp_val _ (App (Val #(functions go.cap [st])) (Val v)) #(W64 n) fun s E Φ hn => by
    rw [func_unfold]
    iintro HΦ
    wp_auto_lc 1
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
    wp_pures
    iapply HΦ $$ Hlc1

end lenCap

/-! ## Range loops over arrays

Applying `array.forRangeIndex`, `array.forRange` and `array.forRangePtr` unfolds
them to their `for:` loop, which proofs then reason about with `wp_for`, as for
`slice.forRange`. -/

section forRange
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_wp_array_for_range_index (n : Int) (body : val) :
    PureWp (G := G) (L := L) True (App (Val (array.forRangeIndex n)) (Val body))
      gl(let: "i" := GoAlloc go.int #(W64 0) in
        for: (λ: <>, (![go.int] "i") <⟨go.int⟩ #(W64 n)) ;
             (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
          (λ: <>, body (![go.int] "i"))) where
  pure_wp_wp s E Φ K _ := by
    unfold array.forRangeIndex
    iintro H
    wp_call_lc Hlc
    iapply H $$ Hlc

instance pure_wp_array_for_range (n : Int) (t : go.GoType) (a body : val) :
    PureWp (G := G) (L := L) True (App (App (Val (array.forRange n t)) (Val a)) (Val body))
      gl(let: "i" := GoAlloc go.int #(W64 0) in
        for: (λ: <>, (![go.int] "i") <⟨go.int⟩ #(W64 n)) ;
             (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
          (λ: <>, glv(λ: "k", body "k" (Index (go.ArrayType n t) (a, "k"))) (![go.int] "i"))) where
  pure_wp_wp s E Φ K _ := by
    unfold array.forRange
    iintro H
    wp_call_lc Hlc
    iapply H $$ Hlc

instance pure_wp_array_for_range_ptr (n : Int) (t : go.GoType) (p body : val) :
    PureWp (G := G) (L := L) True (App (App (Val (array.forRangePtr n t)) (Val p)) (Val body))
      gl(let: "i" := GoAlloc go.int #(W64 0) in
        for: (λ: <>, (![go.int] "i") <⟨go.int⟩ #(W64 n)) ;
             (λ: <>, "i" <-[go.int] (![go.int] "i") +⟨go.int⟩ #(W64 1)) :=
          (λ: <>, glv(λ: "k", body "k" (![t] (IndexRef (go.ArrayType n t) (p, "k"))))
            (![go.int] "i"))) where
  pure_wp_wp s E Φ K _ := by
    unfold array.forRangePtr
    iintro H
    wp_call_lc Hlc
    iapply H $$ Hlc

end forRange

end Perennial
