/-
Port of `new/golang/theory/array.v`: the typed points-to for arrays
(`l ↦{dq} (a : array.t V n)` is the points-to of every element at
`array_index_ref V i l`), and lemmas to access and split it.

`into_val_typed_array` is `Admitted` in Rocq. It is proved here, against the
corrected `go.store_array` of `Perennial/Golang/Defn/Array.lean` (see there).
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
abbrev load_array_body (n : Int) (elem_type : go.type) (l : val) : expr :=
  gl(if: "n" =⟨go.int⟩ #(W64 0) then GoZeroVal (go.ArrayType n elem_type) #()
            else let: "array_so_far" := "recur" ("n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_addr" := IndexRef (go.ArrayType n elem_type) (l, "n" -⟨go.int⟩ #(W64 1)) in
                 let: "elem_val" := GoLoad elem_type "elem_addr" in
                 ArraySet ("array_so_far", ("n" -⟨go.int⟩ #(W64 1), "elem_val")))

theorem wp_load_array_loop (t : go.type) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : loc) (dq : DFrac) (vs : List V)
    (hlen : (vs.length : Int) = n) (hn : 0 ≤ n ∧ n < 2^63-1) (m : Nat) (hm : (m : Int) ≤ n) :
    {{ array_elems (GF := GF) l vs dq }}
      (App (Val (RecV "recur" "n" (load_array_body n t #l))) (Val #(W64 m))) @ s; E
    {{ RET #(array.mk n (vs.take m ++ (List.replicate n.toNat (zero_val V)).drop m));
       array_elems l vs dq }} := by
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
    unfold array_elems
    icases bigSepL_insert_acc (Φ := fun (j : Nat) (x : V) =>
        typed_pointsto (GF := GF) (array_index_ref V (j : Int) l) x dq) hve $$ Hl
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
abbrev store_array_step (n : Int) (elem_type : go.type) (l v : val) (str_so_far : expr) (j : Int) :
    expr :=
  gl(str_so_far ;;
    (let elem_addr := gl(IndexRef (go.ArrayType n elem_type) (l, #(W64 j)))
     let elem_val := gl(Index (go.ArrayType n elem_type) (v, #(W64 j)))
     gl(GoStore elem_type (elem_addr, elem_val))))

theorem wp_store_array_loop (t : go.type) [IntoValTyped (GF := GF) V t] (n : Int)
    {s : Stuckness} {E : CoPset} (l : loc) (vs : List V) (w : array.t V n)
    (hlen : (vs.length : Int) = n) (hwlen : (w.arr.length : Int) = n)
    (hn : 0 ≤ n ∧ n < 2^63-1) (k : Nat) (hk : (k : Int) ≤ n) :
    ⊢ ∀ Φ, array_elems (GF := GF) l vs (DFrac.own 1) -∗
      (array_elems l (w.arr.take k ++ vs.drop k) (DFrac.own 1) -∗ Φ #()) -∗
      WP (List.foldl (store_array_step n t #l #w) (#() : expr)
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
    unfold array_elems
    icases bigSepL_insert_acc (Φ := fun (j : Nat) (x : V) =>
        typed_pointsto (GF := GF) (array_index_ref V (j : Int) l) x (DFrac.own 1)) hve $$ Hl
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

instance into_val_typed_array (t : go.type) [IntoValTyped (GF := GF) V t] (n : Int) :
    IntoValTypedUnderlying (GF := GF) (array.t V n) (go.ArrayType n t) := by
  constructor
  · intro s E t' _ v
    iintro %Φ _ HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    iapply wp_AngelicExit
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
    icases typed_pointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
    icases typed_pointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typed_pointsto_def]
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
    iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
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
    icases typed_pointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
    icases typed_pointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typed_pointsto_def]
    icases Hl with ⟨%Hlen, Hl⟩
    iapply wp_store_array_loop t n l vs w Hlen hwlen hn n.toNat (by omega) $$ Hl
    iintro Hl
    have hws : w.arr.take n.toNat ++ vs.drop n.toNat = w.arr := by
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp
    rw [hws]
    iapply HΦ
    iapply typed_pointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typed_pointsto_def]
    isplit
    · ipureintro; exact hwlen
    · iexact Hl
  · exact go.type_repr_array t V n

end into_val

end Perennial
