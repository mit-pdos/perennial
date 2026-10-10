/-
`rawCells l n`: the `n` cells from `l` on, owned, whatever they hold. `AllocN` returns them
(`rawCells_of_pointstoVals`), and a typed store into them (`IntoValTyped.wp_store_raw`)
gives a typed points-to; that is how `GoAlloc` of a struct or an array is proved. A struct's
raw cells split into its fields' (`rawCells_struct`, for gc's layout).
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.Golang.Defn.Layout

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProofMode goose_heap

section raw
variable [ext : FfiSyntax] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- The `n` cells from `l` on, owned, with any contents. -/
noncomputable def rawCells (l : Loc) (n : Int) : IProp GF :=
  [∗list] _k ↦ i ∈ List.range n.toNat, iprop(∃ v, heapPointsto (l +ₗ ((i : Nat) : Int)) (DFrac.own 1) v)

theorem rawCells_zero (l : Loc) : rawCells l 0 ⊣⊢ (emp : IProp GF) := by
  unfold rawCells
  simp only [Int.toNat_zero, List.range_zero]
  exact BigSepL.bigSepL_nil

theorem rawCells_add (l : Loc) (n m : Int) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    rawCells l (n + m) ⊣⊢ rawCells l n ∗ rawCells (l +ₗ n) m := by
  unfold rawCells
  rw [show (n + m).toNat = n.toNat + m.toNat by omega, List.range_add]
  refine BigSepL.bigSepL_append.trans ?_
  refine sep_congr .rfl ?_
  rw [BigSepL.bigSepL_map]
  rw [BigSepL.bigSepL_eq_of_forall_eq (Ψ := fun _ i =>
    iprop(∃ v, heapPointsto ((l +ₗ n) +ₗ ((i : Nat) : Int)) (DFrac.own 1) v)) (fun {_ i} => by
      rw [loc_add_assoc, show (n : Int) + ((i : Nat) : Int) = ((n.toNat + i : Nat) : Int) by omega])]
  exact .rfl

/-- The first of at least one cell. -/
theorem rawCells_first (l : Loc) (n : Int) (h : 1 ≤ n) :
    rawCells l n ⊢ (iprop(∃ v, heapPointsto l (DFrac.own 1) v) : IProp GF) := by
  unfold rawCells
  obtain ⟨k, hk⟩ : ∃ k : Nat, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
  rw [hk, List.range_succ_eq_map]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H, -⟩
  simp only [Int.natCast_zero, loc_add_0]
  iexact H

/-- Fewer cells. -/
theorem rawCells_le (l : Loc) (n m : Int) (hn : 0 ≤ n) (hnm : n ≤ m) :
    rawCells l m ⊢ (rawCells l n : IProp GF) := by
  have e := rawCells_add (GF := GF) l n (m - n) hn (by omega)
  rw [show n + (m - n) = m by omega] at e
  iintro H
  icases e.1 $$ H with ⟨H, -⟩
  iexact H

/-- `n` cells from offset `o` of `m` cells (`0 ≤ o`, `o + n ≤ m`). -/
theorem rawCells_sub (l : Loc) (o n m : Int) (ho : 0 ≤ o) (hn : 0 ≤ n) (h : o + n ≤ m) :
    rawCells l m ⊢ (rawCells (l +ₗ o) n : IProp GF) := by
  have e := rawCells_add (GF := GF) l o (m - o) ho (by omega)
  rw [show o + (m - o) = m by omega] at e
  iintro H
  icases e.1 $$ H with ⟨-, H⟩
  iapply rawCells_le _ n (m - o) hn (by omega) $$ H

/-- The cells of the fields `fs` laid out from `off` on, as `go.structLayoutAux` does
(each field `(name, size, align)` at its offset). -/
noncomputable def rawFieldsFrom (l : Loc) : Int → List (GoString × Int × Int) → IProp GF
  | _, [] => iprop(emp)
  | off, (_, sz, al) :: fs =>
    iprop(rawCells (l +ₗ go.roundUp off al) sz ∗ rawFieldsFrom l (go.roundUp off al + sz) fs)

theorem rawCells_fieldsFrom (l : Loc) (off ma : Int) (fs : List (GoString × Int × Int))
    (hoff : 0 ≤ off) (hsz : ∀ e ∈ fs, 0 ≤ e.2.1) (hal : ∀ e ∈ fs, 1 ≤ e.2.2) :
    rawCells (l +ₗ off) ((go.structLayoutAux off ma fs).2.1 - off) ⊢
      (rawFieldsFrom l off fs : IProp GF) := by
  induction fs generalizing off ma with
  | nil => simp only [rawFieldsFrom]; iintro _; itrivial
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    have hal0 := hal _ (List.mem_cons_self ..)
    have hsz0 := hsz _ (List.mem_cons_self ..)
    simp only at hal0 hsz0
    have hr := go.roundUp_ge off al hal0
    have hend := go.structLayoutAux_end (go.roundUp off al + sz) (max ma al) fs
      (fun e he => hsz e (List.mem_cons_of_mem _ he)) (fun e he => hal e (List.mem_cons_of_mem _ he))
    simp only [go.structLayoutAux, rawFieldsFrom]
    generalize hE : (go.structLayoutAux (go.roundUp off al + sz) (max ma al) fs).2.1 = E at *
    -- [off, o) dropped, [o, o + sz) the field, [o + sz, E) the rest
    have e1 := rawCells_add (GF := GF) (l +ₗ off) (go.roundUp off al - off) (E - go.roundUp off al)
      (by omega) (by omega)
    rw [show go.roundUp off al - off + (E - go.roundUp off al) = E - off by omega,
      loc_add_assoc, show off + (go.roundUp off al - off) = go.roundUp off al by omega] at e1
    have e2 := rawCells_add (GF := GF) (l +ₗ go.roundUp off al) sz (E - (go.roundUp off al + sz))
      hsz0 (by omega)
    rw [show sz + (E - (go.roundUp off al + sz)) = E - go.roundUp off al by omega,
      loc_add_assoc] at e2
    iintro H
    icases e1.1 $$ H with ⟨-, H⟩
    icases e2.1 $$ H with ⟨Hf, Hrest⟩
    iframe Hf
    have := ih (go.roundUp off al + sz) (max ma al) (by omega)
      (fun e he => hsz e (List.mem_cons_of_mem _ he)) (fun e he => hal e (List.mem_cons_of_mem _ he))
    rw [hE] at this
    iapply this $$ Hrest

theorem lookup_cons_ne {β : Type} (a k : GoString) (v : β) (rest : List (GoString × β))
    (h : a ≠ k) : ((k, v) :: rest).lookup a = rest.lookup a := by
  simp only [List.lookup, beq_false_of_ne h]

theorem lookup_cons_eq {β : Type} (k : GoString) (v : β) (rest : List (GoString × β)) :
    ((k, v) :: rest).lookup k = some v := by
  simp [List.lookup]

theorem lookup_isSome_of_mem {β : Type} (a : GoString) (l : List (GoString × β))
    (h : a ∈ l.map Prod.fst) : (l.lookup a).isSome := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : a = k
    · subst hk; rw [lookup_cons_eq]; rfl
    · rw [lookup_cons_ne _ _ _ _ hk]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hk
      · exact h

/-- The fields' cells, each at its offset (by name; the names are distinct). -/
theorem rawFieldsFrom_split (l : Loc) (off ma : Int) (fs : List (GoString × Int × Int))
    (hnodup : (fs.map Prod.fst).Nodup) :
    rawFieldsFrom l off fs ⊢ ([∗list] e ∈ fs,
      rawCells (l +ₗ (((go.structLayoutAux off ma fs).1.lookup e.1).getD 0)) e.2.1 : IProp GF) := by
  induction fs generalizing off ma with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons e fs ih =>
    obtain ⟨n, sz, al⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [rawFieldsFrom, go.structLayoutAux]
    iintro ⟨Hf, Hrest⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hf]
    · rw [lookup_cons_eq, Option.getD_some]; iexact Hf
    · ihave Hrest := ih (go.roundUp off al + sz) (max ma al) hnodup.2 $$ Hrest
      iapply (BigSepL.bigSepL_mono (fun {k x} hx => ?_)) $$ Hrest
      have hmem : x ∈ fs := List.mem_of_getElem? hx
      have hne : x.1 ≠ n := fun h => hnodup.1 (h ▸ List.mem_map_of_mem hmem)
      rw [lookup_cons_ne _ _ _ _ hne]

/-- A struct's raw cells hold its fields' raw cells, at gc's offsets. -/
theorem rawCells_struct (l : Loc) (fs : List (GoString × Int × Int))
    (hsz : ∀ e ∈ fs, 0 ≤ e.2.1) (hal : ∀ e ∈ fs, 1 ≤ e.2.2) :
    rawCells l (go.structLayout fs).2.1 ⊢ (rawFieldsFrom l 0 fs : IProp GF) := by
  have h1 := go.structLayout_size_ge fs hsz hal
  have h0 := go.structLayoutAux_end 0 1 fs hsz hal
  iintro H
  ihave H := rawCells_le l ((go.structLayoutAux 0 1 fs).2.1) _ (by omega) h1 $$ H
  have := rawCells_fieldsFrom (GF := GF) l 0 1 fs (by omega) hsz hal
  rw [loc_add_0, Int.sub_zero] at this
  iapply this $$ H

end raw

end Perennial
