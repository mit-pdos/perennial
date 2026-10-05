/-
Finite maps, in the role of stdpp's `gmap`.

`gmap K V` is a partial function with finite support. Equality is extensional
(`GMap.ext`), as with stdpp's canonical `gmap`. Only `DecidableEq K` is needed.
The operations are noncomputable: they exist for specifications, not for
execution.

stdpp notation: `m !! k` is lookup, `<[k := v]> m` is insert, `delete k m` is delete.
-/
import Iris.Std.PartialMap

noncomputable section

namespace Perennial

structure GMap (K : Type u) (V : Type v) where
  lookup : K → Option V
  finite : ∃ l : List K, ∀ k, (lookup k).isSome → k ∈ l

namespace GMap

variable {K : Type u} {V : Type v} [DecidableEq K]

@[ext] theorem ext {m₁ m₂ : GMap K V} (h : ∀ k, m₁.lookup k = m₂.lookup k) : m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext k; exact h k

theorem ext_iff' {m₁ m₂ : GMap K V} : m₁ = m₂ ↔ ∀ k, m₁.lookup k = m₂.lookup k :=
  ⟨fun h _ => h ▸ rfl, ext⟩

def empty : GMap K V := ⟨fun _ => none, ⟨[], by simp⟩⟩

instance : EmptyCollection (GMap K V) := ⟨empty⟩
instance : Inhabited (GMap K V) := ⟨empty⟩

def insert (k : K) (v : V) (m : GMap K V) : GMap K V :=
  ⟨fun k' => if k = k' then some v else m.lookup k',
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨k :: l, fun k' h => ?_⟩
    by_cases e : k = k'
    · simp [e]
    · simp only [e, ite_false] at h; exact List.mem_cons_of_mem _ (hl k' h)⟩

def delete (k : K) (m : GMap K V) : GMap K V :=
  ⟨fun k' => if k = k' then none else m.lookup k',
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k' h => ?_⟩
    by_cases e : k = k'
    · simp [e] at h
    · simp only [e, ite_false] at h; exact hl k' h⟩

def singleton (k : K) (v : V) : GMap K V := insert k v empty

/-- Union, left-biased (stdpp `∪`). -/
def union (m₁ m₂ : GMap K V) : GMap K V :=
  ⟨fun k => (m₁.lookup k).or (m₂.lookup k),
   by
    obtain ⟨l₁, h₁⟩ := m₁.finite
    obtain ⟨l₂, h₂⟩ := m₂.finite
    refine ⟨l₁ ++ l₂, fun k h => ?_⟩
    cases e : m₁.lookup k with
    | some _ => exact List.mem_append_left _ (h₁ k (by simp [e]))
    | none => simp only [e, Option.none_or] at h; exact List.mem_append_right _ (h₂ k h)⟩

instance : Union (GMap K V) := ⟨union⟩

def fmap {V' : Type w} (f : V → V') (m : GMap K V) : GMap K V' :=
  ⟨fun k => (m.lookup k).map f,
   by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l, fun k h => hl k (by simpa using h)⟩⟩

def filter (P : K → V → Bool) (m : GMap K V) : GMap K V :=
  ⟨fun k => (m.lookup k).filter (P k),
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k h => hl k ?_⟩
    cases e : m.lookup k <;> simp_all⟩

/-- Remove duplicates (keeps the last occurrence). -/
def _root_.Perennial.listDedup {α} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then listDedup l else a :: listDedup l

theorem _root_.Perennial.mem_list_dedup {α} [DecidableEq α] {a : α} {l : List α} :
    a ∈ listDedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [listDedup]
  | cons b l ih =>
    unfold listDedup; split
    · rw [ih]; constructor
      · exact List.mem_cons_of_mem _
      · intro h; rcases List.mem_cons.mp h with rfl | h <;> assumption
    · simp [ih]

theorem _root_.Perennial.nodup_list_dedup {α} [DecidableEq α] (l : List α) : (listDedup l).Nodup := by
  induction l with
  | nil => simp [listDedup]
  | cons b l ih =>
    unfold listDedup; split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨fun h' => h (mem_list_dedup.mp h'), ih⟩

def domList (m : GMap K V) : List K :=
  (listDedup (Classical.choose m.finite)).filter (fun k => (m.lookup k).isSome)

/-- The bindings of `m`, in unspecified order (stdpp `mapToList`). -/
noncomputable def toList (m : GMap K V) : List (K × V) :=
  m.domList.filterMap (fun k => (m.lookup k).map (k, ·))

/-- stdpp `dom`, as a membership predicate. -/
def dom (m : GMap K V) (k : K) : Prop := (m.lookup k).isSome

instance : Membership K (GMap K V) := ⟨fun m k => (m.lookup k).isSome⟩

instance (k : K) (m : GMap K V) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable ((m.lookup k).isSome = true))

/-- Number of bindings. -/
noncomputable def size (m : GMap K V) : Nat := m.toList.length

def Disjoint (m₁ m₂ : GMap K V) : Prop := ∀ k, (m₁.lookup k).isSome → (m₂.lookup k).isSome → False

def Subseteq (m₁ m₂ : GMap K V) : Prop := ∀ k v, m₁.lookup k = some v → m₂.lookup k = some v

instance : HasSubset (GMap K V) := ⟨Subseteq⟩

/-- stdpp `listToMap`; later bindings win. -/
def ofList : List (K × V) → GMap K V
  | [] => empty
  | (k, v) :: l => insert k v (ofList l)

/-- Maps from `List.range`-style index (stdpp `map_seq`). -/
def mapSeq (start : Nat) : List V → GMap Nat V
  | [] => empty
  | v :: l => insert start v (mapSeq (start + 1) l)

end GMap

/-! ## stdpp-style notation -/

/-
`m !! k` and `<[k := v]> m` are overloaded on the type of `m`, as in stdpp:
* for `m : gmap K V` they are `GMap.lookup m k` and `GMap.insert k v m`;
* for `l : List A` (index `i : Nat`) they are `l[i]?` and `l.set i v`, so that
  Lean core's `List` lemmas apply directly;
* for any other type, `m !! k` is `m[k]?` (`GetElem?`).
The choice is made by an elaborator from the (whnfR of the) type of `m`.
-/
scoped syntax:80 (name := lookupNotation) term:80 " !! " term:81 : term
scoped syntax:max (name := insertNotation) "<[" term " := " term "]>" term:max : term
scoped notation "{[" k " := " v "]}" => GMap.singleton k v

open Lean Elab Term Meta in
/-- Classify the container type of `m` for `!!` / `<[ ]>`: 0 = gmap, 1 = list,
2 = other, 3 = unknown (metavariable). -/
private def lookupKind (m : Expr) : TermElabM Nat := do
  let ty ← whnfR (← instantiateMVars (← inferType m))
  if ty.isAppOf ``GMap then return 0
  if ty.isAppOf ``List then return 1
  if ty.getAppFn.isMVar then return 3
  return 2

open Lean Elab Term Meta in
@[term_elab lookupNotation] def elabLookupNotation : TermElab := fun stx expectedType => do
  match stx with
  | `($m !! $k) =>
    let mE ← elabTerm m none
    let mut kind ← lookupKind mE
    if kind == 3 then
      tryPostpone
      kind ← lookupKind mE
    let mS ← exprToSyntax mE
    match kind with
    | 1 => elabTerm (← `(($mS)[($k : Nat)]?)) expectedType
    | 2 => elabTerm (← `(($mS)[$k]?)) expectedType
    | _ => elabTerm (← `(GMap.lookup $mS $k)) expectedType
  | _ => throwUnsupportedSyntax

open Lean Elab Term Meta in
@[term_elab insertNotation] def elabInsertNotation : TermElab := fun stx expectedType => do
  match stx with
  | `(<[ $k := $v ]> $m) =>
    let mE ← elabTerm m none
    let mut kind ← lookupKind mE
    if kind == 3 then
      tryPostpone
      kind ← lookupKind mE
    let mS ← exprToSyntax mE
    match kind with
    | 1 => elabTerm (← `(List.set $mS ($k : Nat) $v)) expectedType
    | _ => elabTerm (← `(GMap.insert $k $v $mS)) expectedType
  | _ => throwUnsupportedSyntax

@[app_unexpander GMap.lookup] def GMap.unexpandLookup : Lean.PrettyPrinter.Unexpander
  | `($_ $m $k) => `($m !! $k)
  | _ => throw ()

@[app_unexpander GMap.insert] def GMap.unexpandInsert : Lean.PrettyPrinter.Unexpander
  | `($_ $k $v $m) => `(<[$k := $v]> $m)
  | _ => throw ()

namespace GMap

variable {K : Type u} {V : Type v} [DecidableEq K]

@[simp] theorem lookup_empty (k : K) : (∅ : GMap K V) !! k = none := rfl
@[simp] theorem lookup_mk (f : K → Option V) h (k : K) : (GMap.mk f h) !! k = f k := rfl

theorem lookup_insert (m : GMap K V) (k : K) (v : V) : (<[k := v]> m) !! k = some v := by
  simp [insert]

theorem lookup_insert_ne (m : GMap K V) {k k' : K} (v : V) (h : k ≠ k') :
    (<[k := v]> m) !! k' = m !! k' := by
  simp [insert, h]

@[simp] theorem lookup_insert_eq_iff (m : GMap K V) (k k' : K) (v : V) :
    (<[k := v]> m) !! k' = if k = k' then some v else m !! k' := rfl

theorem lookup_delete (m : GMap K V) (k : K) : (delete k m) !! k = none := by
  simp [delete]

theorem lookup_delete_ne (m : GMap K V) {k k' : K} (h : k ≠ k') :
    (delete k m) !! k' = m !! k' := by
  simp [delete, h]

@[simp] theorem lookup_delete_iff (m : GMap K V) (k k' : K) :
    (delete k m) !! k' = if k = k' then none else m !! k' := rfl

@[simp] theorem lookup_singleton_iff (k k' : K) (v : V) :
    ({[k := v]} : GMap K V) !! k' = if k = k' then some v else none := by
  simp [singleton, insert]; rfl

@[simp] theorem lookup_union (m₁ m₂ : GMap K V) (k : K) :
    (m₁ ∪ m₂) !! k = (m₁ !! k).or (m₂ !! k) := rfl

@[simp] theorem lookup_fmap {V'} (f : V → V') (m : GMap K V) (k : K) :
    (fmap f m) !! k = (m !! k).map f := rfl

@[simp] theorem lookup_filter (P : K → V → Bool) (m : GMap K V) (k : K) :
    (filter P m) !! k = (m !! k).filter (P k) := rfl

theorem mem_iff (m : GMap K V) (k : K) : k ∈ m ↔ (m !! k).isSome := Iff.rfl

theorem insert_insert (m : GMap K V) (k : K) (v v' : V) :
    <[k := v]> (<[k := v']> m) = <[k := v]> m := by
  ext k'; simp; split <;> simp

theorem insert_commute (m : GMap K V) {k k' : K} (v v' : V) (h : k ≠ k') :
    <[k := v]> (<[k' := v']> m) = <[k' := v']> (<[k := v]> m) := by
  ext k''; simp; split <;> split <;> simp_all

theorem insert_id (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) : <[k := v]> m = m := by
  ext k'; simp; split <;> simp_all

theorem delete_insert (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    delete k (<[k := v]> m) = m := by
  ext k'; simp; split <;> simp_all

theorem insert_delete (m : GMap K V) (k : K) (v : V) :
    <[k := v]> (delete k m) = <[k := v]> m := by
  ext k'; simp; split <;> simp_all

theorem mem_dom_list (m : GMap K V) (k : K) : k ∈ m.domList ↔ (m !! k).isSome := by
  unfold domList
  constructor
  · intro h; simpa using (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨mem_list_dedup.mpr (Classical.choose_spec m.finite k h), by simpa using h⟩

theorem nodup_dom_list (m : GMap K V) : m.domList.Nodup :=
  (nodup_list_dedup _).filter _

theorem mem_toList (m : GMap K V) (k : K) (v : V) : (k, v) ∈ m.toList ↔ m !! k = some v := by
  unfold toList
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k', _, v', h, rfl, rfl⟩; exact h
  · intro h; exact ⟨k, (mem_dom_list m k).mpr (by simp [h]), v, h, rfl, rfl⟩

theorem toList_keys_nodup (m : GMap K V) : (m.toList.map Prod.fst).Nodup := by
  unfold toList
  have hnd := nodup_dom_list m
  generalize m.domList = l at hnd ⊢
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    cases e : m.lookup a with
    | none => simpa [List.filterMap_cons, e] using ih hnd.2
    | some v =>
      simp only [List.filterMap_cons, e, Option.map_some, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hnd.2⟩
      intro hmem
      simp only [List.mem_map, List.mem_filterMap, Option.map_eq_some_iff] at hmem
      obtain ⟨⟨k, w⟩, ⟨k', hk', w', _, he⟩, rfl⟩ := hmem
      cases he; exact hnd.1 hk'

@[simp] theorem toList_empty : (∅ : GMap K V).toList = [] := by
  unfold toList
  apply List.filterMap_eq_nil_iff.mpr
  intro k _; rfl

end GMap

/-! ## iris-lean finite-map instance (so iris-lean's `ghost_map`/`gen_heap` apply). -/

open Iris.Std in
instance GMap.instPartialMap {K : Type u} [DecidableEq K] : PartialMap (GMap K) K where
  get? m k := m !! k
  insert m k v := <[k := v]> m
  delete m k := GMap.delete k m
  empty := GMap.empty
  bindAlter f m := ⟨fun k => (m !! k).bind (f k), by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k h => hl k ?_⟩
    cases e : m !! k <;> simp_all⟩
  merge op m₁ m₂ := ⟨fun k => Option.merge (op k) (m₁ !! k) (m₂ !! k), by
    obtain ⟨l₁, h₁⟩ := m₁.finite
    obtain ⟨l₂, h₂⟩ := m₂.finite
    refine ⟨l₁ ++ l₂, fun k h => ?_⟩
    cases e₁ : m₁ !! k <;> cases e₂ : m₂ !! k <;> simp_all [Option.merge]
    all_goals first
      | exact Or.inl (h₁ k (by simp [e₁]))
      | exact Or.inr (h₂ k (by simp [e₂]))⟩

open Iris.Std in
instance GMap.instLawfulFiniteMap {K : Type u} [DecidableEq K] : LawfulFiniteMap (GMap K) K where
  toList m := m.toList
  get?_empty _ := rfl
  get?_insert_eq h := by subst h; exact GMap.lookup_insert _ _ _
  get?_insert_ne h := GMap.lookup_insert_ne _ _ h
  get?_delete_eq h := by subst h; exact GMap.lookup_delete _ _
  get?_delete_ne h := GMap.lookup_delete_ne _ h
  get?_bindAlter := rfl
  get?_merge := rfl
  equiv_iff_eq := ⟨fun h => GMap.ext h, fun h => h ▸ fun _ => rfl⟩
  toList_empty := GMap.toList_empty
  toList_noDupKeys := GMap.toList_keys_nodup _
  toList_get := GMap.mem_toList _ _ _

/-- Finite sets, in the role of stdpp's `gset`. -/
abbrev GSet (K : Type u) := GMap K Unit

/-! ## More operations (stdpp `fin_maps`, `fin_map_dom`, `fin_sets`)

stdpp's set-valued `dom m` is `GMap.domSet m : gset K` here (`GMap.dom` is
the older membership predicate and is kept for compatibility). The lemmas keep
their stdpp names; a lemma `foo_L` (Leibniz version) is the same as `foo`,
since all equalities here are Leibniz. -/

namespace GMap

variable {K : Type u} {V : Type v} [DecidableEq K]

/-- Map difference (stdpp `m₁ ∖ m₂`): the bindings of `m₁` whose key is not in `m₂`. -/
def difference {V' : Type w} (m₁ : GMap K V) (m₂ : GMap K V') : GMap K V :=
  ⟨fun k => if (m₂.lookup k).isSome then none else m₁.lookup k,
   by
    obtain ⟨l, hl⟩ := m₁.finite
    refine ⟨l, fun k h => hl k ?_⟩
    split at h <;> simp_all⟩

/-- Map intersection, left-biased (stdpp `m₁ ∩ m₂`). -/
def intersection {V' : Type w} (m₁ : GMap K V) (m₂ : GMap K V') : GMap K V :=
  ⟨fun k => if (m₂.lookup k).isSome then m₁.lookup k else none,
   by
    obtain ⟨l, hl⟩ := m₁.finite
    refine ⟨l, fun k h => hl k ?_⟩
    split at h <;> simp_all⟩

instance : SDiff (GMap K V) := ⟨difference⟩
instance : Inter (GMap K V) := ⟨intersection⟩

/-- stdpp `dom m`, as a `gset`. -/
def domSet (m : GMap K V) : GMap K Unit := fmap (fun _ => ()) m

/-- stdpp `gsetToGmap x X`. -/
def gsetToGmap (x : V) (X : GMap K Unit) : GMap K V := fmap (fun _ => x) X

/-- stdpp `MapForall P m`. -/
def MapForall (P : K → V → Prop) (m : GMap K V) : Prop := ∀ k v, m.lookup k = some v → P k v

/-- stdpp `MapForall2 P m₁ m₂`: same domain, and `P` holds pointwise. -/
def MapForall2 {V' : Type w} (P : K → V → V' → Prop) (m₁ : GMap K V) (m₂ : GMap K V') : Prop :=
  ∀ k, match m₁.lookup k, m₂.lookup k with
    | some a, some b => P k a b
    | none, none => True
    | _, _ => False

/-- stdpp `mapToList`. -/
abbrev mapToList (m : GMap K V) : List (K × V) := m.toList

/-- stdpp `listToMap`. -/
abbrev listToMap (l : List (K × V)) : GMap K V := ofList l

/-- stdpp `mapFold f b m`: fold over the bindings in an unspecified order. -/
def mapFold {B : Type w} (f : K → V → B → B) (b : B) (m : GMap K V) : B :=
  m.toList.foldr (fun kv acc => f kv.1 kv.2 acc) b

instance : Functor (GMap K) where
  map f m := fmap f m

end GMap

/-- stdpp `m₁ ##ₘ m₂`. -/
scoped infix:50 " ##ₘ " => GMap.Disjoint

namespace GMap

variable {K : Type u} {V : Type v} [DecidableEq K]

/-! ### lookup -/

@[simp] theorem lookup_fmap' {V'} (f : V → V') (m : GMap K V) (k : K) :
    (f <$> m) !! k = (m !! k).map f := rfl

@[simp] theorem fmap_eq {V'} (f : V → V') (m : GMap K V) : f <$> m = fmap f m := rfl

@[simp] theorem lookup_difference {V'} (m₁ : GMap K V) (m₂ : GMap K V') (k : K) :
    (difference m₁ m₂) !! k = if (m₂ !! k).isSome then none else m₁ !! k := rfl

@[simp] theorem lookup_sdiff (m₁ m₂ : GMap K V) (k : K) :
    (m₁ \ m₂) !! k = if (m₂ !! k).isSome then none else m₁ !! k := rfl

@[simp] theorem lookup_intersection {V'} (m₁ : GMap K V) (m₂ : GMap K V') (k : K) :
    (intersection m₁ m₂) !! k = if (m₂ !! k).isSome then m₁ !! k else none := rfl

@[simp] theorem lookup_inter (m₁ m₂ : GMap K V) (k : K) :
    (m₁ ∩ m₂) !! k = if (m₂ !! k).isSome then m₁ !! k else none := rfl

theorem map_eq {m₁ m₂ : GMap K V} (h : ∀ k, m₁ !! k = m₂ !! k) : m₁ = m₂ := ext h

theorem map_eq_iff {m₁ m₂ : GMap K V} : m₁ = m₂ ↔ ∀ k, m₁ !! k = m₂ !! k := ext_iff'

theorem lookup_insert_eq (m : GMap K V) (k : K) (v : V) : (<[k := v]> m) !! k = some v :=
  lookup_insert m k v

theorem lookup_delete_eq (m : GMap K V) (k : K) : (delete k m) !! k = none := lookup_delete m k

theorem lookup_insert_Some (m : GMap K V) (i j : K) (x y : V) :
    (<[i := x]> m) !! j = some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = some y) := by
  simp only [lookup_insert_eq_iff]; split <;> simp_all

theorem lookup_insert_None (m : GMap K V) (i j : K) (x : V) :
    (<[i := x]> m) !! j = none ↔ m !! j = none ∧ i ≠ j := by
  simp only [lookup_insert_eq_iff]; split <;> simp_all

theorem lookup_insert_is_Some (m : GMap K V) (i j : K) (x : V) :
    ((<[i := x]> m) !! j).isSome ↔ i = j ∨ (i ≠ j ∧ (m !! j).isSome) := by
  simp only [lookup_insert_eq_iff]; split <;> simp_all

theorem lookup_delete_Some (m : GMap K V) (i j : K) (y : V) :
    (delete i m) !! j = some y ↔ i ≠ j ∧ m !! j = some y := by
  simp only [lookup_delete_iff]; split <;> simp_all

theorem lookup_delete_None (m : GMap K V) (i j : K) :
    (delete i m) !! j = none ↔ i = j ∨ m !! j = none := by
  simp only [lookup_delete_iff]; split <;> simp_all

theorem lookup_singleton_eq (k : K) (v : V) : ({[k := v]} : GMap K V) !! k = some v := by simp

theorem lookup_singleton (k : K) (v : V) : ({[k := v]} : GMap K V) !! k = some v := by simp

theorem lookup_singleton_ne {k k' : K} (v : V) (h : k ≠ k') :
    ({[k := v]} : GMap K V) !! k' = none := by simp [h]

theorem lookup_singleton_Some (i j : K) (x y : V) :
    ({[i := x]} : GMap K V) !! j = some y ↔ i = j ∧ x = y := by
  simp only [lookup_singleton_iff]; split <;> simp_all

theorem lookup_singleton_None (i j : K) (x : V) :
    ({[i := x]} : GMap K V) !! j = none ↔ i ≠ j := by
  simp only [lookup_singleton_iff]; split <;> simp_all

theorem lookup_fmap_Some {V'} (f : V → V') (m : GMap K V) (k : K) (y : V') :
    (fmap f m) !! k = some y ↔ ∃ x, f x = y ∧ m !! k = some x := by
  simp only [lookup_fmap, Option.map_eq_some_iff]; constructor
  · rintro ⟨x, h, rfl⟩; exact ⟨x, rfl, h⟩
  · rintro ⟨x, rfl, h⟩; exact ⟨x, h, rfl⟩

theorem lookup_union_Some_raw (m₁ m₂ : GMap K V) (k : K) (x : V) :
    (m₁ ∪ m₂) !! k = some x ↔ m₁ !! k = some x ∨ (m₁ !! k = none ∧ m₂ !! k = some x) := by
  simp only [lookup_union]; cases m₁ !! k <;> simp

theorem lookup_union_None (m₁ m₂ : GMap K V) (k : K) :
    (m₁ ∪ m₂) !! k = none ↔ m₁ !! k = none ∧ m₂ !! k = none := by
  simp only [lookup_union]; cases m₁ !! k <;> simp

theorem lookup_union_Some_l (m₁ m₂ : GMap K V) (k : K) (x : V) (h : m₁ !! k = some x) :
    (m₁ ∪ m₂) !! k = some x := by simp [h]

theorem lookup_union_l' (m₁ m₂ : GMap K V) (k : K) (h : (m₁ !! k).isSome) :
    (m₁ ∪ m₂) !! k = m₁ !! k := by
  simp only [lookup_union]; cases e : m₁ !! k <;> simp_all

theorem lookup_union_l (m₁ m₂ : GMap K V) (k : K) (h : m₂ !! k = none) :
    (m₁ ∪ m₂) !! k = m₁ !! k := by
  simp only [lookup_union, h]; cases m₁ !! k <;> rfl

theorem lookup_union_r (m₁ m₂ : GMap K V) (k : K) (h : m₁ !! k = none) :
    (m₁ ∪ m₂) !! k = m₂ !! k := by simp [h]

theorem lookup_union_Some (m₁ m₂ : GMap K V) (k : K) (x : V) (hd : m₁ ##ₘ m₂) :
    (m₁ ∪ m₂) !! k = some x ↔ m₁ !! k = some x ∨ m₂ !! k = some x := by
  rw [lookup_union_Some_raw]; constructor
  · rintro (h | ⟨_, h⟩) <;> simp [h]
  · rintro (h | h)
    · exact Or.inl h
    · right; refine ⟨?_, h⟩
      cases e : m₁ !! k
      · rfl
      · exact (hd k (by simp [e]) (by simp [h])).elim

theorem lookup_union_Some_r (m₁ m₂ : GMap K V) (k : K) (x : V) (hd : m₁ ##ₘ m₂)
    (h : m₂ !! k = some x) : (m₁ ∪ m₂) !! k = some x :=
  (lookup_union_Some m₁ m₂ k x hd).mpr (Or.inr h)

theorem lookup_weaken {m₁ m₂ : GMap K V} {k : K} {v : V} (h : m₁ !! k = some v) (hs : m₁ ⊆ m₂) :
    m₂ !! k = some v := hs k v h

/-! ### basic equalities -/

theorem option_or_match {α} (a b : Option α) :
    a.or b = (match a with | some x => some x | none => b) := by cases a <;> rfl

theorem option_map_match {α β} (f : α → β) (a : Option α) :
    a.map f = (match a with | some x => some (f x) | none => none) := by cases a <;> rfl

theorem option_filter_match {α} (p : α → Bool) (a : Option α) :
    a.filter p = (match a with | some x => if p x then some x else none | none => none) := by
  cases a <;> rfl

theorem ite_isSome_eq {α β} (o : Option α) (a b : β) [Decidable (o.isSome = true)] :
    (if o.isSome = true then a else b) = (match o with | some _ => a | none => b) := by
  cases o <;> simp

open Lean Elab Tactic Term Meta in
/-- `cases` on every `GMap.lookup m k` (closed term) in the goal. -/
elab "cases_lookups" : tactic => do
  let rec collect (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.isAppOfArity ``GMap.lookup 4 && !e.hasLooseBVars && !acc.contains e
      then acc.push e else acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ => collect b (collect t acc)
    | .forallE _ t b _ => collect b (collect t acc)
    | .mdata _ b => collect b acc
    | _ => acc
  let ts := collect (← instantiateMVars (← getMainTarget)) #[]
  for t in ts do
    let stx ← exprToSyntax t
    evalTactic (← `(tactic| all_goals try (cases _ : $stx:term)))

/-- Pointwise proof of a map equation: `ext`, compute all lookups, and case on
every lookup and `if`. -/
local macro "map_pointwise" : tactic => `(tactic| (
  refine GMap.ext (fun k' => ?_)
  simp only [lookup_insert_eq_iff, lookup_delete_iff, lookup_singleton_iff, lookup_union,
    lookup_fmap, lookup_filter, lookup_sdiff, lookup_inter, lookup_difference,
    lookup_intersection, lookup_empty, lookup_fmap', Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ite_false, ite_true]
  repeat' split
  all_goals cases_lookups
  all_goals try simp only [Option.some_or, Option.none_or, Option.map_some, Option.map_none,
    Option.filter_some, Option.filter_none, Option.isSome_some, Option.isSome_none]
  all_goals (first | rfl | (simp_all; done) | skip)))

theorem mapEmpty (m : GMap K V) : m = ∅ ↔ ∀ k, m !! k = none := by
  constructor
  · rintro rfl k; rfl
  · intro h; exact GMap.ext h

theorem lookup_empty_iff (m : GMap K V) : (∀ k, m !! k = none) ↔ m = ∅ := (mapEmpty m).symm

theorem insert_empty (k : K) (v : V) : <[k := v]> (∅ : GMap K V) = {[k := v]} := rfl

theorem insert_delete_eq (m : GMap K V) (k : K) (v : V) :
    <[k := v]> (delete k m) = <[k := v]> m := insert_delete m k v

theorem delete_insert_eq (m : GMap K V) (k : K) (v : V) :
    delete k (<[k := v]> m) = delete k m := by
  map_pointwise

theorem delete_insert_ne (m : GMap K V) {i j : K} (v : V) (h : i ≠ j) :
    delete i (<[j := v]> m) = <[j := v]> (delete i m) := by
  map_pointwise

theorem insert_delete_ne (m : GMap K V) {i j : K} (v : V) (h : i ≠ j) :
    <[i := v]> (delete j m) = delete j (<[i := v]> m) := by
  map_pointwise

theorem delete_empty (k : K) : delete k (∅ : GMap K V) = ∅ := by map_pointwise

theorem delete_notin (m : GMap K V) (k : K) (h : m !! k = none) : delete k m = m := by
  map_pointwise

theorem delete_idemp (m : GMap K V) (k : K) : delete k (delete k m) = delete k m := by
  map_pointwise

theorem delete_commute (m : GMap K V) (i j : K) : delete i (delete j m) = delete j (delete i m) := by
  map_pointwise

theorem delete_singleton (k : K) (v : V) : delete k ({[k := v]} : GMap K V) = ∅ := by
  map_pointwise

theorem insert_singleton (k : K) (v v' : V) : <[k := v]> ({[k := v']} : GMap K V) = {[k := v]} :=
  insert_insert _ _ _ _

theorem delete_insert_id (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) :
    <[k := v]> (delete k m) = m := by
  rw [insert_delete]; exact insert_id m k v h

theorem insert_union_singleton_l (m : GMap K V) (k : K) (v : V) :
    <[k := v]> m = {[k := v]} ∪ m := by
  map_pointwise

theorem insert_union_singleton_r (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    <[k := v]> m = m ∪ {[k := v]} := by
  map_pointwise

theorem insert_union_l (m₁ m₂ : GMap K V) (k : K) (v : V) :
    <[k := v]> (m₁ ∪ m₂) = <[k := v]> m₁ ∪ m₂ := by
  map_pointwise

theorem insert_union_r (m₁ m₂ : GMap K V) (k : K) (v : V) (h : m₁ !! k = none) :
    <[k := v]> (m₁ ∪ m₂) = m₁ ∪ <[k := v]> m₂ := by
  map_pointwise

theorem delete_union (m₁ m₂ : GMap K V) (k : K) :
    delete k (m₁ ∪ m₂) = delete k m₁ ∪ delete k m₂ := by
  map_pointwise

theorem union_delete_insert (m₁ m₂ : GMap K V) (k : K) (v : V) (h : m₁ !! k = some v) :
    delete k m₁ ∪ <[k := v]> m₂ = m₁ ∪ m₂ := by
  map_pointwise

theorem mapEmpty_union (m : GMap K V) : ∅ ∪ m = m := by map_pointwise

theorem map_union_empty (m : GMap K V) : m ∪ ∅ = m := by map_pointwise

theorem map_union_assoc (m₁ m₂ m₃ : GMap K V) : m₁ ∪ m₂ ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) := by
  map_pointwise

theorem map_union_idemp (m : GMap K V) : m ∪ m = m := by map_pointwise

theorem map_union_comm (m₁ m₂ : GMap K V) (hd : m₁ ##ₘ m₂) : m₁ ∪ m₂ = m₂ ∪ m₁ := by
  refine GMap.ext (fun k => ?_); simp only [lookup_union]
  cases e₁ : m₁ !! k <;> cases e₂ : m₂ !! k <;> simp
  exact (hd k (by simp [e₁]) (by simp [e₂])).elim

/-! ### disjointness -/

theorem map_disjoint_spec (m₁ m₂ : GMap K V) :
    m₁ ##ₘ m₂ ↔ ∀ k x y, m₁ !! k = some x → m₂ !! k = some y → False := by
  constructor
  · intro h k x y h1 h2; exact h k (by simp [h1]) (by simp [h2])
  · intro h k h1 h2
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h2
    exact h k x y hx hy

theorem map_disjoint_alt (m₁ m₂ : GMap K V) :
    m₁ ##ₘ m₂ ↔ ∀ k, m₁ !! k = none ∨ m₂ !! k = none := by
  constructor
  · intro h k
    cases e₁ : m₁ !! k
    · exact Or.inl rfl
    · cases e₂ : m₂ !! k
      · exact Or.inr rfl
      · exact (h k (by simp [e₁]) (by simp [e₂])).elim
  · intro h k h1 h2; rcases h k with e | e <;> simp_all

theorem map_disjoint_sym {m₁ m₂ : GMap K V} (h : m₁ ##ₘ m₂) : m₂ ##ₘ m₁ :=
  fun k h1 h2 => h k h2 h1

theorem map_disjoint_empty_l (m : GMap K V) : (∅ : GMap K V) ##ₘ m := fun _ h _ => by simp at h

theorem map_disjoint_empty_r (m : GMap K V) : m ##ₘ (∅ : GMap K V) := fun _ _ h => by simp at h

theorem map_disjoint_singleton_l (m : GMap K V) (k : K) (v : V) :
    ({[k := v]} : GMap K V) ##ₘ m ↔ m !! k = none := by
  constructor
  · intro h; cases e : m !! k
    · rfl
    · exact (h k (by simp) (by simp [e])).elim
  · intro h k' h1 h2; simp at h1; subst h1; simp_all

theorem map_disjoint_singleton_r (m : GMap K V) (k : K) (v : V) :
    m ##ₘ ({[k := v]} : GMap K V) ↔ m !! k = none :=
  ⟨fun h => (map_disjoint_singleton_l m k v).mp (map_disjoint_sym h),
   fun h => map_disjoint_sym ((map_disjoint_singleton_l m k v).mpr h)⟩

theorem map_disjoint_insert_l (m₁ m₂ : GMap K V) (k : K) (v : V) :
    <[k := v]> m₁ ##ₘ m₂ ↔ m₂ !! k = none ∧ m₁ ##ₘ m₂ := by
  simp only [map_disjoint_alt, lookup_insert_eq_iff]
  constructor
  · intro h; refine ⟨?_, fun k' => ?_⟩
    · rcases h k with h | h <;> simp_all
    · rcases h k' with h | h
      · split at h <;> simp_all
      · exact Or.inr h
  · rintro ⟨h1, h2⟩ k'; split
    · subst_vars; exact Or.inr h1
    · exact h2 k'

theorem map_disjoint_insert_r (m₁ m₂ : GMap K V) (k : K) (v : V) :
    m₁ ##ₘ <[k := v]> m₂ ↔ m₁ !! k = none ∧ m₁ ##ₘ m₂ :=
  ⟨fun h => (map_disjoint_insert_l m₂ m₁ k v).mp (map_disjoint_sym h) |>.imp id map_disjoint_sym,
   fun h => map_disjoint_sym ((map_disjoint_insert_l m₂ m₁ k v).mpr ⟨h.1, map_disjoint_sym h.2⟩)⟩

theorem map_disjoint_delete_l (m₁ m₂ : GMap K V) (k : K) (h : m₁ ##ₘ m₂) : delete k m₁ ##ₘ m₂ := by
  intro k' h1 h2; simp at h1; split at h1
  · simp at h1
  · exact h k' h1 h2

theorem map_disjoint_delete_r (m₁ m₂ : GMap K V) (k : K) (h : m₁ ##ₘ m₂) : m₁ ##ₘ delete k m₂ :=
  map_disjoint_sym (map_disjoint_delete_l m₂ m₁ k (map_disjoint_sym h))

theorem map_disjoint_union_l (m₁ m₂ m₃ : GMap K V) :
    m₁ ∪ m₂ ##ₘ m₃ ↔ m₁ ##ₘ m₃ ∧ m₂ ##ₘ m₃ := by
  simp only [map_disjoint_alt, lookup_union]
  constructor
  · intro h; refine ⟨fun k => ?_, fun k => ?_⟩ <;> rcases h k with h | h <;>
      (cases e : m₁ !! k <;> simp_all)
  · rintro ⟨h1, h2⟩ k; rcases h1 k with h | h <;> rcases h2 k with h' | h' <;> simp_all

theorem map_disjoint_union_r (m₁ m₂ m₃ : GMap K V) :
    m₁ ##ₘ m₂ ∪ m₃ ↔ m₁ ##ₘ m₂ ∧ m₁ ##ₘ m₃ := by
  constructor
  · intro h
    have := (map_disjoint_union_l m₂ m₃ m₁).mp (map_disjoint_sym h)
    exact ⟨map_disjoint_sym this.1, map_disjoint_sym this.2⟩
  · rintro ⟨h1, h2⟩
    exact map_disjoint_sym ((map_disjoint_union_l m₂ m₃ m₁).mpr ⟨map_disjoint_sym h1, map_disjoint_sym h2⟩)

theorem map_disjoint_fmap {V'} (f : V → V') (m₁ m₂ : GMap K V) :
    fmap f m₁ ##ₘ fmap f m₂ ↔ m₁ ##ₘ m₂ := by
  simp only [Disjoint, lookup_fmap, Option.isSome_map]

/-! ### subseteq -/

theorem map_subseteq_spec (m₁ m₂ : GMap K V) :
    m₁ ⊆ m₂ ↔ ∀ k v, m₁ !! k = some v → m₂ !! k = some v := Iff.rfl

theorem mapEmpty_subseteq (m : GMap K V) : (∅ : GMap K V) ⊆ m := fun _ _ h => by simp at h

theorem map_subseteq_refl (m : GMap K V) : m ⊆ m := fun _ _ h => h

theorem map_subseteq_trans {m₁ m₂ m₃ : GMap K V} (h1 : m₁ ⊆ m₂) (h2 : m₂ ⊆ m₃) : m₁ ⊆ m₃ :=
  fun k v h => h2 k v (h1 k v h)

theorem map_subseteq_antisymm {m₁ m₂ : GMap K V} (h1 : m₁ ⊆ m₂) (h2 : m₂ ⊆ m₁) : m₁ = m₂ := by
  refine GMap.ext (fun k => ?_); cases e : m₁ !! k
  · cases e' : m₂ !! k
    · rfl
    · rw [h2 k _ e'] at e; cases e
  · exact (h1 k _ e).symm

theorem insert_subseteq (m : GMap K V) (k : K) (v : V) (h : m !! k = none) : m ⊆ <[k := v]> m := by
  intro k' v' h'; simp; split <;> simp_all

theorem insert_subseteq_l (m₁ m₂ : GMap K V) (k : K) (v : V) (h : m₂ !! k = some v)
    (hs : m₁ ⊆ m₂) : <[k := v]> m₁ ⊆ m₂ := by
  intro k' v' h'; simp at h'; split at h'
  · subst_vars; simp_all
  · exact hs k' v' h'

theorem insert_mono (m₁ m₂ : GMap K V) (k : K) (v : V) (hs : m₁ ⊆ m₂) :
    <[k := v]> m₁ ⊆ <[k := v]> m₂ := by
  intro k' v' h'; simp at h' ⊢; split at h' <;> simp_all
  exact hs k' v' h'

theorem delete_subseteq (m : GMap K V) (k : K) : delete k m ⊆ m := by
  intro k' v' h'; simp at h'; exact h'.2

theorem map_union_subseteq_l (m₁ m₂ : GMap K V) : m₁ ⊆ m₁ ∪ m₂ := by
  intro k v h; simp [h]

theorem map_union_subseteq_r (m₁ m₂ : GMap K V) (hd : m₁ ##ₘ m₂) : m₂ ⊆ m₁ ∪ m₂ := by
  intro k v h; exact lookup_union_Some_r m₁ m₂ k v hd h

/-! ### fmap -/

theorem fmap_empty {V'} (f : V → V') : fmap f (∅ : GMap K V) = ∅ := GMap.ext (fun _ => rfl)

theorem fmap_insert {V'} (f : V → V') (m : GMap K V) (k : K) (v : V) :
    fmap f (<[k := v]> m) = <[k := f v]> (fmap f m) := by
  map_pointwise

theorem fmap_delete {V'} (f : V → V') (m : GMap K V) (k : K) :
    fmap f (delete k m) = delete k (fmap f m) := by
  map_pointwise

theorem map_fmap_singleton {V'} (f : V → V') (k : K) (v : V) :
    fmap f ({[k := v]} : GMap K V) = {[k := f v]} := by
  map_pointwise

theorem map_fmap_union {V'} (f : V → V') (m₁ m₂ : GMap K V) :
    fmap f (m₁ ∪ m₂) = fmap f m₁ ∪ fmap f m₂ := by
  map_pointwise

theorem map_fmap_difference {V'} (f : V → V') (m₁ m₂ : GMap K V) :
    fmap f (m₁ \ m₂) = difference (fmap f m₁) m₂ := by
  map_pointwise

theorem map_fmap_id (m : GMap K V) : fmap id m = m := by map_pointwise

theorem map_fmap_compose {V' V''} (f : V → V') (g : V' → V'') (m : GMap K V) :
    fmap (g ∘ f) m = fmap g (fmap f m) := by map_pointwise

theorem map_fmap_ext {V'} (f g : V → V') (m : GMap K V)
    (h : ∀ k x, m !! k = some x → f x = g x) : fmap f m = fmap g m := by
  refine GMap.ext (fun k => ?_); simp only [lookup_fmap]
  cases e : m !! k with
  | none => rfl
  | some x => simp [h k x e]

/-! ### difference / intersection -/

theorem map_difference_diag (m : GMap K V) : m \ m = ∅ := by
  map_pointwise

theorem map_difference_empty (m : GMap K V) : m \ (∅ : GMap K V) = m := by map_pointwise

theorem delete_difference (m₁ m₂ : GMap K V) (k : K) (v : V) :
    delete k (m₁ \ m₂) = m₁ \ <[k := v]> m₂ := by
  map_pointwise

theorem map_difference_union' (m₁ m₂ : GMap K V) : m₁ \ m₂ ∪ m₂ = m₂ ∪ m₁ := by
  map_pointwise

theorem map_difference_union (m₁ m₂ : GMap K V) (h : m₂ ⊆ m₁) : m₂ ∪ m₁ \ m₂ = m₁ := by
  refine GMap.ext (fun k => ?_); simp only [lookup_union, lookup_sdiff]
  cases e₂ : m₂ !! k <;> simp
  exact (h k _ e₂).symm

theorem map_disjoint_difference_l (m₁ m₂ : GMap K V) : m₂ \ m₁ ##ₘ m₁ := by
  intro k h1 h2; simp at h1; split at h1 <;> simp_all

theorem map_disjoint_difference_r (m₁ m₂ : GMap K V) : m₁ ##ₘ m₂ \ m₁ :=
  map_disjoint_sym (map_disjoint_difference_l m₁ m₂)

/-! ### MapForall -/

theorem mapForall_lookup (P : K → V → Prop) (m : GMap K V) :
    MapForall P m ↔ ∀ k v, m !! k = some v → P k v := Iff.rfl

theorem mapForall_lookup_1 {P : K → V → Prop} {m : GMap K V} {k v} (h : MapForall P m)
    (hk : m !! k = some v) : P k v := h k v hk

theorem mapForall_empty (P : K → V → Prop) : MapForall P (∅ : GMap K V) :=
  fun _ _ h => by simp at h

theorem mapForall_impl {P Q : K → V → Prop} {m : GMap K V} (h : MapForall P m)
    (hPQ : ∀ k v, P k v → Q k v) : MapForall Q m := fun k v hk => hPQ k v (h k v hk)

theorem mapForall_insert_1_1 {P : K → V → Prop} {m : GMap K V} {k v}
    (h : MapForall P (<[k := v]> m)) : P k v := h k v (lookup_insert m k v)

theorem mapForall_insert_2 {P : K → V → Prop} {m : GMap K V} {k v} (hv : P k v)
    (h : MapForall P m) : MapForall P (<[k := v]> m) := by
  intro k' v' h'; simp at h'; split at h'
  · simp_all
  · exact h k' v' h'

theorem mapForall_insert (P : K → V → Prop) (m : GMap K V) (k : K) (v : V) (hk : m !! k = none) :
    MapForall P (<[k := v]> m) ↔ P k v ∧ MapForall P m := by
  refine ⟨fun h => ⟨mapForall_insert_1_1 h, fun k' v' h' => h k' v' ?_⟩,
    fun h => mapForall_insert_2 h.1 h.2⟩
  have : k ≠ k' := by rintro rfl; simp_all
  rw [lookup_insert_ne _ _ this]; exact h'

theorem mapForall_delete {P : K → V → Prop} {m : GMap K V} (k : K) (h : MapForall P m) :
    MapForall P (delete k m) := fun k' v' h' => h k' v' (delete_subseteq m k k' v' h')

theorem mapForall_singleton (P : K → V → Prop) (k : K) (v : V) :
    MapForall P ({[k := v]} : GMap K V) ↔ P k v := by
  constructor
  · intro h; exact h k v (by simp)
  · intro h k' v' h'; rw [lookup_singleton_Some] at h'; obtain ⟨rfl, rfl⟩ := h'; exact h

theorem mapForall_fmap {V'} (P : K → V' → Prop) (f : V → V') (m : GMap K V) :
    MapForall P (fmap f m) ↔ MapForall (fun k v => P k (f v)) m := by
  constructor
  · intro h k v hk; exact h k (f v) (by simp [hk])
  · intro h k v' hk; rw [lookup_fmap_Some] at hk; obtain ⟨v, rfl, hk⟩ := hk; exact h k v hk

theorem mapForall_union {P : K → V → Prop} {m₁ m₂ : GMap K V} (h1 : MapForall P m₁)
    (h2 : MapForall P m₂) : MapForall P (m₁ ∪ m₂) := by
  intro k v h; rw [lookup_union_Some_raw] at h
  rcases h with h | ⟨_, h⟩
  · exact h1 k v h
  · exact h2 k v h

/-! ### size -/

theorem length_filterMap_of_isSome {α β} (g : α → Option β) (l : List α)
    (h : ∀ a ∈ l, (g a).isSome) : (l.filterMap g).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ha
    simp only [List.filterMap_cons, hb, List.length_cons]
    rw [ih (fun a' h' => h a' (List.mem_cons_of_mem _ h'))]

theorem size_eq_dom_list_length (m : GMap K V) : size m = m.domList.length := by
  unfold size toList
  apply length_filterMap_of_isSome
  intro k hk; simpa using (mem_dom_list m k).mp hk

/-- The size of a map is the length of any duplicate-free list of its keys. -/
theorem size_eq_length (m : GMap K V) (l : List K) (hnd : l.Nodup)
    (h : ∀ k, k ∈ l ↔ (m !! k).isSome) : size m = l.length := by
  rw [size_eq_dom_list_length]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (nodup_dom_list m) hnd]
  intro k; rw [mem_dom_list, h]

theorem map_size_empty : size (∅ : GMap K V) = 0 :=
  size_eq_length _ [] List.nodup_nil (by simp)

theorem map_size_empty_inv (m : GMap K V) (h : size m = 0) : m = ∅ := by
  rw [size_eq_dom_list_length, List.length_eq_zero_iff] at h
  refine GMap.ext (fun k => ?_); cases e : m !! k
  · rfl
  · have := (mem_dom_list m k).mpr (by simp [e]); rw [h] at this; cases this

theorem map_size_empty_iff (m : GMap K V) : size m = 0 ↔ m = ∅ :=
  ⟨map_size_empty_inv m, fun h => h ▸ map_size_empty⟩

theorem map_size_ne_0_lookup (m : GMap K V) : size m ≠ 0 ↔ ∃ k v, m !! k = some v := by
  constructor
  · intro h
    rw [size_eq_dom_list_length] at h
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil m.domList (fun e => h (by rw [e]; rfl))
    have := (mem_dom_list m k).mp hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
    exact ⟨k, v, hv⟩
  · rintro ⟨k, v, h⟩ h0
    rw [map_size_empty_inv m h0] at h; simp at h

theorem map_size_ne_0_lookup_2 (m : GMap K V) {k v} (h : m !! k = some v) : size m ≠ 0 :=
  (map_size_ne_0_lookup m).mpr ⟨k, v, h⟩

/-- Rocq `map_size_nonzero_lookup` (`Helpers/Map.v`). -/
theorem map_size_nonzero_lookup (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) :
    0 < size m := Nat.pos_of_ne_zero (map_size_ne_0_lookup_2 m h)

/-- Rocq `map_size_nonzero` (`Helpers/Map.v`). -/
theorem map_size_nonzero (m : GMap K V) (k : K) (h : (m !! k).isSome) : 0 < size m := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact map_size_nonzero_lookup m k v hv

theorem map_size_insert_None (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    size (<[k := v]> m) = size m + 1 := by
  rw [size_eq_length _ (k :: m.domList), size_eq_dom_list_length]
  · rfl
  · refine List.nodup_cons.mpr ⟨fun hk => ?_, nodup_dom_list m⟩
    have := (mem_dom_list m k).mp hk; simp [h] at this
  · intro k'; simp only [List.mem_cons, mem_dom_list, lookup_insert_eq_iff]
    by_cases e : k = k'
    · subst e; simp
    · have : k' ≠ k := Ne.symm e
      simp [e, this]

theorem map_size_delete_Some (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) :
    size (delete k m) = size m - 1 := by
  rw [size_eq_length _ (m.domList.erase k), size_eq_dom_list_length]
  · exact List.length_erase_of_mem ((mem_dom_list m k).mpr (by simp [h]))
  · exact (nodup_dom_list m).erase k
  · intro k'; rw [(nodup_dom_list m).mem_erase_iff, mem_dom_list, lookup_delete_iff]
    by_cases e : k = k'
    · subst e; simp
    · have : k' ≠ k := Ne.symm e
      simp [e, this]

theorem map_size_delete_None (m : GMap K V) (k : K) (h : m !! k = none) :
    size (delete k m) = size m := by rw [delete_notin m k h]

theorem map_size_delete (m : GMap K V) (k : K) :
    size (delete k m) = if (m !! k).isSome then size m - 1 else size m := by
  cases e : m !! k
  · simp [map_size_delete_None m k e]
  · simp [map_size_delete_Some m k _ e]

theorem map_size_insert_Some (m : GMap K V) (k : K) (v v' : V) (h : m !! k = some v') :
    size (<[k := v]> m) = size m := by
  rw [← insert_delete, map_size_insert_None _ _ _ (lookup_delete m k),
    map_size_delete_Some m k v' h]
  have := map_size_nonzero_lookup m k v' h; omega

theorem map_size_insert (m : GMap K V) (k : K) (v : V) :
    size (<[k := v]> m) = if (m !! k).isSome then size m else size m + 1 := by
  cases e : m !! k
  · simp [map_size_insert_None m k v e]
  · simp [map_size_insert_Some m k v _ e]

theorem map_size_singleton (k : K) (v : V) : size ({[k := v]} : GMap K V) = 1 := by
  show size (<[k := v]> (∅ : GMap K V)) = 1
  rw [map_size_insert_None _ _ _ rfl, map_size_empty]

theorem map_size_fmap {V'} (f : V → V') (m : GMap K V) : size (fmap f m) = size m := by
  rw [size_eq_length _ m.domList (nodup_dom_list m), size_eq_dom_list_length]
  intro k; simp [mem_dom_list]

theorem map_subseteq_size {m₁ m₂ : GMap K V} (h : m₁ ⊆ m₂) : size m₁ ≤ size m₂ := by
  rw [size_eq_dom_list_length, size_eq_dom_list_length]
  have hsub : m₁.domList ⊆ m₂.domList := by
    intro k hk
    have := (mem_dom_list m₁ k).mp hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
    exact (mem_dom_list m₂ k).mpr (by simp [h k v hv])
  exact (List.subperm_of_subset (nodup_dom_list m₁) hsub).length_le

/-! ### induction -/

theorem map_ind {P : GMap K V → Prop} (h0 : P ∅)
    (hins : ∀ k v m, m !! k = none → P m → P (<[k := v]> m)) : ∀ m, P m := by
  intro m
  induction hs : size m generalizing m with
  | zero => rw [map_size_empty_inv m hs]; exact h0
  | succ n ih =>
    obtain ⟨k, v, hk⟩ := (map_size_ne_0_lookup m).mp (by omega)
    rw [← delete_insert_id m k v hk]
    apply hins k v _ (lookup_delete m k)
    apply ih
    rw [map_size_delete_Some m k v hk]; omega

/-! ### mapToList / mapFold -/

theorem elem_of_map_to_list (m : GMap K V) (k : K) (v : V) :
    (k, v) ∈ mapToList m ↔ m !! k = some v := mem_toList m k v

theorem NoDup_map_to_list (m : GMap K V) : (mapToList m).Nodup := by
  have := toList_keys_nodup m
  exact List.Pairwise.of_map Prod.fst (fun a b h e => h (e ▸ rfl)) this

theorem NoDup_fst_map_to_list (m : GMap K V) : ((mapToList m).map Prod.fst).Nodup :=
  toList_keys_nodup m

theorem mapToList_empty : mapToList (∅ : GMap K V) = [] := toList_empty

theorem length_map_to_list (m : GMap K V) : (mapToList m).length = size m := rfl

/-- Rocq `length_gmap_to_list` (`Helpers/Map.v`). -/
theorem length_gmap_to_list (m : GMap K V) : (mapToList m).length = size m := rfl

theorem mapToList_insert (m : GMap K V) (k : K) (v : V) (h : m !! k = none) :
    (mapToList (<[k := v]> m)).Perm ((k, v) :: mapToList m) := by
  rw [List.perm_ext_iff_of_nodup (NoDup_map_to_list _)]
  · rintro ⟨k', v'⟩
    simp only [elem_of_map_to_list, List.mem_cons, Prod.mk.injEq, lookup_insert_Some]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨_, h'⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr h'
    · rintro (⟨rfl, rfl⟩ | h')
      · exact Or.inl ⟨rfl, rfl⟩
      · right; refine ⟨?_, h'⟩; rintro rfl; simp_all
  · refine List.nodup_cons.mpr ⟨fun hk => ?_, NoDup_map_to_list m⟩
    rw [elem_of_map_to_list] at hk; simp_all

theorem mapToList_delete (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) :
    (mapToList m).Perm ((k, v) :: mapToList (delete k m)) := by
  have := mapToList_insert (delete k m) k v (lookup_delete m k)
  rwa [delete_insert_id m k v h] at this

theorem mapFold_empty {B} (f : K → V → B → B) (b : B) : mapFold f b (∅ : GMap K V) = b := by
  simp [mapFold, toList_empty]

theorem mapFold_insert {B} (f : K → V → B → B) (b : B) (m : GMap K V) (k : K) (v : V)
    (hcomm : ∀ j1 z1 j2 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y))
    (h : m !! k = none) : mapFold f b (<[k := v]> m) = f k v (mapFold f b m) := by
  unfold mapFold
  rw [List.Perm.foldr_eq' (mapToList_insert m k v h)]
  · rfl
  · intro x _ y _ z; exact hcomm _ _ _ _ _

/-- `mapFold` over a list of bindings: every function that ignores order. -/
theorem mapFold_ind {B} (P : B → GMap K V → Prop) (f : K → V → B → B) (b : B)
    (hcomm : ∀ j1 z1 j2 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y))
    (h0 : P b ∅) (hins : ∀ k v m r, m !! k = none → P r m → P (f k v r) (<[k := v]> m)) :
    ∀ m, P (mapFold f b m) m := by
  intro m
  induction m using map_ind with
  | h0 => rw [mapFold_empty]; exact h0
  | hins k v m hk ih => rw [mapFold_insert f b m k v hcomm hk]; exact hins k v m _ hk ih

/-! ### filter -/

theorem map_filter_empty (P : K → V → Bool) : filter P (∅ : GMap K V) = ∅ := GMap.ext (fun _ => rfl)

theorem map_filter_insert_True (P : K → V → Bool) (m : GMap K V) (k : K) (v : V) (h : P k v) :
    filter P (<[k := v]> m) = <[k := v]> (filter P m) := by
  map_pointwise

theorem map_filter_insert_False (P : K → V → Bool) (m : GMap K V) (k : K) (v : V)
    (h : P k v = false) : filter P (<[k := v]> m) = delete k (filter P m) := by
  map_pointwise

theorem map_filter_delete (P : K → V → Bool) (m : GMap K V) (k : K) :
    filter P (delete k m) = delete k (filter P m) := by
  map_pointwise

theorem mapLookup_filter_Some (P : K → V → Bool) (m : GMap K V) (k : K) (v : V) :
    filter P m !! k = some v ↔ m !! k = some v ∧ P k v := by
  simp only [lookup_filter]
  cases m !! k with
  | none => simp
  | some x =>
    by_cases hp : P k x
    · simp [hp]
    · simp [hp]

theorem mapLookup_filter_None (P : K → V → Bool) (m : GMap K V) (k : K) :
    filter P m !! k = none ↔ ∀ v, m !! k = some v → P k v = false := by
  simp only [lookup_filter]; cases m !! k <;> simp [Option.filter]

theorem map_filter_subseteq (P : K → V → Bool) (m : GMap K V) : filter P m ⊆ m := by
  intro k v h; exact ((mapLookup_filter_Some P m k v).mp h).1

/-- Rocq `map_size_filter` (`Helpers/Map.v`). -/
theorem map_size_filter (P : K → V → Bool) (m : GMap K V) : size (filter P m) ≤ size m :=
  map_subseteq_size (map_filter_subseteq P m)

/-! ### map_seq -/

theorem lookup_map_seq (start : Nat) (l : List V) (i : Nat) :
    mapSeq start l !! i = if start ≤ i then l[i - start]? else none := by
  induction l generalizing start with
  | nil => show (∅ : GMap Nat V) !! i = _; split <;> rfl
  | cons v l ih =>
    simp only [mapSeq, lookup_insert_eq_iff, ih]
    by_cases h : start = i
    · subst h; simp
    · simp only [h, ite_false]
      by_cases h' : start + 1 ≤ i
      · have : i - start = (i - (start + 1)) + 1 := by omega
        simp [h', this, show start ≤ i by omega]
      · simp [h', show ¬ start ≤ i by omega]

theorem lookup_map_seq_0 (l : List V) (i : Nat) : mapSeq 0 l !! i = l[i]? := by
  simp [lookup_map_seq]

theorem lookup_map_seq_None (start : Nat) (l : List V) (i : Nat) :
    mapSeq start l !! i = none ↔ i < start ∨ start + l.length ≤ i := by
  rw [lookup_map_seq]; split
  · rw [List.getElem?_eq_none_iff]; omega
  · simp; omega

theorem mapSeq_cons (start : Nat) (v : V) (l : List V) :
    mapSeq start (v :: l) = <[start := v]> (mapSeq (start + 1) l) := rfl

theorem mapSeq_snoc (start : Nat) (l : List V) (v : V) :
    mapSeq start (l ++ [v]) = <[start + l.length := v]> (mapSeq start l) := by
  refine GMap.ext (fun i => ?_); simp only [lookup_map_seq, lookup_insert_eq_iff]
  by_cases h : start + l.length = i
  · subst h; simp
  · simp only [h, ite_false]; split
    · by_cases hl : i - start < l.length
      · rw [List.getElem?_append_left hl]
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by omega)]
    · rfl

theorem mapSeq_cons_disjoint (start : Nat) (l : List V) :
    mapSeq (start + 1) l !! start = none := by
  rw [lookup_map_seq, if_neg (by omega)]

end GMap


/-! ## Finite sets (`gset K = gmap K Unit`)

Set operations reuse the map ones: `∪` is map union, `∩` and `∖` are map
intersection and difference, `x ∈ X` is map membership, `X ⊆ Y` is map
inclusion, and `X ## Y` is map disjointness. `{[x]}` is the singleton set. -/

namespace GMap

variable {K : Type u} [DecidableEq K]

instance : Singleton K (GMap K Unit) := ⟨fun k => singleton k ()⟩
instance : Insert K (GMap K Unit) := ⟨fun k s => insert k () s⟩

end GMap

/-- stdpp `{[x]}` (singleton set). -/
scoped notation "{[" x "]}" => (Singleton.singleton x : GSet _)

/-- stdpp `X ## Y` (disjoint sets). -/
scoped infix:50 " ## " => GMap.Disjoint

/-- stdpp's `X ∖ Y` (U+2216), the same as Lean's `X \ Y`. -/
scoped infixl:70 " ∖ " => SDiff.sdiff

namespace GMap

variable {K : Type u} {V : Type v} [DecidableEq K]

/-- stdpp `elements X`. -/
def elements (X : GSet K) : List K := X.domList

/-- stdpp `listToSet l`. -/
def listToSet : List K → GSet K
  | [] => ∅
  | k :: l => insert k () (listToSet l)

/-- stdpp `⋃ Xs` (`unionList`). -/
def unionList : List (GSet K) → GSet K
  | [] => ∅
  | X :: Xs => X ∪ unionList Xs

theorem elem_of_gset (X : GSet K) (x : K) : x ∈ X ↔ X !! x = some () := by
  show (X !! x).isSome = true ↔ _
  cases X !! x <;> simp

theorem set_eq {X Y : GSet K} (h : ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := by
  refine ext (fun x => ?_)
  have := h x; rw [elem_of_gset, elem_of_gset] at this
  cases e₁ : X !! x <;> cases e₂ : Y !! x <;> simp_all

theorem set_eq_iff {X Y : GSet K} : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y :=
  ⟨fun h _ => h ▸ Iff.rfl, set_eq⟩

theorem elem_of_empty (x : K) : x ∈ (∅ : GSet K) ↔ False := by
  simp [elem_of_gset]

theorem not_elem_of_empty (x : K) : x ∉ (∅ : GSet K) := by simp [elem_of_gset]

theorem elem_of_singleton (x y : K) : x ∈ ({[y]} : GSet K) ↔ x = y := by
  show ((singleton y () : GSet K) !! x).isSome = true ↔ _
  simp only [lookup_singleton_iff]
  by_cases e : y = x
  · subst e; simp
  · have : x ≠ y := Ne.symm e
    simp [e, this]

theorem elem_of_singleton_2 (x : K) : x ∈ ({[x]} : GSet K) := (elem_of_singleton x x).mpr rfl

theorem elem_of_insert_set (x y : K) (X : GSet K) :
    x ∈ (Insert.insert y X : GSet K) ↔ x = y ∨ x ∈ X := by
  show ((insert y () X) !! x).isSome = true ↔ _ ∨ (X !! x).isSome = true
  simp only [lookup_insert_eq_iff]
  by_cases e : y = x
  · subst e; simp
  · have : x ≠ y := Ne.symm e
    simp [e, this]

theorem elem_of_union (x : K) (X Y : GSet K) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y := by
  show ((X ∪ Y) !! x).isSome = true ↔ (X !! x).isSome = true ∨ (Y !! x).isSome = true
  simp only [lookup_union]; cases X !! x <;> simp

theorem elem_of_intersection (x : K) (X Y : GSet K) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y := by
  show ((X ∩ Y) !! x).isSome = true ↔ (X !! x).isSome = true ∧ (Y !! x).isSome = true
  simp only [lookup_inter]; split <;> simp_all

theorem elem_of_difference (x : K) (X Y : GSet K) : x ∈ X \ Y ↔ x ∈ X ∧ x ∉ Y := by
  show ((X \ Y) !! x).isSome = true ↔ (X !! x).isSome = true ∧ ¬ (Y !! x).isSome = true
  simp only [lookup_sdiff]; split <;> simp_all

theorem elem_of_subseteq (X Y : GSet K) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by
  constructor
  · intro h x hx; rw [elem_of_gset] at *; exact h x () hx
  · intro h x u hx; cases u; rw [← elem_of_gset] at *; exact h x hx

theorem elem_of_disjoint (X Y : GSet K) : X ## Y ↔ ∀ x, x ∈ X → x ∈ Y → False := Iff.rfl

theorem elem_of_weaken {x : K} {X Y : GSet K} (h : x ∈ X) (hs : X ⊆ Y) : x ∈ Y :=
  (elem_of_subseteq X Y).mp hs x h

theorem elem_of_union_l {x : K} {X : GSet K} (Y : GSet K) (h : x ∈ X) : x ∈ X ∪ Y :=
  (elem_of_union x X Y).mpr (Or.inl h)

theorem elem_of_union_r {x : K} (X : GSet K) {Y : GSet K} (h : x ∈ Y) : x ∈ X ∪ Y :=
  (elem_of_union x X Y).mpr (Or.inr h)

theorem not_elem_of_union (x : K) (X Y : GSet K) : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y := by
  rw [elem_of_union]; exact not_or

theorem not_elem_of_singleton (x y : K) : x ∉ ({[y]} : GSet K) ↔ x ≠ y := by
  rw [elem_of_singleton]

/-- A tactic for simple set goals: reduce to membership and use propositional
logic (a weak `set_solver`). -/
macro "set_solver" : tactic => `(tactic| (
  try apply set_eq
  try intro
  simp_all only [elem_of_union, elem_of_intersection, elem_of_difference, elem_of_singleton,
    elem_of_empty, elem_of_subseteq, elem_of_disjoint, not_elem_of_empty, elem_of_insert_set]
  try grind))

theorem union_comm_L (X Y : GSet K) : X ∪ Y = Y ∪ X := set_eq fun x => by
  simp only [elem_of_union]; exact Or.comm

theorem union_assoc_L (X Y Z : GSet K) : X ∪ Y ∪ Z = X ∪ (Y ∪ Z) := set_eq fun x => by
  simp only [elem_of_union]; exact or_assoc

theorem union_empty_l_L (X : GSet K) : ∅ ∪ X = X := mapEmpty_union X
theorem union_empty_r_L (X : GSet K) : X ∪ ∅ = X := map_union_empty X
theorem union_idemp_L (X : GSet K) : X ∪ X = X := map_union_idemp X

theorem intersection_comm_L (X Y : GSet K) : X ∩ Y = Y ∩ X := set_eq fun x => by
  simp only [elem_of_intersection]; exact And.comm

theorem difference_diag_L (X : GSet K) : X \ X = ∅ := map_difference_diag X
theorem difference_empty_L (X : GSet K) : X \ (∅ : GSet K) = X := map_difference_empty X

theorem union_difference_L {X Y : GSet K} (h : X ⊆ Y) : Y = X ∪ (Y \ X) := set_eq fun x => by
  simp only [elem_of_union, elem_of_difference]
  have := (elem_of_subseteq X Y).mp h x
  by_cases hx : x ∈ X <;> simp_all

theorem difference_union_L (X Y : GSet K) : X \ Y ∪ Y = X ∪ Y := set_eq fun x => by
  simp only [elem_of_union, elem_of_difference]; by_cases hy : x ∈ Y <;> simp [hy]

theorem empty_subseteq (X : GSet K) : (∅ : GSet K) ⊆ X := mapEmpty_subseteq X

theorem subseteq_refl (X : GSet K) : X ⊆ X := map_subseteq_refl X

theorem union_subseteq_l (X Y : GSet K) : X ⊆ X ∪ Y :=
  (elem_of_subseteq _ _).mpr fun _ h => elem_of_union_l Y h

theorem union_subseteq_r (X Y : GSet K) : Y ⊆ X ∪ Y :=
  (elem_of_subseteq _ _).mpr fun _ h => elem_of_union_r X h

theorem union_subseteq (X Y Z : GSet K) : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z := by
  simp only [elem_of_subseteq, elem_of_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem difference_subseteq (X Y : GSet K) : X \ Y ⊆ X :=
  (elem_of_subseteq _ _).mpr fun x h => ((elem_of_difference x X Y).mp h).1

theorem elem_of_subseteq_singleton (x : K) (X : GSet K) : x ∈ X ↔ {[x]} ⊆ X := by
  rw [elem_of_subseteq]
  exact ⟨fun h y hy => (elem_of_singleton y x).mp hy ▸ h, fun h => h x (elem_of_singleton_2 x)⟩

theorem singleton_subseteq_l (x : K) (X : GSet K) : {[x]} ⊆ X ↔ x ∈ X :=
  (elem_of_subseteq_singleton x X).symm

theorem disjoint_sym {X Y : GSet K} (h : X ## Y) : Y ## X := map_disjoint_sym h

theorem disjoint_union_l (X Y Z : GSet K) : X ∪ Y ## Z ↔ X ## Z ∧ Y ## Z :=
  map_disjoint_union_l X Y Z

theorem disjoint_union_r (X Y Z : GSet K) : X ## Y ∪ Z ↔ X ## Y ∧ X ## Z :=
  map_disjoint_union_r X Y Z

theorem disjoint_singleton_l (x : K) (X : GSet K) : {[x]} ## X ↔ x ∉ X := by
  rw [elem_of_disjoint]
  exact ⟨fun h hx => h x (elem_of_singleton_2 x) hx,
    fun h y hy hy' => h ((elem_of_singleton y x).mp hy ▸ hy')⟩

theorem disjoint_singleton_r (x : K) (X : GSet K) : X ## {[x]} ↔ x ∉ X :=
  ⟨fun h => (disjoint_singleton_l x X).mp (disjoint_sym h),
   fun h => disjoint_sym ((disjoint_singleton_l x X).mpr h)⟩

theorem disjoint_intersection_L (X Y : GSet K) : X ## Y ↔ X ∩ Y = ∅ := by
  rw [elem_of_disjoint, set_eq_iff]
  simp only [elem_of_intersection, elem_of_empty, iff_false, not_and]

theorem disjoint_difference_l (X Y : GSet K) : X \ Y ## Y := map_disjoint_difference_l Y X

theorem singleton_union_difference (x : K) (X : GSet K) (h : x ∈ X) :
    X = {[x]} ∪ (X \ {[x]}) :=
  union_difference_L ((singleton_subseteq_l x X).mpr h)

/-! ### size -/

theorem size_empty : size (∅ : GSet K) = 0 := map_size_empty

theorem size_empty_iff (X : GSet K) : size X = 0 ↔ X = ∅ := map_size_empty_iff X

theorem size_singleton (x : K) : size ({[x]} : GSet K) = 1 := map_size_singleton x ()

theorem set_choose_L (X : GSet K) (h : X ≠ ∅) : ∃ x, x ∈ X := by
  obtain ⟨k, v, hk⟩ := (map_size_ne_0_lookup X).mp (fun h0 => h (map_size_empty_inv X h0))
  exact ⟨k, by show (X !! k).isSome = true; simp [hk]⟩

theorem size_pos_elem_of (X : GSet K) (h : 0 < size X) : ∃ x, x ∈ X :=
  set_choose_L X (fun e => by rw [e, size_empty] at h; exact Nat.lt_irrefl _ h)

theorem size_eq_length_set (X : GSet K) (l : List K) (hnd : l.Nodup) (h : ∀ x, x ∈ l ↔ x ∈ X) :
    size X = l.length := size_eq_length X l hnd h

theorem size_union {X Y : GSet K} (h : X ## Y) : size (X ∪ Y) = size X + size Y := by
  rw [size_eq_dom_list_length X, size_eq_dom_list_length Y, ← List.length_append]
  apply size_eq_length
  · rw [List.nodup_append]
    refine ⟨nodup_dom_list X, nodup_dom_list Y, fun a ha b hb e => ?_⟩
    subst e
    exact h a ((mem_dom_list X a).mp ha) ((mem_dom_list Y a).mp hb)
  · intro k
    rw [List.mem_append, mem_dom_list, mem_dom_list]
    exact (elem_of_union k X Y).symm

theorem size_union_alt (X Y : GSet K) : size (X ∪ Y) = size X + size (Y \ X) := by
  rw [← size_union (map_disjoint_sym (disjoint_difference_l Y X))]
  congr 1; apply set_eq; intro x
  simp only [elem_of_union, elem_of_difference]; by_cases hx : x ∈ X <;> simp [hx]

theorem subseteq_size {X Y : GSet K} (h : X ⊆ Y) : size X ≤ size Y := map_subseteq_size h

theorem size_difference {X Y : GSet K} (h : Y ⊆ X) : size (X \ Y) = size X - size Y := by
  have := union_difference_L h
  have hs := size_union (disjoint_sym (disjoint_difference_l X Y))
  rw [← this] at hs; omega

theorem set_subseteq_size_eq {X Y : GSet K} (h : X ⊆ Y) (hs : size Y ≤ size X) : X = Y := by
  have := size_difference h
  have h0 : size (Y \ X) = 0 := by have := subseteq_size h; omega
  rw [size_empty_iff] at h0
  rw [union_difference_L h, h0, union_empty_r_L]

theorem size_1_elem_of (X : GSet K) (h : size X = 1) : ∃ x, X = {[x]} := by
  obtain ⟨x, hx⟩ := size_pos_elem_of X (by omega)
  refine ⟨x, (set_subseteq_size_eq ((singleton_subseteq_l x X).mpr hx) ?_).symm⟩
  rw [size_singleton]; omega

/-! ### elements / listToSet -/

theorem elem_of_elements (X : GSet K) (x : K) : x ∈ elements X ↔ x ∈ X := mem_dom_list X x

theorem NoDup_elements (X : GSet K) : (elements X).Nodup := nodup_dom_list X

theorem length_elements (X : GSet K) : (elements X).length = size X :=
  (size_eq_dom_list_length X).symm

theorem elem_of_list_to_set (x : K) (l : List K) : x ∈ listToSet l ↔ x ∈ l := by
  induction l with
  | nil => simp [listToSet, elem_of_empty]
  | cons a l ih => rw [listToSet]; exact (elem_of_insert_set x a _).trans (by simp [ih])

theorem listToSet_nil : listToSet ([] : List K) = ∅ := rfl

theorem listToSet_cons (x : K) (l : List K) : listToSet (x :: l) = {[x]} ∪ listToSet l :=
  insert_union_singleton_l _ _ _

theorem listToSet_app (l₁ l₂ : List K) :
    listToSet (l₁ ++ l₂) = listToSet l₁ ∪ listToSet l₂ := set_eq fun x => by
  simp [elem_of_list_to_set, elem_of_union]

theorem size_list_to_set (l : List K) (h : l.Nodup) : size (listToSet l) = l.length :=
  size_eq_length _ l h (fun x => (elem_of_list_to_set x l).symm)

theorem listToSet_elements (X : GSet K) : listToSet (elements X) = X := set_eq fun x => by
  rw [elem_of_list_to_set, elem_of_elements]

theorem elem_of_union_list (x : K) (Xs : List (GSet K)) :
    x ∈ unionList Xs ↔ ∃ X ∈ Xs, x ∈ X := by
  induction Xs with
  | nil => simp [unionList, elem_of_empty]
  | cons X Xs ih => simp [unionList, elem_of_union, ih]

theorem unionList_app (Xs Ys : List (GSet K)) :
    unionList (Xs ++ Ys) = unionList Xs ∪ unionList Ys := set_eq fun x => by
  simp only [elem_of_union_list, elem_of_union, List.mem_append]
  constructor
  · rintro ⟨X, hX | hX, hx⟩
    · exact Or.inl ⟨X, hX, hx⟩
    · exact Or.inr ⟨X, hX, hx⟩
  · rintro (⟨X, hX, hx⟩ | ⟨X, hX, hx⟩)
    · exact ⟨X, Or.inl hX, hx⟩
    · exact ⟨X, Or.inr hX, hx⟩

/-! ### induction -/

theorem set_ind_L {P : GSet K → Prop} (h0 : P ∅)
    (hins : ∀ x X, x ∉ X → P X → P ({[x]} ∪ X)) : ∀ X, P X := by
  intro X
  induction X using map_ind with
  | h0 => exact h0
  | hins k u m hk ih =>
    cases u
    rw [insert_union_singleton_l]
    exact hins k m (by show ¬ (m !! k).isSome = true; simp [hk]) ih

/-! ### dom -/

theorem elem_of_dom (m : GMap K V) (k : K) : k ∈ domSet m ↔ ∃ v, m !! k = some v := by
  show ((fmap _ m) !! k).isSome = true ↔ _
  simp only [lookup_fmap, Option.isSome_map]
  exact Option.isSome_iff_exists

theorem elem_of_dom' (m : GMap K V) (k : K) : k ∈ domSet m ↔ k ∈ m := by
  show ((fmap _ m) !! k).isSome = true ↔ (m !! k).isSome = true
  simp

theorem elem_of_dom_2 (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) : k ∈ domSet m :=
  (elem_of_dom m k).mpr ⟨v, h⟩

theorem not_elem_of_dom (m : GMap K V) (k : K) : k ∉ domSet m ↔ m !! k = none := by
  rw [elem_of_dom]; cases m !! k <;> simp

theorem not_elem_of_dom_1 (m : GMap K V) (k : K) (h : k ∉ domSet m) : m !! k = none :=
  (not_elem_of_dom m k).mp h

theorem not_elem_of_dom_2 (m : GMap K V) (k : K) (h : m !! k = none) : k ∉ domSet m :=
  (not_elem_of_dom m k).mpr h

@[simp] theorem lookup_domSet (m : GMap K V) (k : K) :
    domSet m !! k = (m !! k).map (fun _ => ()) := rfl

theorem dom_empty : domSet (∅ : GMap K V) = ∅ := GMap.ext fun _ => rfl
theorem dom_empty_L : domSet (∅ : GMap K V) = ∅ := dom_empty

theorem dom_empty_iff (m : GMap K V) : domSet m = ∅ ↔ m = ∅ := by
  constructor
  · intro h; refine GMap.ext fun k => ?_
    have := congrArg (· !! k) h; simp at this; simpa using this
  · rintro rfl; exact dom_empty

theorem dom_empty_iff_L (m : GMap K V) : domSet m = ∅ ↔ m = ∅ := dom_empty_iff m

theorem dom_insert (m : GMap K V) (k : K) (v : V) :
    domSet (<[k := v]> m) = {[k]} ∪ domSet m := by
  show fmap _ (<[k := v]> m) = _
  rw [fmap_insert, insert_union_singleton_l]; rfl

theorem dom_insert_L (m : GMap K V) (k : K) (v : V) :
    domSet (<[k := v]> m) = {[k]} ∪ domSet m := dom_insert m k v

theorem dom_insert_lookup (m : GMap K V) (k : K) (v v' : V) (h : m !! k = some v') :
    domSet (<[k := v]> m) = domSet m := by
  rw [dom_insert]; apply set_eq; intro x
  rw [elem_of_union, elem_of_singleton]
  constructor
  · rintro (rfl | h'); exact elem_of_dom_2 m x v' h; exact h'
  · exact Or.inr

theorem dom_delete (m : GMap K V) (k : K) : domSet (delete k m) = domSet m \ {[k]} := by
  apply set_eq; intro x
  rw [elem_of_difference, elem_of_singleton, elem_of_dom', elem_of_dom']
  show ((delete k m) !! x).isSome = true ↔ (m !! x).isSome = true ∧ ¬ x = k
  simp only [lookup_delete_iff]; by_cases e : k = x
  · subst e; simp
  · simp [e, Ne.symm e]

theorem dom_delete_L (m : GMap K V) (k : K) : domSet (delete k m) = domSet m \ {[k]} :=
  dom_delete m k

theorem dom_singleton (k : K) (v : V) : domSet ({[k := v]} : GMap K V) = {[k]} := by
  show fmap _ (singleton k v) = singleton k ()
  rw [map_fmap_singleton]

theorem dom_singleton_L (k : K) (v : V) : domSet ({[k := v]} : GMap K V) = {[k]} :=
  dom_singleton k v

theorem dom_fmap {V'} (f : V → V') (m : GMap K V) : domSet (fmap f m) = domSet m := by
  refine GMap.ext fun k => ?_; simp

theorem dom_fmap_L {V'} (f : V → V') (m : GMap K V) : domSet (fmap f m) = domSet m :=
  dom_fmap f m

theorem dom_union (m₁ m₂ : GMap K V) : domSet (m₁ ∪ m₂) = domSet m₁ ∪ domSet m₂ := by
  show fmap _ (m₁ ∪ m₂) = _
  rw [map_fmap_union]; rfl

theorem dom_union_L (m₁ m₂ : GMap K V) : domSet (m₁ ∪ m₂) = domSet m₁ ∪ domSet m₂ :=
  dom_union m₁ m₂

theorem subseteq_dom {m₁ m₂ : GMap K V} (h : m₁ ⊆ m₂) : domSet m₁ ⊆ domSet m₂ := by
  rw [elem_of_subseteq]; intro x hx
  obtain ⟨v, hv⟩ := (elem_of_dom m₁ x).mp hx
  exact elem_of_dom_2 m₂ x v (h x v hv)

theorem size_dom (m : GMap K V) : size (domSet m) = size m := map_size_fmap _ m

/-- Rocq `map_size_dom` (`Helpers/Map.v`). -/
theorem map_size_dom (m : GMap K V) : size m = size (domSet m) := (size_dom m).symm

theorem map_disjoint_dom (m₁ m₂ : GMap K V) : m₁ ##ₘ m₂ ↔ domSet m₁ ## domSet m₂ := by
  simp only [Disjoint, lookup_domSet, Option.isSome_map]

theorem dom_map_seq (start : Nat) (l : List V) (i : Nat) :
    i ∈ domSet (mapSeq start l) ↔ start ≤ i ∧ i < start + l.length := by
  rw [elem_of_dom']
  show ((mapSeq start l) !! i).isSome = true ↔ _
  rw [lookup_map_seq]; split
  · rw [Option.isSome_iff_ne_none, Ne, List.getElem?_eq_none_iff]; omega
  · simp; omega

/-! ### gsetToGmap -/

@[simp] theorem lookup_gset_to_gmap (x : V) (X : GSet K) (k : K) :
    gsetToGmap x X !! k = (X !! k).map (fun _ => x) := rfl

theorem lookup_gset_to_gmap_Some (x y : V) (X : GSet K) (k : K) :
    gsetToGmap x X !! k = some y ↔ k ∈ X ∧ x = y := by
  rw [lookup_gset_to_gmap, elem_of_gset]; cases X !! k <;> simp

theorem lookup_gset_to_gmap_None (x : V) (X : GSet K) (k : K) :
    gsetToGmap x X !! k = none ↔ k ∉ X := by
  rw [lookup_gset_to_gmap, elem_of_gset]; cases X !! k <;> simp

theorem dom_gset_to_gmap (x : V) (X : GSet K) : domSet (gsetToGmap x X) = X := by
  refine GMap.ext fun k => ?_; simp; cases X !! k <;> rfl

theorem gsetToGmap_empty (x : V) : gsetToGmap x (∅ : GSet K) = ∅ := GMap.ext fun _ => rfl

theorem gsetToGmap_union_singleton (x : V) (k : K) (X : GSet K) :
    gsetToGmap x ({[k]} ∪ X) = <[k := x]> (gsetToGmap x X) := by
  show fmap _ (singleton k () ∪ X) = _
  rw [map_fmap_union, map_fmap_singleton, ← insert_union_singleton_l]; rfl

end GMap

/-! ## Rocq-style unqualified names

stdpp lemmas are not namespaced; these aliases let ported proofs say
`lookup_insert_ne` etc. inside `namespace Perennial` (or after `open Perennial`). -/

export GMap (lookup_empty lookup_insert lookup_insert_ne lookup_insert_eq lookup_delete
  lookup_delete_ne lookup_delete_eq lookup_union lookup_fmap lookup_filter lookup_difference
  lookup_intersection lookup_insert_Some lookup_insert_None lookup_insert_is_Some
  lookup_delete_Some lookup_delete_None lookup_singleton lookup_singleton_eq lookup_singleton_ne
  lookup_singleton_Some lookup_singleton_None lookup_fmap_Some lookup_union_Some_raw
  lookup_union_None lookup_union_Some_l lookup_union_l lookup_union_l' lookup_union_r
  lookup_union_Some lookup_union_Some_r lookup_weaken map_eq map_eq_iff mapEmpty insert_empty
  insert_insert insert_commute insert_id delete_insert insert_delete insert_delete_eq
  delete_insert_eq delete_insert_ne insert_delete_ne delete_empty delete_notin delete_idemp
  delete_commute delete_singleton insert_singleton delete_insert_id insert_union_singleton_l
  insert_union_singleton_r insert_union_l insert_union_r delete_union union_delete_insert
  mapEmpty_union map_union_empty map_union_assoc map_union_idemp map_union_comm
  map_disjoint_spec map_disjoint_alt map_disjoint_sym map_disjoint_empty_l map_disjoint_empty_r
  map_disjoint_singleton_l map_disjoint_singleton_r map_disjoint_insert_l map_disjoint_insert_r
  map_disjoint_delete_l map_disjoint_delete_r map_disjoint_union_l map_disjoint_union_r
  map_disjoint_fmap map_subseteq_spec mapEmpty_subseteq map_subseteq_refl map_subseteq_trans
  map_subseteq_antisymm insert_subseteq insert_subseteq_l insert_mono delete_subseteq
  map_union_subseteq_l map_union_subseteq_r fmap_empty fmap_insert fmap_delete
  map_fmap_singleton map_fmap_union map_fmap_difference map_fmap_id map_fmap_compose
  map_fmap_ext map_difference_diag map_difference_empty delete_difference map_difference_union'
  map_difference_union map_disjoint_difference_l map_disjoint_difference_r MapForall
  MapForall2 mapForall_lookup mapForall_lookup_1 mapForall_empty mapForall_impl
  mapForall_insert_1_1 mapForall_insert_2 mapForall_insert mapForall_delete
  mapForall_singleton mapForall_fmap mapForall_union map_size_empty map_size_empty_inv
  map_size_empty_iff map_size_ne_0_lookup map_size_ne_0_lookup_2 map_size_nonzero_lookup
  map_size_nonzero map_size_insert_None map_size_delete_Some map_size_delete_None
  map_size_delete map_size_insert_Some map_size_insert map_size_singleton map_size_fmap
  map_subseteq_size map_ind mapToList listToMap elem_of_map_to_list NoDup_map_to_list
  NoDup_fst_map_to_list mapToList_empty length_map_to_list length_gmap_to_list
  mapToList_insert mapToList_delete mapFold mapFold_empty mapFold_insert mapFold_ind
  map_filter_empty map_filter_insert_True map_filter_insert_False map_filter_delete
  mapLookup_filter_Some mapLookup_filter_None map_filter_subseteq map_size_filter
  lookup_map_seq lookup_map_seq_0 lookup_map_seq_None mapSeq_cons mapSeq_snoc
  mapSeq_cons_disjoint mapSeq
  domSet gsetToGmap elements listToSet unionList elem_of_gset set_eq set_eq_iff elem_of_empty
  not_elem_of_empty elem_of_singleton elem_of_singleton_2 elem_of_insert_set elem_of_union
  elem_of_intersection elem_of_difference elem_of_subseteq elem_of_disjoint elem_of_weaken
  elem_of_union_l elem_of_union_r not_elem_of_union not_elem_of_singleton union_comm_L
  union_assoc_L union_empty_l_L union_empty_r_L union_idemp_L intersection_comm_L
  difference_diag_L difference_empty_L union_difference_L difference_union_L empty_subseteq
  subseteq_refl union_subseteq_l union_subseteq_r union_subseteq difference_subseteq
  elem_of_subseteq_singleton singleton_subseteq_l disjoint_sym disjoint_union_l disjoint_union_r
  disjoint_singleton_l disjoint_singleton_r disjoint_intersection_L disjoint_difference_l
  singleton_union_difference size_empty size_empty_iff size_singleton set_choose_L
  size_pos_elem_of size_union size_union_alt subseteq_size size_difference
  set_subseteq_size_eq size_1_elem_of elem_of_elements NoDup_elements length_elements
  elem_of_list_to_set listToSet_nil listToSet_cons listToSet_app size_list_to_set
  listToSet_elements elem_of_union_list unionList_app set_ind_L elem_of_dom elem_of_dom'
  elem_of_dom_2 not_elem_of_dom not_elem_of_dom_1 not_elem_of_dom_2 lookup_domSet dom_empty
  dom_empty_L dom_empty_iff dom_empty_iff_L dom_insert dom_insert_L dom_insert_lookup dom_delete
  dom_delete_L dom_singleton dom_singleton_L dom_fmap dom_fmap_L dom_union dom_union_L
  subseteq_dom size_dom map_size_dom map_disjoint_dom dom_map_seq lookup_gset_to_gmap
  lookup_gset_to_gmap_Some lookup_gset_to_gmap_None dom_gset_to_gmap gsetToGmap_empty
  gsetToGmap_union_singleton)

end Perennial

end
