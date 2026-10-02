/-
Finite maps, in the role of stdpp's `gmap`.

`gmap K V` is a partial function with finite support. Equality is extensional
(`gmap.ext`), as with stdpp's canonical `gmap`. Only `DecidableEq K` is needed.
The operations are noncomputable: they exist for specifications, not for
execution.

stdpp notation: `m !! k` is lookup, `<[k := v]> m` is insert, `delete k m` is delete.
-/
import Iris.Std.PartialMap

noncomputable section

namespace Perennial

structure gmap (K : Type u) (V : Type v) where
  lookup : K → Option V
  finite : ∃ l : List K, ∀ k, (lookup k).isSome → k ∈ l

namespace gmap

variable {K : Type u} {V : Type v} [DecidableEq K]

@[ext] theorem ext {m₁ m₂ : gmap K V} (h : ∀ k, m₁.lookup k = m₂.lookup k) : m₁ = m₂ := by
  cases m₁; cases m₂; congr; funext k; exact h k

theorem ext_iff' {m₁ m₂ : gmap K V} : m₁ = m₂ ↔ ∀ k, m₁.lookup k = m₂.lookup k :=
  ⟨fun h _ => h ▸ rfl, ext⟩

def empty : gmap K V := ⟨fun _ => none, ⟨[], by simp⟩⟩

instance : EmptyCollection (gmap K V) := ⟨empty⟩
instance : Inhabited (gmap K V) := ⟨empty⟩

def insert (k : K) (v : V) (m : gmap K V) : gmap K V :=
  ⟨fun k' => if k = k' then some v else m.lookup k',
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨k :: l, fun k' h => ?_⟩
    by_cases e : k = k'
    · simp [e]
    · simp only [e, ite_false] at h; exact List.mem_cons_of_mem _ (hl k' h)⟩

def delete (k : K) (m : gmap K V) : gmap K V :=
  ⟨fun k' => if k = k' then none else m.lookup k',
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k' h => ?_⟩
    by_cases e : k = k'
    · simp [e] at h
    · simp only [e, ite_false] at h; exact hl k' h⟩

def singleton (k : K) (v : V) : gmap K V := insert k v empty

/-- Union, left-biased (stdpp `∪`). -/
def union (m₁ m₂ : gmap K V) : gmap K V :=
  ⟨fun k => (m₁.lookup k).or (m₂.lookup k),
   by
    obtain ⟨l₁, h₁⟩ := m₁.finite
    obtain ⟨l₂, h₂⟩ := m₂.finite
    refine ⟨l₁ ++ l₂, fun k h => ?_⟩
    cases e : m₁.lookup k with
    | some _ => exact List.mem_append_left _ (h₁ k (by simp [e]))
    | none => simp only [e, Option.none_or] at h; exact List.mem_append_right _ (h₂ k h)⟩

instance : Union (gmap K V) := ⟨union⟩

def fmap {V' : Type w} (f : V → V') (m : gmap K V) : gmap K V' :=
  ⟨fun k => (m.lookup k).map f,
   by
    obtain ⟨l, hl⟩ := m.finite
    exact ⟨l, fun k h => hl k (by simpa using h)⟩⟩

def filter (P : K → V → Bool) (m : gmap K V) : gmap K V :=
  ⟨fun k => (m.lookup k).filter (P k),
   by
    obtain ⟨l, hl⟩ := m.finite
    refine ⟨l, fun k h => hl k ?_⟩
    cases e : m.lookup k <;> simp_all⟩

/-- Remove duplicates (keeps the last occurrence). -/
def _root_.Perennial.list_dedup {α} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then list_dedup l else a :: list_dedup l

theorem _root_.Perennial.mem_list_dedup {α} [DecidableEq α] {a : α} {l : List α} :
    a ∈ list_dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [list_dedup]
  | cons b l ih =>
    unfold list_dedup; split
    · rw [ih]; constructor
      · exact List.mem_cons_of_mem _
      · intro h; rcases List.mem_cons.mp h with rfl | h <;> assumption
    · simp [ih]

theorem _root_.Perennial.nodup_list_dedup {α} [DecidableEq α] (l : List α) : (list_dedup l).Nodup := by
  induction l with
  | nil => simp [list_dedup]
  | cons b l ih =>
    unfold list_dedup; split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨fun h' => h (mem_list_dedup.mp h'), ih⟩

def dom_list (m : gmap K V) : List K :=
  (list_dedup (Classical.choose m.finite)).filter (fun k => (m.lookup k).isSome)

/-- The bindings of `m`, in unspecified order (stdpp `map_to_list`). -/
noncomputable def toList (m : gmap K V) : List (K × V) :=
  m.dom_list.filterMap (fun k => (m.lookup k).map (k, ·))

/-- stdpp `dom`, as a membership predicate. -/
def dom (m : gmap K V) (k : K) : Prop := (m.lookup k).isSome

instance : Membership K (gmap K V) := ⟨fun m k => (m.lookup k).isSome⟩

instance (k : K) (m : gmap K V) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable ((m.lookup k).isSome = true))

/-- Number of bindings. -/
noncomputable def size (m : gmap K V) : Nat := m.toList.length

def disjoint (m₁ m₂ : gmap K V) : Prop := ∀ k, (m₁.lookup k).isSome → (m₂.lookup k).isSome → False

def subseteq (m₁ m₂ : gmap K V) : Prop := ∀ k v, m₁.lookup k = some v → m₂.lookup k = some v

instance : HasSubset (gmap K V) := ⟨subseteq⟩

/-- stdpp `list_to_map`; later bindings win. -/
def ofList : List (K × V) → gmap K V
  | [] => empty
  | (k, v) :: l => insert k v (ofList l)

/-- Maps from `List.range`-style index (stdpp `map_seq`). -/
def map_seq (start : Nat) : List V → gmap Nat V
  | [] => empty
  | v :: l => insert start v (map_seq (start + 1) l)

end gmap

/-! ## stdpp-style notation -/

scoped infixl:80 " !! " => gmap.lookup
scoped notation "<[" k " := " v "]>" m:max => gmap.insert k v m
scoped notation "{[" k " := " v "]}" => gmap.singleton k v

namespace gmap

variable {K : Type u} {V : Type v} [DecidableEq K]

@[simp] theorem lookup_empty (k : K) : (∅ : gmap K V) !! k = none := rfl
@[simp] theorem lookup_mk (f : K → Option V) h (k : K) : (gmap.mk f h) !! k = f k := rfl

theorem lookup_insert (m : gmap K V) (k : K) (v : V) : (<[k := v]> m) !! k = some v := by
  simp [insert]

theorem lookup_insert_ne (m : gmap K V) {k k' : K} (v : V) (h : k ≠ k') :
    (<[k := v]> m) !! k' = m !! k' := by
  simp [insert, h]

@[simp] theorem lookup_insert_eq_iff (m : gmap K V) (k k' : K) (v : V) :
    (<[k := v]> m) !! k' = if k = k' then some v else m !! k' := rfl

theorem lookup_delete (m : gmap K V) (k : K) : (delete k m) !! k = none := by
  simp [delete]

theorem lookup_delete_ne (m : gmap K V) {k k' : K} (h : k ≠ k') :
    (delete k m) !! k' = m !! k' := by
  simp [delete, h]

@[simp] theorem lookup_delete_iff (m : gmap K V) (k k' : K) :
    (delete k m) !! k' = if k = k' then none else m !! k' := rfl

@[simp] theorem lookup_singleton_iff (k k' : K) (v : V) :
    ({[k := v]} : gmap K V) !! k' = if k = k' then some v else none := by
  simp [singleton, insert]; rfl

@[simp] theorem lookup_union (m₁ m₂ : gmap K V) (k : K) :
    (m₁ ∪ m₂) !! k = (m₁ !! k).or (m₂ !! k) := rfl

@[simp] theorem lookup_fmap {V'} (f : V → V') (m : gmap K V) (k : K) :
    (fmap f m) !! k = (m !! k).map f := rfl

@[simp] theorem lookup_filter (P : K → V → Bool) (m : gmap K V) (k : K) :
    (filter P m) !! k = (m !! k).filter (P k) := rfl

theorem mem_iff (m : gmap K V) (k : K) : k ∈ m ↔ (m !! k).isSome := Iff.rfl

theorem insert_insert (m : gmap K V) (k : K) (v v' : V) :
    <[k := v]> (<[k := v']> m) = <[k := v]> m := by
  ext k'; simp; split <;> simp

theorem insert_commute (m : gmap K V) {k k' : K} (v v' : V) (h : k ≠ k') :
    <[k := v]> (<[k' := v']> m) = <[k' := v']> (<[k := v]> m) := by
  ext k''; simp; split <;> split <;> simp_all

theorem insert_id (m : gmap K V) (k : K) (v : V) (h : m !! k = some v) : <[k := v]> m = m := by
  ext k'; simp; split <;> simp_all

theorem delete_insert (m : gmap K V) (k : K) (v : V) (h : m !! k = none) :
    delete k (<[k := v]> m) = m := by
  ext k'; simp; split <;> simp_all

theorem insert_delete (m : gmap K V) (k : K) (v : V) :
    <[k := v]> (delete k m) = <[k := v]> m := by
  ext k'; simp; split <;> simp_all

theorem mem_dom_list (m : gmap K V) (k : K) : k ∈ m.dom_list ↔ (m !! k).isSome := by
  unfold dom_list
  constructor
  · intro h; simpa using (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨mem_list_dedup.mpr (Classical.choose_spec m.finite k h), by simpa using h⟩

theorem nodup_dom_list (m : gmap K V) : m.dom_list.Nodup :=
  (nodup_list_dedup _).filter _

theorem mem_toList (m : gmap K V) (k : K) (v : V) : (k, v) ∈ m.toList ↔ m !! k = some v := by
  unfold toList
  simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨k', _, v', h, rfl, rfl⟩; exact h
  · intro h; exact ⟨k, (mem_dom_list m k).mpr (by simp [h]), v, h, rfl, rfl⟩

theorem toList_keys_nodup (m : gmap K V) : (m.toList.map Prod.fst).Nodup := by
  unfold toList
  have hnd := nodup_dom_list m
  generalize m.dom_list = l at hnd ⊢
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

@[simp] theorem toList_empty : (∅ : gmap K V).toList = [] := by
  unfold toList
  apply List.filterMap_eq_nil_iff.mpr
  intro k _; rfl

end gmap

/-! ## iris-lean finite-map instance (so iris-lean's `ghost_map`/`gen_heap` apply). -/

open Iris.Std in
instance gmap.instPartialMap {K : Type u} [DecidableEq K] : PartialMap (gmap K) K where
  get? m k := m !! k
  insert m k v := <[k := v]> m
  delete m k := gmap.delete k m
  empty := gmap.empty
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
instance gmap.instLawfulFiniteMap {K : Type u} [DecidableEq K] : LawfulFiniteMap (gmap K) K where
  toList m := m.toList
  get?_empty _ := rfl
  get?_insert_eq h := by subst h; exact gmap.lookup_insert _ _ _
  get?_insert_ne h := gmap.lookup_insert_ne _ _ h
  get?_delete_eq h := by subst h; exact gmap.lookup_delete _ _
  get?_delete_ne h := gmap.lookup_delete_ne _ h
  get?_bindAlter := rfl
  get?_merge := rfl
  equiv_iff_eq := ⟨fun h => gmap.ext h, fun h => h ▸ fun _ => rfl⟩
  toList_empty := gmap.toList_empty
  toList_noDupKeys := gmap.toList_keys_nodup _
  toList_get := gmap.mem_toList _ _ _

/-- Finite sets, in the role of stdpp's `gset`. -/
abbrev gset (K : Type u) := gmap K Unit

end Perennial

end
