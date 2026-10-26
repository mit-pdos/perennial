/-
The map points-to `mref ↦${dq} m`
(`ownMap`) and specs for the map operations (insert, delete, lookup, make,
clear, `for range`).

Notes:
* Maps are `Perennial.gmap K V`, which only needs `DecidableEq K`.
* The map instructions compare keys with Go's `==` (see `Perennial/Golang/Defn/Map.lean`), so
  the specs need, of the key `k` an operation is given, that `k == k'` returns
  `decide (k = k')` for every `k' : K` (`SafeMapKey`): an `==` that is equality of values, at
  `k`. Every strictly comparable key type has it (`safeMapKey_of_go_eq`); a float `NaN` key, or
  an interface key holding one, does not.
* `ownMap` represents `m` by its entries in some order (`map.lookupL`), each with the id
  `(k, 0)` (`map.toE`).
* In `wp_map_for_range`, the fact that `keys` lists the domain of `m` is stated
  as `∀ k, k ∈ keys ↔ (m !! k).isSome`.
* `map.forRange` does not hold the map across the body, so a body may write the
  map it ranges over: `wp_map_for_range_gen` (any change; keys deleted before
  they are reached are skipped), `wp_map_for_range_mut_keys`/`wp_map_for_range_mut`
  (the body changes only the current key), `wp_map_for_range` (read only).
* `wp_map_len` and `pure_wp_map_nil_len` are stated at any type whose
  underlying type is a map (see `len_map` in `Perennial/Golang/Defn/Map.lean`),
  not only at the literal `go.MapType key_type elem_type`.
-/
module

public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Theory.Array
public import Perennial.Golang.Defn.Map
public import Perennial.GooseLang.IPersist

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The keys a map points-to of key type `K` may hold. All of `K` (`mapKeys_all`), but for
interfaces (`mapKeys_interface`): the model does not type an interface's dynamic value, so `==`
between two interfaces is known only for some forms. A proof that needs other interface keys can
give its own instance. -/
class MapKeys (K : Type) where
  keyOk : K → Prop

instance (priority := low) mapKeys_all (K : Type) : MapKeys K := ⟨fun _ => True⟩

/-- Interface keys: `nil`, or a pointer. -/
instance mapKeys_interface [GooseExts] [GoGlobalContext] : MapKeys GoInterface :=
  ⟨fun i => i = interface.nil ∨ ∃ (t : go.GoType) (l : Loc), i = interface.mkOk (go.PointerType t) #l⟩

/-! ## Maps as lists of entries -/

namespace map
section pure
variable [GooseExts] [GoGlobalContext]
variable {K V : Type} [DecidableEq K]

/-- The id of the entry of key `k` (`freshId` of a key no entry has). -/
def keyId (k : K) : val := PairV #k (idV 0)

/-- The entry `k ↦ v`. -/
def toE (p : K × V) : Entry := ⟨keyId p.1, #p.1, #p.2⟩

def lookupL (k : K) : List (K × V) → Option V
  | [] => none
  | p :: ps => if k = p.1 then some p.2 else lookupL k ps

def insertL (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | p :: ps => if k = p.1 then (k, v) :: ps else p :: insertL k v ps

def deleteL (k : K) : List (K × V) → List (K × V)
  | [] => []
  | p :: ps => if k = p.1 then ps else p :: deleteL k ps

theorem lookupL_eq_none_iff (k : K) (ps : List (K × V)) :
    lookupL k ps = none ↔ k ∉ ps.map Prod.fst := by
  induction ps with
  | nil => simp [lookupL]
  | cons p ps ih =>
    by_cases h : k = p.1 <;> simp [lookupL, h, ih]

theorem lookupL_insertL (k k' : K) (v : V) (ps : List (K × V)) :
    lookupL k' (insertL k v ps) = if k' = k then some v else lookupL k' ps := by
  induction ps with
  | nil => simp [lookupL, insertL]
  | cons p ps ih =>
    obtain ⟨pk, pv⟩ := p
    by_cases h : k = pk
    · subst h; by_cases h' : k' = k <;> simp [lookupL, insertL, h']
    · by_cases h' : k' = pk
      · subst h'; simp [lookupL, insertL, h, Ne.symm h]
      · simp [lookupL, insertL, h, h', ih]

theorem mem_keys_insertL (k k' : K) (v : V) (ps : List (K × V)) :
    k' ∈ (insertL k v ps).map Prod.fst ↔ k' = k ∨ k' ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [insertL]
  | cons p ps ih =>
    by_cases h : k = p.1
    · subst h; simp [insertL]
    · simp only [insertL, h, ite_false, List.map_cons, List.mem_cons, ih]
      exact or_left_comm

theorem nodup_insertL (k : K) (v : V) (ps : List (K × V)) (h : (ps.map Prod.fst).Nodup) :
    ((insertL k v ps).map Prod.fst).Nodup := by
  induction ps with
  | nil => simp [insertL]
  | cons p ps ih =>
    rw [List.map_cons, List.nodup_cons] at h
    by_cases hk : k = p.1
    · subst hk; simpa [insertL] using h
    · simp only [insertL, hk, ite_false, List.map_cons, List.nodup_cons, mem_keys_insertL]
      refine ⟨?_, ih h.2⟩
      rintro (h' | h')
      · exact hk h'.symm
      · exact h.1 h'

theorem keyOk_insertL [MapKeys K] (k : K) (v : V) (ps : List (K × V))
    (h : ∀ p ∈ ps, MapKeys.keyOk p.1) (hk : MapKeys.keyOk k) :
    ∀ p ∈ insertL k v ps, MapKeys.keyOk p.1 := by
  induction ps with
  | nil => simpa [insertL] using hk
  | cons p ps ih =>
    by_cases hp : k = p.1
    · simp only [insertL, hp, ite_true, List.mem_cons]
      rintro q (rfl | hq)
      · rw [← hp]; exact hk
      · exact h q (List.mem_cons_of_mem _ hq)
    · simp only [insertL, hp, ite_false, List.mem_cons]
      rintro q (rfl | hq)
      · exact h q (List.mem_cons_self ..)
      · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) q hq

theorem deleteL_sublist (k : K) (ps : List (K × V)) : (deleteL k ps).Sublist ps := by
  induction ps with
  | nil => simp [deleteL]
  | cons p ps ih =>
    by_cases h : k = p.1
    · simp only [deleteL, h, ite_true]; exact List.sublist_cons_self _ _
    · simp only [deleteL, h, ite_false]; exact ih.cons₂ _

theorem nodup_deleteL (k : K) (ps : List (K × V)) (h : (ps.map Prod.fst).Nodup) :
    ((deleteL k ps).map Prod.fst).Nodup :=
  h.sublist ((deleteL_sublist k ps).map _)

theorem lookupL_deleteL (k k' : K) (ps : List (K × V)) (hnd : (ps.map Prod.fst).Nodup) :
    lookupL k' (deleteL k ps) = if k' = k then none else lookupL k' ps := by
  induction ps with
  | nil => simp [lookupL, deleteL]
  | cons p ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨pk, pv⟩ := p
    by_cases h : k = pk
    · subst h
      by_cases h' : k' = k
      · subst h'; simp only [deleteL, ite_true]; exact (lookupL_eq_none_iff _ _).2 hnd.1
      · simp [deleteL, lookupL, h']
    · by_cases h' : k' = pk
      · subst h'; simp [lookupL, deleteL, h, Ne.symm h]
      · simp [lookupL, deleteL, h, h', ih hnd.2]

variable [go.IntoValInj K]

theorem keyId_inj : Function.Injective (keyId (K := K)) := by
  intro a b h
  simp only [keyId, val.PairV.injEq] at h
  exact go.intoVal_inj h.1

theorem freshId_keyId (k : K) (ps : List (K × V)) (h : k ∉ ps.map Prod.fst) :
    freshId #k (ps.map toE) = keyId k := by
  have hfree : decide (PairV #k (idV 0) ∉ (ps.map toE).map (·.id)) = true := by
    simp only [decide_eq_true_eq, List.map_map, List.mem_map, Function.comp_def, toE, not_exists,
      not_and]
    intro p hp heq
    exact h (List.mem_map.2 ⟨p, hp, keyId_inj heq⟩)
  simp only [freshId, List.range_succ_eq_map, List.find?_cons, hfree, Option.getD_some]
  rfl

theorem lookupIdVal_keyId (dv : val) (k : K) (ps : List (K × V)) :
    lookupIdVal dv (ps.map toE) (keyId k) =
      (match lookupL k ps with
       | some v => PairV (PairV #k #v) #true
       | none => PairV (PairV #() dv) #false) := by
  induction ps with
  | nil => simp [lookupIdVal, lookupL]
  | cons p ps ih =>
    by_cases h : k = p.1
    · subst h; simp [lookupIdVal, lookupL, toE]
    · have h' : ¬ keyId p.1 = keyId k := fun e => h (keyId_inj e).symm
      simp only [lookupIdVal, List.map_cons, List.find?_cons, toE, h', decide_false] at ih ⊢
      simp only [lookupL, h, ite_false]
      exact ih

omit [DecidableEq K] in
theorem toE_inj [go.IntoValInj V] : Function.Injective (toE (K := K) (V := V)) := by
  intro a b h
  simp only [toE, Entry.mk.injEq] at h
  exact Prod.ext (go.intoVal_inj h.2.1) (go.intoVal_inj h.2.2)

theorem entryV_inj : Function.Injective entryV := by
  intro a b h
  cases a; cases b
  simp only [entryV, val.PairV.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1 h2 h3; rfl

theorem list_map_inj {α β : Type} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro l1 l2 h
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, ih h.2]

theorem mapV_inj (dv dv' : val) (es es' : List Entry) (h : mapV dv es = mapV dv' es') :
    es = es' := by
  simp only [mapV, val.PairV.injEq, val.ArrayV.injEq] at h
  exact list_map_inj _ entryV_inj h.2

end pure
end map

noncomputable section defns
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- `k` is a safe map key at `key_type` (see the comment in `Perennial/Golang/Defn/Map.lean`): a
key a map may hold (`MapKeys.keyOk`), and comparing it with any such key `k'` does not panic and
is equality of values. A float `NaN` is not one (`NaN != NaN`). -/
class SafeMapKey {K : Type} [DecidableEq K] [keys : MapKeys K] (key_type : go.GoType) (k : K) :
    Prop where
  key_ok : MapKeys.keyOk k
  wp_go_eq_map_key : ∀ (k' : K), MapKeys.keyOk k' → ∀ (s : Stuckness) (E : CoPset)
    (Φ : val → IProp GF), Φ #(decide (k = k')) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #k'))) @ s; E {{ Φ }}

export SafeMapKey (key_ok wp_go_eq_map_key)

/-- A key type whose `==` is equality of values: every key is safe. -/
instance safeMapKey_of_go_eq {K : Type} [DecidableEq K] (key_type : go.GoType) (k : K)
    [h : ∀ k' : K, ⟦GoOp GoEquals key_type, (#k, #k')⟧ ⤳ #(decide (k = k'))] :
    SafeMapKey (GF := GF) (keys := mapKeys_all K) key_type k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

theorem interface_mkOk_inj (t t' : go.GoType) (v v' : val) :
    interface.mkOk t v = interface.mkOk t' v' ↔ t = t' ∧ v = v' := by
  simp [interface.mkOk]

/-- An interface key holding a pointer, at any interface key type. -/
instance safeMapKey_interface_pointer (key_type : go.GoType) {elems : List go.InterfaceElem}
    [key_type ↓u go.InterfaceType elems] (t : go.GoType) (l : Loc) :
    SafeMapKey (GF := GF) key_type (interface.mkOk (go.PointerType t) #l) where
  key_ok := Or.inr ⟨t, l, rfl⟩
  wp_go_eq_map_key k' hk' s E Φ := by
    rcases hk' with rfl | ⟨t', l', rfl⟩
    · have h : decide (interface.mkOk (go.PointerType t) #l = (interface.nil : GoInterface)) =
          false := by simp [interface.mkOk]
      rw [h]
      iintro HΦ
      wp_auto
      iapply HΦ
    · by_cases ht : t = t'
      · subst ht
        have h : decide (interface.mkOk (go.PointerType t) #l =
            interface.mkOk (go.PointerType t) #l') = decide (l = l') := by
          simp only [interface_mkOk_inj, _root_.true_and]
          by_cases hl : l = l'
          · subst hl; simp
          · have : ¬ (#l : val) = #l' := fun e => hl (GoGlobalContext.intoVal_inj_loc e)
            simp [hl, this]
        rw [h]
        iintro HΦ
        wp_auto
        iapply HΦ
      · have h : decide (interface.mkOk (go.PointerType t) #l =
            interface.mkOk (go.PointerType t') #l') = false := by
          simp [interface_mkOk_inj, ht]
        have ht' : ¬ go.PointerType t = go.PointerType t' := by simpa using ht
        rw [h]
        iintro HΦ
        wp_pures
        rw [if_neg ht']
        wp_auto
        iapply HΦ

/-- The nil interface as a key, at any interface key type. -/
instance safeMapKey_interface_nil (key_type : go.GoType) {elems : List go.InterfaceElem}
    [key_type ↓u go.InterfaceType elems] :
    SafeMapKey (GF := GF) key_type (interface.nil : GoInterface) where
  key_ok := Or.inl rfl
  wp_go_eq_map_key k' hk' s E Φ := by
    rcases hk' with rfl | ⟨t', l', rfl⟩
    · rw [show decide ((interface.nil : GoInterface) = interface.nil) = true by simp]
      iintro HΦ
      wp_auto
      iapply HΦ
    · rw [show decide ((interface.nil : GoInterface) = interface.mkOk (go.PointerType t') #l') =
        false by simp [interface.mkOk]]
      iintro HΦ
      wp_auto
      iapply HΦ

-- TODO: reading from nil map. Want to say that an owned map is not nil, which
-- requires knowing that wp_ref gives non-null pointers.

variable {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]

/-- `mv` is the map `m` with the entries `ps`. -/
def map.Repr (m : GMap K V) (mv : val) (ps : List (K × V)) : Prop :=
  mv = map.mapV #(zero_val V) (ps.map map.toE) ∧ (ps.map Prod.fst).Nodup ∧
    (∀ p ∈ ps, MapKeys.keyOk p.1) ∧
    ∀ k, m !! k = map.lookupL k ps

/-- The map points-to. -/
def ownMapDef (mptr : Loc) (dq : DFrac) (m : GMap K V) : IProp GF :=
  iprop(∃ (mv : val) (ps : List (K × V)),
    "Hown" ∷ heapPointsto mptr dq mv ∗
    "%Hrepr" ∷ ⌜map.Repr m mv ps⌝)

@[irreducible] def ownMap (mptr : Loc) (dq : DFrac) (m : GMap K V) : IProp GF :=
  ownMapDef mptr dq m

theorem ownMap_unseal : @ownMap = @ownMapDef := by
  funext; with_unfolding_all rfl

end defns

/-- `mref ↦${dq} m`: the map at `mref` has contents `m`. -/
scoped notation:50 mref:50 " ↦${" dq "} " m:50 => ownMap mref dq m
/-- `mref ↦$ m`: the map points-to with full ownership. -/
scoped notation:50 mref:50 " ↦$ " m:50 => ownMap mref (DFrac.own 1) m
/-- `mref ↦$□ m`: persistent map points-to. -/
scoped notation:50 mref:50 " ↦$□ " m:50 => ownMap mref DFrac.discard m

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]

theorem map.mapV_not_panic (dv : val) (es : List map.Entry) : (map.mapV dv es).isPanic = false := by
  simp [map.mapV]

/-- The lookup instruction's comparisons, on the entries of `ps`. -/
theorem wp_lookupExpr (key_type : go.GoType) (k : K) [Hk : SafeMapKey (GF := GF) key_type k]
    (ps : List (K × V)) (hps : ∀ p ∈ ps, MapKeys.keyOk p.1) (Φ : val → IProp GF) :
    Φ (match map.lookupL k ps with
       | some v => PairV #v #true
       | none => PairV #(zero_val V) #false) ⊢
    WP (map.lookupExpr key_type #k #(zero_val V) (ps.map map.toE)) @ s; E {{ Φ }} := by
  induction ps with
  | nil =>
    iintro HΦ
    simp only [List.map_nil, map.lookupExpr, map.lookupL]
    wp_pures
    iapply HΦ
  | cons p ps ih =>
    iintro HΦ
    simp only [List.map_cons, map.lookupExpr, map.keyEq, map.toE]
    wp_pures
    wp_bind (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #p.1)))
    iapply (Hk.wp_go_eq_map_key p.1 (hps p (List.mem_cons_self ..)))
    by_cases h : k = p.1
    · simp only [h, _root_.decide_true, map.lookupL, ite_true]
      wp_pures
      iapply HΦ
    · simp only [h, _root_.decide_false, map.lookupL, ite_false]
      wp_pures
      iapply ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) $$ HΦ

/-- The insert instruction's comparisons, on the entries of `pre ++ ps` (`pre` checked). The new
entry's id is `id`, the key's own id if it is new. -/
theorem wp_insertExpr (key_type : go.GoType) (k : K) [Hk : SafeMapKey (GF := GF) key_type k]
    (v : V) (dv id : val) (pre ps : List (K × V))
    (hid : k ∉ ps.map Prod.fst → id = map.keyId k) (hps : ∀ p ∈ ps, MapKeys.keyOk p.1) (Φ : val → IProp GF) :
    Φ (map.mapV dv ((pre ++ map.insertL k v ps).map map.toE)) ⊢
    WP (map.insertExpr key_type #k #v dv id (pre.map map.toE) (ps.map map.toE)) @ s; E
      {{ Φ }} := by
  induction ps generalizing pre with
  | nil =>
    iintro HΦ
    rw [hid (by simp)]
    simp only [List.map_nil, map.insertExpr, map.insertL, List.map_append, List.map_cons, map.toE]
    wp_pures
    iapply HΦ
  | cons p ps ih =>
    iintro HΦ
    simp only [List.map_cons, map.insertExpr, map.keyEq]
    wp_pures
    wp_bind (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #p.1)))
    iapply (Hk.wp_go_eq_map_key p.1 (hps p (List.mem_cons_self ..)))
    by_cases h : k = p.1
    · subst h
      simp only [decide_true, map.insertL, ite_true, List.map_append, List.map_cons, map.toE]
      wp_pures
      iapply HΦ
    · simp only [h, _root_.decide_false, map.insertL, ite_false]
      wp_pures
      have hid' : k ∉ ps.map Prod.fst → id = map.keyId k := fun hn =>
        hid (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨h, hn⟩)
      have hpre : pre.map map.toE ++ [map.toE p] = (pre ++ [p]).map map.toE := by simp
      rw [hpre]
      iapply ih (pre ++ [p]) hid' (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iexact HΦ

/-- The delete instruction's comparisons, on the entries of `pre ++ ps` (`pre` checked). -/
theorem wp_deleteExpr (key_type : go.GoType) (k : K) [Hk : SafeMapKey (GF := GF) key_type k]
    (dv : val) (pre ps : List (K × V)) (hps : ∀ p ∈ ps, MapKeys.keyOk p.1) (Φ : val → IProp GF) :
    Φ (map.mapV dv ((pre ++ map.deleteL k ps).map map.toE)) ⊢
    WP (map.deleteExpr key_type #k dv (pre.map map.toE) (ps.map map.toE)) @ s; E {{ Φ }} := by
  induction ps generalizing pre with
  | nil =>
    iintro HΦ
    simp only [List.map_nil, map.deleteExpr, map.deleteL, List.append_nil]
    wp_pures
    iapply HΦ
  | cons p ps ih =>
    iintro HΦ
    simp only [List.map_cons, map.deleteExpr, map.keyEq]
    wp_pures
    wp_bind (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #p.1)))
    iapply (Hk.wp_go_eq_map_key p.1 (hps p (List.mem_cons_self ..)))
    by_cases h : k = p.1
    · subst h
      simp only [decide_true, map.deleteL, ite_true, List.map_append]
      wp_pures
      iapply HΦ
    · simp only [h, _root_.decide_false, map.deleteL, ite_false]
      wp_pures
      have hpre : pre.map map.toE ++ [map.toE p] = (pre ++ [p]).map map.toE := by simp
      rw [hpre]
      iapply ih (pre ++ [p]) (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iexact HΦ

instance ownMap_timeless (mptr : Loc) (dq : DFrac) (m : GMap K V) :
    Timeless (ownMap (GF := GF) mptr dq m) := by
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]; infer_instance

theorem map.Repr_insert (m : GMap K V) (ps : List (K × V)) (k : K) (v : V)
    (Hnd : (ps.map Prod.fst).Nodup) (Hok : ∀ p ∈ ps, MapKeys.keyOk p.1)
    (Hagree : ∀ k, m !! k = map.lookupL k ps) (hk : MapKeys.keyOk k) :
    map.Repr (<[k := v]> m) (map.mapV #(zero_val V) ((map.insertL k v ps).map map.toE))
      (map.insertL k v ps) := by
  refine ⟨rfl, map.nodup_insertL k v ps Hnd, map.keyOk_insertL k v ps Hok hk, fun k' => ?_⟩
  rw [map.lookupL_insertL]
  by_cases h : k' = k
  · subst h; simp [GMap.lookup_insert]
  · simp only [h, ite_false, GMap.lookup_insert_ne _ _ (Ne.symm h)]; exact Hagree k'

theorem map.Repr_delete (m : GMap K V) (ps : List (K × V)) (k : K)
    (Hnd : (ps.map Prod.fst).Nodup) (Hok : ∀ p ∈ ps, MapKeys.keyOk p.1)
    (Hagree : ∀ k, m !! k = map.lookupL k ps) :
    map.Repr (GMap.delete k m) (map.mapV #(zero_val V) ((map.deleteL k ps).map map.toE))
      (map.deleteL k ps) := by
  refine ⟨rfl, map.nodup_deleteL k ps Hnd,
    fun p hp => Hok p ((map.deleteL_sublist k ps).subset hp), fun k' => ?_⟩
  rw [map.lookupL_deleteL k k' ps Hnd]
  by_cases h : k' = k
  · subst h; simp [GMap.lookup_delete]
  · simp only [h, ite_false, GMap.lookup_delete_ne _ (Ne.symm h)]; exact Hagree k'

theorem wp_mapInsert (key_type : go.GoType) (l : Loc) (m : GMap K V) (k : K) (v : V)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (App (Val (map.insert key_type)) (Val #l)) (Val #k)) (Val #v)) @ s; E
    {{ RET #(); l ↦$ (<[k := v]> m) }} := by
  rw [ownMap_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  obtain ⟨rfl, Hnd, Hok, Hagree⟩ := Hrepr
  wp_call
  wp_apply (wp_go_eq_map_key (GF := GF) (key_type := key_type) (k := k) k Hsafe.key_ok)
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  wp_pures
  have hid : k ∉ ps.map Prod.fst → map.freshId #k (ps.map map.toE) = map.keyId k :=
    map.freshId_keyId k ps
  have Hins := wp_insertExpr (GF := GF) (s := s) (E := E) key_type k v #(zero_val V) _ [] ps hid Hok
  simp only [List.map_nil, List.nil_append] at Hins
  wp_bind (map.insertExpr key_type #k #v #(zero_val V) (map.freshId #k (ps.map map.toE)) []
    (ps.map map.toE))
  iapply Hins
  wp_apply (_internal_wp_untyped_store _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  iapply HΦ
  unfold ownMapDef
  simp only [named]
  iexists _, (map.insertL k v ps)
  iframe Hown
  ipureintro
  exact map.Repr_insert m ps k v Hnd Hok Hagree Hsafe.key_ok

theorem wp_mapDelete (l : Loc) (m : GMap K V) (k : K) (key_type elem_type : go.GoType)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [go.MapType key_type elem_type])) (Val #l)) (Val #k)) @ s; E
    {{ RET #(); l ↦$ (GMap.delete k m) }} := by
  wp_start as Hm
  rw [ownMap_unseal]
  iNamed Hm
  obtain ⟨rfl, Hnd, Hok, Hagree⟩ := Hrepr
  wp_apply (wp_go_eq_map_key (GF := GF) (key_type := key_type) (k := k) k Hsafe.key_ok)
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  wp_pures
  have Hdel := wp_deleteExpr (GF := GF) (s := s) (E := E) key_type k #(zero_val V) [] ps Hok
  simp only [List.map_nil, List.nil_append] at Hdel
  wp_bind (map.deleteExpr key_type #k #(zero_val V) [] (ps.map map.toE))
  iapply Hdel
  wp_apply (_internal_wp_untyped_store _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  iapply HΦ
  unfold ownMapDef
  simp only [named]
  iexists _, (map.deleteL k ps)
  iframe Hown
  ipureintro
  exact map.Repr_delete m ps k Hnd Hok Hagree

theorem wp_map_lookup2 (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (k : K)
    (dq : DFrac) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (App (Val (map.lookup2 key_type elem_type)) (Val #mref)) (Val #k)) @ s; E
    {{ RET (PairV #((m !! k).getD (zero_val V)) #(decide ((m !! k).isSome))); mref ↦${dq} m }} := by
  rw [ownMap_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hown
  obtain ⟨rfl, Hnd, Hok, Hagree⟩ := Hrepr
  wp_call
  wp_apply (wp_go_eq_map_key (GF := GF) (key_type := key_type) (k := k) k Hsafe.key_ok)
  rw [decide_eq_false (show ¬ mref = map.nil from Hnn)]
  wp_pures
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  wp_pures
  iapply wp_lookupExpr key_type k ps Hok
  rw [← Hagree k]
  cases hk : m !! k <;>
  · simp only [Option.getD_none, Option.getD_some, Option.isSome_none, Option.isSome_some,
      _root_.decide_true, _root_.decide_false, Bool.false_eq_true]
    iapply HΦ
    unfold ownMapDef
    simp only [named]
    iexists _, ps
    iframe Hown
    ipureintro
    exact ⟨rfl, Hnd, Hok, Hagree⟩

instance pure_wp_map_nil_lookup2 (key_type elem_type : go.GoType) (k : K)
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type]
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (App (Val (map.lookup2 key_type elem_type)) (Val #map.nil)) (Val #k))
      (Val (PairV #(zero_val V) #false)) :=
  pure_wp_val True _ (PairV #(zero_val V) #false) fun s E Φ _ => by
    iintro HΦ
    wp_call_lc Hlc
    wp_apply (wp_go_eq_map_key (GF := GF) (key_type := key_type) (k := k) k Hsafe.key_ok)
    iapply HΦ $$ Hlc

theorem wp_map_lookup1 (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (k : K)
    (dq : DFrac) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (App (Val (map.lookup1 key_type elem_type)) (Val #mref)) (Val #k)) @ s; E
    {{ RET #((m !! k).getD (zero_val V)); mref ↦${dq} m }} := by
  iintro %Φ Hm HΦ
  wp_call
  wp_apply wp_map_lookup2 key_type elem_type mref m k dq $$ Hm with Hm
  iapply HΦ $$ Hm

instance pure_wp_map_nil_lookup1 (key_type elem_type : go.GoType) (k : K)
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type]
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (App (Val (map.lookup1 key_type elem_type)) (Val #map.nil)) (Val #k))
      (Val #(zero_val V)) :=
  pure_wp_val True _ #(zero_val V) fun s E Φ _ => by
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

theorem wp_map_make2 (len : w64) (key_type elem_type : go.GoType)
    [TypeRepr key_type K] -- to automatically fill in `K`
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.MapType key_type elem_type])) (Val #len)) @ s; E
    {{ (mref : Loc), RET #mref; mref ↦$ (∅ : GMap K V) }} := by
  wp_start
  wp_apply (wp_alloc_untyped _ (map.mapV_not_panic _ _)) with %l Hl
  iapply HΦ
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]
  iexists _, ([] : List (K × V))
  iframe Hl
  ipureintro
  exact ⟨rfl, List.nodup_nil, (fun _ h => nomatch h), fun k => rfl⟩

theorem wp_map_make1 (key_type elem_type : go.GoType) [TypeRepr key_type K]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [go.MapType key_type elem_type])) (Val #())) @ s; E
    {{ (mref : Loc), RET #mref; mref ↦$ (∅ : GMap K V) }} := by
  wp_start
  wp_apply (wp_map_make2 (K := K) (V := V) (W64 0) key_type elem_type) with %mref Hm
  iapply HΦ $$ Hm

theorem wp_map_clear (mref : Loc) (m : GMap K V) (key_type elem_type : go.GoType)
    [TypeRepr key_type K] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (mref ↦$ m : IProp GF) }}
      (App (Val #(functions go.clear [go.MapType key_type elem_type])) (Val #mref)) @ s; E
    {{ RET #(); mref ↦$ (∅ : GMap K V) }} := by
  wp_start as Hm
  wp_apply (wp_map_make1 (K := K) (V := V) key_type elem_type) with %m' Hm'
  rw [ownMap_unseal]
  unfold ownMapDef
  iNamed Hm
  obtain ⟨rfl, -, -, -⟩ := Hrepr
  icases Hm' with ⟨%mv', %ps', Hown', %Hrepr'⟩
  obtain ⟨rfl, Hnd', Hok', Hagree'⟩ := Hrepr'
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown' with Hown'
  wp_apply (_internal_wp_untyped_store _ _ _ (by simp)) $$ Hown with Hown
  iapply HΦ
  simp only [named]
  iexists _, ps'
  iframe Hown
  ipureintro
  exact ⟨rfl, Hnd', Hok', Hagree'⟩

theorem ownMap_not_nil (mref : Loc) (m : GMap K V) (dq : DFrac) :
    (mref ↦${dq} m : IProp GF) ⊢ ⌜mref ≠ map.nil⌝ := by
  rw [ownMap_unseal]
  iintro Hm
  iNamed Hm
  ihave %H := heapPointsto_non_null _ _ _ $$ Hown
  ipureintro; exact H

instance ownMap_discarded_persist (mref : Loc) (m : GMap K V) :
    Persistent (ownMap (GF := GF) mref DFrac.discard m) := by
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]; infer_instance

theorem ownMap_persist (mref : Loc) (dq : DFrac) (m : GMap K V) :
    (mref ↦${dq} m : IProp GF) ⊢ |==> mref ↦$□ m := by
  rw [ownMap_unseal]
  iintro Hm
  iNamed Hm
  imod heapPointsto_persist _ _ _ $$ Hown with Hown
  imodintro
  unfold ownMapDef
  simp only [named]
  iexists mv, ps
  iframe Hown
  ipureintro
  exact Hrepr

instance ownMap_update_into_persistently (mref : Loc) (dq : DFrac) (m : GMap K V) :
    UpdateIntoPersistently (ownMap (GF := GF) mref dq m) (ownMap mref DFrac.discard m) where
  update_into_persistently := by
    iintro H
    imod ownMap_persist mref dq m $$ H with #H
    imodintro
    iexact H

/-- A map points-to splits and combines by fraction. -/
theorem ownMap_fractional (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, ps; simp only [named]; iframe H1; ipureintro; exact Hrepr
      · iexists mv, ps; simp only [named]; iframe H2; ipureintro; exact Hrepr
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      icases H1 with ⟨%mv, %ps1, Hown1, %Hrepr1⟩
      icases H2 with ⟨%mv2, %ps2, Hown2, %Hrepr2⟩
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, ps1
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact Hrepr1

/-- Two shares of a map points-to agree on the map (for values whose Go values are injective). -/
theorem ownMap_agree [go.IntoValInj V] (mref : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    ownMap (GF := GF) mref dq1 m1 ∗ ownMap (GF := GF) mref dq2 m2 ⊢ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  iintro ⟨H1, H2⟩
  unfold ownMapDef
  icases H1 with ⟨%mv1, %ps1, Hown1, %Hrepr1⟩
  icases H2 with ⟨%mv2, %ps2, Hown2, %Hrepr2⟩
  icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
  subst Hmv
  ipureintro
  obtain ⟨Hmv1, -, -, Hagree1⟩ := Hrepr1
  obtain ⟨Hmv2, -, -, Hagree2⟩ := Hrepr2
  have hps : ps1 = ps2 :=
    map.list_map_inj _ map.toE_inj (map.mapV_inj _ _ _ _ (Hmv1.symm.trans Hmv2))
  subst hps
  apply GMap.ext
  intro k
  change m1 !! k = m2 !! k
  rw [Hagree1, Hagree2]

end lemmas
/-! ## `for range` -/

theorem list_exists_map_of_forall {α β : Type} (f : α → β) (l : List β)
    (h : ∀ b ∈ l, ∃ a, b = f a) : ∃ l' : List α, l = l'.map f := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    obtain ⟨a, rfl⟩ := h b (List.mem_cons_self ..)
    obtain ⟨l', rfl⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact ⟨a :: l', rfl⟩

theorem list_mem_map_inj {α β : Type} (f : α → β) (hf : Function.Injective f) (l : List α)
    (a : α) : f a ∈ l.map f ↔ a ∈ l := by
  simp only [List.mem_map]
  exact ⟨fun ⟨b, hb, e⟩ => hf e ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem list_nodup_of_map {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) :
    l.Nodup :=
  (List.pairwise_map.1 h).imp (fun h e => h (congrArg f e))

theorem list_nodup_getElem?_inj {α} (l : List α) (h : l.Nodup) (i j : Nat) (a : α)
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  rw [List.getElem?_eq_some_iff] at hi hj
  obtain ⟨hi, ei⟩ := hi
  obtain ⟨hj, ej⟩ := hj
  have hp := List.pairwise_iff_getElem.1 h
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (ei.trans ej.symm) (hp i j hi hj hlt)
  · exact heq
  · exact absurd (ej.trans ei.symm) (hp j i hj hi hgt)

section forRange
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_InternalMapForRange (dv : val) (es : List map.Entry) (body : val)
    (key_type elem_type : go.GoType) (Φ : val → IProp GF) :
    (∀ e', ⌜is_go_step_pure (InternalMapForRange key_type elem_type)
        (PairV (map.mapV dv es) body) e'⌝ -∗ WP e' @ s; E {{ Φ }}) -∗
    WP (App (Val (GoInstruction (InternalMapForRange key_type elem_type)))
      (Val (PairV (map.mapV dv es) body))) @ s; E {{ Φ }} := by
  iintro HΦ
  have hstep := go.internal_map_for_range_step dv es body key_type elem_type
  iapply wp_GoInstruction' (s := s) (E := E) (InternalMapForRange key_type elem_type)
    (PairV (map.mapV dv es) body) Φ
    (fun gs => by
      have h : ∃ e, is_go_step_pure (InternalMapForRange key_type elem_type)
          (PairV (map.mapV dv es) body) e := by
        rw [hstep]; exact ⟨_, es.map (·.id), List.Perm.refl _, rfl⟩
      obtain ⟨e, he⟩ := h
      exact ⟨e, gs, he, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure (InternalMapForRange key_type elem_type)
      (PairV (map.mapV dv es) body) e' := Hp
  imodintro
  iframe Hctx
  iapply HΦ $$ %e' %Hp'

variable {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V] [go.IntoValInj K]

/-- The postcondition of a `for range` loop body over a map. FIXME: seal. -/
def forMapPostcondition (P : IProp GF) (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continueVal⌝ ∗ P) ∨
    (⌜bv = executeVal⌝ ∗ P) ∨
    (⌜bv = breakVal⌝ ∗ Φ executeVal) ∨
    (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv))

/-- Reading the map cell: the value read is the map's entries `ps`. -/
theorem wp_ownMap_read (mref : Loc) (dq : DFrac) (m : GMap K V) (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ ps : List (K × V),
      ⌜(ps.map Prod.fst).Nodup ∧ ∀ k, m !! k = map.lookupL k ps⌝ -∗
      mref ↦${dq} m -∗ Φ (map.mapV #(zero_val V) (ps.map map.toE))) -∗
    WP (App (Val Read) (Val #mref)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  rw [ownMap_unseal]
  iNamed Hm
  obtain ⟨rfl, Hnd, Hok, Hagree⟩ := Hrepr
  wp_apply (_internal_wp_untyped_read _ _ _ (map.mapV_not_panic _ _)) $$ Hown with Hown
  iapply HΦ $$ %ps %(⟨Hnd, Hagree⟩)
  unfold ownMapDef
  simp only [named]
  iexists _, ps
  iframe Hown
  ipureintro
  exact ⟨rfl, Hnd, Hok, Hagree⟩

/-- The keys of a map whose entries are `ps`, from a permutation of their ids. -/
theorem map.keys_of_ids_perm (m : GMap K V) (ps : List (K × V))
    (Hnd : (ps.map Prod.fst).Nodup) (Hagree : ∀ k, m !! k = map.lookupL k ps) (ids : List val)
    (hperm : ids.Perm ((ps.map map.toE).map (·.id))) :
    ∃ keys : List K, ids = keys.map map.keyId ∧
      (∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup := by
  have hids : (ps.map map.toE).map (·.id) = (ps.map Prod.fst).map map.keyId := by
    simp [List.map_map, Function.comp_def, map.toE]
  rw [hids] at hperm
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall map.keyId ids (fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hx)
    exact ⟨k, rfl⟩)
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj map.keyId map.keyId_inj, hperm.mem_iff,
      list_mem_map_inj map.keyId map.keyId_inj, Hagree k]
    have := map.lookupL_eq_none_iff k ps
    cases h : map.lookupL k ps <;> simp_all
  have Hnd' : keys.Nodup :=
    list_nodup_of_map _ _ (hperm.nodup_iff.2 (List.pairwise_map.2 (Hnd.imp fun h e => h (map.keyId_inj e))))
  exact ⟨keys, rfl, Hmem, (GMap.size_eq_length m keys Hnd' Hmem).symm, Hnd'⟩

/-- The general `for range` rule. `keys` lists the keys of `m`, the map when the loop starts, in
iteration order; `P keys i m'` is the loop invariant before the `i`-th key, when the map is `m'`.
The body gets the map's points-to and may change the map (with `dq = 1`). At the `i`-th key
`key`, if `key` is in the current map `m'` the body is called with its current value; if it is
not (deleted since the loop started), it is skipped. Keys added during the loop are not
visited. A `break`/`return` of the body must establish `Φ` itself (the body holds the map). -/
theorem wp_map_for_range_gen (P : List K → Nat → GMap K V → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (dq : DFrac)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 m ∗
       □ (∀ (i : Nat) (key : K) (v : V) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m' !! key = some v⌝ -∗
          P keys i m' -∗ mref ↦${dq} m' -∗
          WP (App (App (Val #body) (Val #key)) (Val #v)) @ s; E
            {{ bv, forMapPostcondition
                iprop(∃ m'' : GMap K V, mref ↦${dq} m'' ∗ P keys (i + 1) m'') Φ bv }}) ∗
       □ (∀ (i : Nat) (key : K) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m' !! key = none⌝ -∗ P keys i m' -∗ P keys (i + 1) m') ∗
       (∀ m' : GMap K V, P keys keys.length m' -∗ mref ↦${dq} m' -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false Hnn]
  wp_pures
  wp_bind (App (Val Read) (Val #mref))
  iapply wp_ownMap_read $$ Hm
  iintro %ps %Hps Hm
  obtain ⟨Hnd0, Hagree⟩ := Hps
  wp_pures
  wp_bind (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) _)
  iapply wp_InternalMapForRange
  iintro %e' %He'
  rw [go.internal_map_for_range_step] at He'
  obtain ⟨ids, hperm, rfl⟩ := He'
  obtain ⟨keys, rfl, Hmem, Hsize, Hnd⟩ := map.keys_of_ids_perm m ps Hnd0 Hagree ids hperm
  icases HΦ $$ %keys %(⟨Hmem, Hsize, Hnd⟩) with ⟨HP, #Hiter, #Hskip, HΦ⟩
  ihave Hinv : iprop(∃ m' : GMap K V, mref ↦${dq} m' ∗ P keys 0 m') $$ [Hm HP]
  · iexists m
    iframe HP Hm
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map map.keyId keys = List.map map.keyId (keys.drop i) by rw [hi, List.drop_zero],
    show P keys 0 = P keys i by rw [hi]]
  clear hi
  iloeb as IH generalizing %i %hile
  by_cases hlt : i < keys.length
  · have hkey : keys[i]? = some keys[i] := List.getElem?_eq_getElem hlt
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldr_cons]
    icases Hinv with ⟨%m', Hm', HP⟩
    wp_auto
    wp_bind (App (Val Read) (Val #mref))
    iapply wp_ownMap_read $$ Hm'
    iintro %ps' %Hps' Hm'
    obtain ⟨-, Hagree'⟩ := Hps'
    wp_pures
    rw [show PairV #(keys[i]) (ArrayV (List.replicate 0 (LitV LitUnit))) = map.keyId keys[i]
      from rfl, map.lookupIdVal_keyId, ← Hagree' keys[i]]
    cases hk : m' !! keys[i] with
    | none =>
      simp only
      wp_auto
      rw [executeVal_unseal]; simp only [executeValDef]
      wp_auto
      ihave HP := Hskip $$ %i %(keys[i]) %m' %(⟨hkey, hk⟩) HP
      iapply IH $$ %(i + 1) %(by omega) HΦ [Hm' HP]
      iexists m'
      iframe Hm' HP
    | some v =>
      simp only
      wp_pures
      ihave Hb := Hiter $$ %i %(keys[i]) %v %m' %(⟨hkey, hk⟩) HP Hm'
      wp_bind (App (App (Val #body) (Val #(keys[i]))) (Val #v))
      iapply wp_wand $$ Hb
      iintro %bv Hpost
      unfold forMapPostcondition
      icases Hpost with (⟨%hbv, Hinv⟩ | ⟨%hbv, Hinv⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩)
      · subst hbv
        rw [continueVal_unseal]; simp only [continueValDef]
        wp_auto
        iapply IH $$ %(i + 1) %(by omega) HΦ Hinv
      · subst hbv
        rw [executeVal_unseal]; simp only [executeValDef]
        wp_auto
        iapply IH $$ %(i + 1) %(by omega) HΦ Hinv
      · subst hbv
        rw [breakVal_unseal]; simp only [breakValDef]
        wp_auto
        iexact HΦ'
      · subst hbv
        rw [returnVal_unseal]; simp only [returnValDef]
        wp_auto
        iexact HΦ'
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    icases Hinv with ⟨%m', Hm', HP⟩
    have hi : i = keys.length := by omega
    subst hi
    iapply HΦ $$ HP Hm'
/-- Weakening `forMapPostcondition`; the `∧` lets both sides share resources. -/
theorem forMapPostcondition_mono (P Q : IProp GF) (Φ Ψ : val → IProp GF) (bv : val) :
    ((P -∗ Q) ∧ (∀ v, Φ v -∗ Ψ v)) -∗ forMapPostcondition P Φ bv -∗
      forMapPostcondition Q Ψ bv := by
  iintro Hw H
  unfold forMapPostcondition
  icases H with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ⟩ | ⟨%v', %hbv, HΦ⟩)
  · ileft; iframe %hbv; icases Hw with ⟨HPQ, -⟩; iapply HPQ $$ HP
  · iright; ileft; iframe %hbv; icases Hw with ⟨HPQ, -⟩; iapply HPQ $$ HP
  · iright; iright; ileft; iframe %hbv; icases Hw with ⟨-, HΦΨ⟩; iapply HΦΨ $$ HΦ
  · iright; iright; iright; iexists v'; iframe %hbv; icases Hw with ⟨-, HΦΨ⟩; iapply HΦΨ $$ HΦ

/-- `for range` over a map the loop only reads (`mref ↦${dq} m`, any fraction): the body is
called on each key of `m` once, in the order of `keys`, with its value. -/
theorem wp_map_for_range (P : List K → Int → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (dq : DFrac)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 ∗
       □ (∀ (i : Int) (key : K) (v : V), ⌜keys[i.toNat]? = some key ∧ m !! key = some v⌝ -∗
          P keys i -∗
          WP (App (App (Val #body) (Val #key)) (Val #v)) @ s; E
            {{ v, forMapPostcondition (P keys (i + 1)) (fun v => iprop(mref ↦${dq} m -∗ Φ v)) v }}) ∗
       (P keys (GMap.size m) -∗ mref ↦${dq} m -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  iapply wp_map_for_range_gen (fun keys (i : Nat) m' => iprop(⌜m' = m⌝ ∗ P keys (i : Int)))
    body key_type elem_type mref m dq Φ $$ Hm
  iintro %keys %Hkeys
  icases HΦ $$ %keys %Hkeys with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
  isplitl [HP]
  · isplitr
    · ipureintro; rfl
    · iexact HP
  isplitr
  · imodintro
    iintro %i %key %v %m' %Hiv ⟨%hm, HP⟩ Hm
    subst hm
    obtain ⟨hk, hv⟩ := Hiv
    iapply wp_wand $$ (Hiter $$ %(i : Int) %key %v %(⟨by simpa using hk, hv⟩) HP)
    iintro %bv Hpost
    iapply forMapPostcondition_mono $$ [Hm] Hpost
    isplit
    · iintro HP
      iexists m'
      iframe Hm
      isplitr
      · ipureintro; rfl
      · have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by push_cast; rfl
        rw [hcast]
        iexact HP
    · iintro %v' HΦ'
      iapply HΦ' $$ Hm
  isplitr
  · imodintro
    iintro %i %key %m' %Hin ⟨%hm, HP⟩
    subst hm
    obtain ⟨hk, hnone⟩ := Hin
    exfalso
    have := (Hmem key).1 (List.mem_of_getElem? hk)
    rw [hnone] at this
    exact Bool.false_ne_true this
  · iintro %m' ⟨%hm, HP⟩ Hm
    subst hm
    rw [Hsize]
    iapply HΦ $$ HP Hm

/-- `for k, v := range m { body }` where the body owns the map (full ownership, `mref ↦$`)
and changes at most the current key: called on the `i`-th key `key` of the domain `keys`
(the map's keys at the start, each once) with the value `v` it had at the start, when the
map is `m'` (equal to `m` on the keys not yet visited), it returns the map as `m''`, equal
to `m'` except at `key`. `P keys i m'` is the loop invariant (it may mention the order of
the keys, as `wp_map_for_range`'s does). A `break`/`return` of the body must establish `Φ`
itself (the body holds the map). For a body that changes other keys, see
`wp_map_for_range_gen`. -/
theorem wp_map_for_range_mut_keys (P : List K → Nat → GMap K V → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦$ m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 m ∗
       □ (∀ (i : Nat) (key : K) (v : V) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m !! key = some v ∧
            ∀ (j : Nat) (k : K), i ≤ j → keys[j]? = some k → m' !! k = m !! k⌝ -∗
          P keys i m' -∗ mref ↦$ m' -∗
          WP (App (App (Val #body) (Val #key)) (Val #v))
            {{ bv, forMapPostcondition
                iprop(∃ m'' : GMap K V, mref ↦$ m'' ∗ P keys (i + 1) m'' ∗
                  ⌜∀ k, k ≠ key → m'' !! k = m' !! k⌝) Φ bv }}) ∗
       (∀ m' : GMap K V, P keys keys.length m' -∗ mref ↦$ m' -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) {{ Φ }} := by
  iintro Hm HΦ
  iapply wp_map_for_range_gen (fun keys i m' => iprop(P keys i m' ∗
      ⌜∀ (j : Nat) (k : K), i ≤ j → keys[j]? = some k → m' !! k = m !! k⌝))
    body key_type elem_type mref m (DFrac.own 1) Φ $$ Hm
  iintro %keys %Hkeys
  icases HΦ $$ %keys %Hkeys with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
  isplitl [HP]
  · iframe HP
    ipureintro
    intro j k _ _
    rfl
  isplitr
  · imodintro
    iintro %i %key %v %m' %Hiv ⟨HP, %Hagree⟩ Hm
    obtain ⟨hk, hv⟩ := Hiv
    have hvm : m !! key = some v := (Hagree i key (Nat.le_refl _) hk).symm.trans hv
    iapply wp_wand $$ (Hiter $$ %i %key %v %m' %(⟨hk, hvm, Hagree⟩) HP Hm)
    iintro %bv Hpost
    iapply forMapPostcondition_mono $$ [] Hpost
    isplit
    · iintro ⟨%m'', Hm, HP, %Hchg⟩
      iexists m''
      iframe Hm HP
      ipureintro
      intro j k hj hkj
      have hne : k ≠ key := by
        rintro rfl
        have := list_nodup_getElem?_inj keys Hnd i j k hk hkj
        omega
      rw [Hchg k hne]
      exact Hagree j k (by omega) hkj
    · iintro %v' HΦ'
      iexact HΦ'
  isplitr
  · imodintro
    iintro %i %key %m' %Hin ⟨HP, %Hagree⟩
    obtain ⟨hk, hnone⟩ := Hin
    exfalso
    have := (Hmem key).1 (List.mem_of_getElem? hk)
    rw [← Hagree i key (Nat.le_refl _) hk, hnone] at this
    exact Bool.false_ne_true this
  · iintro %m' ⟨HP, _⟩ Hm
    iapply HΦ $$ HP Hm

/-- `wp_map_for_range_mut_keys` with an invariant that does not mention the keys. -/
theorem wp_map_for_range_mut (P : Nat → GMap K V → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦$ m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P 0 m ∗
       □ (∀ (i : Nat) (key : K) (v : V) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m !! key = some v ∧
            ∀ (j : Nat) (k : K), i ≤ j → keys[j]? = some k → m' !! k = m !! k⌝ -∗
          P i m' -∗ mref ↦$ m' -∗
          WP (App (App (Val #body) (Val #key)) (Val #v))
            {{ bv, forMapPostcondition
                iprop(∃ m'' : GMap K V, mref ↦$ m'' ∗ P (i + 1) m'' ∗
                  ⌜∀ k, k ≠ key → m'' !! k = m' !! k⌝) Φ bv }}) ∗
       (∀ m' : GMap K V, P keys.length m' -∗ mref ↦$ m' -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) {{ Φ }} := by
  iintro Hm H
  iapply wp_map_for_range_mut_keys (fun _ i m' => P i m') body key_type elem_type mref m Φ
    $$ Hm H


/-- `len(m)` of a map the caller owns, and the model's bound on its size (fewer
than `2^63` keys: `internal_map_length_step`). `t` is any type whose
underlying type is a map (`len_map` takes `[t ↓u go.MapType ..]`). The nil map
is `pure_wp_map_nil_len`. -/
theorem wp_map_len_lt {t key_type elem_type : go.GoType} [t ↓u go.MapType key_type elem_type]
    (mref : Loc) (m : GMap K V) (dq : DFrac) :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #mref)) @ s; E
    {{ RET #(W64 (GMap.size m)); mref ↦${dq} m ∗ ⌜GMap.size m < 2 ^ 63⌝ }} := by
  wp_start as Hm
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  rw [decide_eq_false Hnn]
  wp_pures
  wp_bind (App (Val Read) (Val #mref))
  iapply wp_ownMap_read $$ Hm
  iintro %ps %Hps Hm
  obtain ⟨Hnd, Hagree⟩ := Hps
  obtain ⟨keys, hkeys, -, Hsize, -⟩ :=
    map.keys_of_ids_perm m ps Hnd Hagree _ (List.Perm.refl _)
  have Hlen : (ps.map map.toE).length = GMap.size m := by
    rw [← Hsize]; simpa using congrArg List.length hkeys
  wp_pures
  rw [Hlen]
  by_cases hb : GMap.size m < 2 ^ 63
  · rw [if_pos hb]
    wp_pures
    iapply HΦ
    isplitl
    · iexact Hm
    · ipureintro; exact hb
  · rw [if_neg hb]
    iapply wp_assume
    iintro %h
    cases h

/-- `len(m)` of a map the caller owns (see `wp_map_len_lt`, which also gives the
model's bound on the map's size). -/
theorem wp_map_len {t key_type elem_type : go.GoType} [t ↓u go.MapType key_type elem_type]
    (mref : Loc) (m : GMap K V) (dq : DFrac) :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #mref)) @ s; E
    {{ RET #(W64 (GMap.size m)); mref ↦${dq} m }} := by
  iintro %Φ Hm HΦ
  iapply wp_map_len_lt $$ Hm
  inext
  iintro ⟨Hm, -⟩
  iapply HΦ $$ Hm


instance wp_map_nil_for_range (body : GoFunc) (key_type elem_type : go.GoType) :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (App (Val (map.forRange key_type elem_type)) (Val #map.nil)) (Val #body))
      (Val executeVal) :=
  pure_wp_val True _ executeVal fun s E Φ _ => by
    iintro HΦ
    wp_call_lc Hlc
    iapply HΦ $$ Hlc

/-- `len` of a nil map is `0`; see `go.len_map`. The non-nil case needs the
map's ownership (for the `Read`) and is not a `PureWp`; it is `wp_map_len`. -/
instance pure_wp_map_nil_len {t key_type elem_type : go.GoType}
    [t ↓u go.MapType key_type elem_type] :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (Val #(functions go.len [t])) (Val #map.nil)) (Val #(W64 0)) :=
  pure_wp_val True _ #(W64 0) fun s E Φ _ => by
    rw [func_unfold]
    iintro HΦ
    wp_auto_lc 1
    iapply HΦ $$ Hlc1

end forRange

end Perennial
