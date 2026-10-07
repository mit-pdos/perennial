/-
Port of `new/golang/theory/map.v`: the map points-to `mref ↦${dq} m`
(`ownMap`) and specs for the map operations (insert, delete, lookup, make,
clear, `for range`).

Differences from Rocq:
* stdpp's `gmap K V` (with `EqDecision K` and `Countable K`) is
  `Perennial.gmap K V`, which only needs `DecidableEq K`.
* In `wp_map_for_range`, Rocq's `listToSet keys = dom m` is stated as
  `∀ k, k ∈ keys ↔ (m !! k).isSome`.
* `wp_map_len` and `pure_wp_map_nil_len` are stated at any type whose
  underlying type is a map (see `len_map` in `Perennial/Golang/Defn/Map.lean`);
  Rocq states them at the literal `go.MapType key_type elem_type`.
-/
import Perennial.Golang.Theory.TacticsSimp
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Theory.Array
import Perennial.Golang.Defn.Map
import Perennial.GooseLang.IPersist

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

noncomputable section defns
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- `k` is a safe map key at `key_type`: comparing it with itself does not
panic (see the comment in `Perennial/Golang/Defn/Map.lean`). -/
class SafeMapKey {K : Type} (key_type : go.GoType) (k : K) : Prop where
  wp_go_eq_safe_map_key : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF),
    (∀ v, Φ v) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #k))) @ s; E {{ Φ }}

export SafeMapKey (wp_go_eq_safe_map_key)

instance safe_map_key_is_go_eq {K : Type} (key_type : go.GoType) (k : K) (b : Bool)
    [h : ⟦GoOp GoEquals key_type, (#k, #k)⟧ ⤳ #b] : SafeMapKey (GF := GF) key_type k where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

-- TODO: reading from nil map. Want to say that an owned map is not nil, which
-- requires knowing that wp_ref gives non-null pointers.

variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- The map points-to. -/
def ownMapDef (mptr : Loc) (dq : DFrac) (m : GMap K V) : IProp GF :=
  iprop(∃ (mv : val) (mp : val → Bool × val),
    "Hown" ∷ heapPointsto mptr dq mv ∗
    "%His_map" ∷ ⌜is_map_pure mv mp⌝ ∗
    "%Hagree" ∷ ⌜∀ k : K, mp #k = (match m !! k with
                                   | none => (false, #(zero_val V))
                                   | some v => (true, #v))⌝ ∗
    "%Hdom" ∷ ⌜∀ kv, (mp kv).1 = true → ∃ k : K, kv = #k⌝ ∗
    "%Hdefault" ∷ ⌜mapDefault mv = #(zero_val V)⌝)

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

instance ownMap_timeless (mptr : Loc) (dq : DFrac) (m : GMap K V) :
    Timeless (ownMap (GF := GF) mptr dq m) := by
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]; infer_instance

theorem wp_mapInsert (key_type : go.GoType) (l : Loc) (m : GMap K V) (k : K) (v : V)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (App (Val (map.insert key_type)) (Val #l)) (Val #k)) (Val #v)) @ s; E
    {{ RET #(); l ↦$ (<[k := v]> m) }} := by
  rw [ownMap_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  wp_call
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  wp_apply _internal_wp_untyped_store $$ Hown with Hown
  iapply HΦ
  unfold ownMapDef
  simp only [named]
  iexists (mapInsert mv #k #v), (fun k' => if k' = #k then (true, #v) else mp k')
  iframe Hown
  ipureintro
  refine ⟨go.is_map_pure_map_insert _ _ _ _ His_map, ?_, ?_, ?_⟩
  · intro k'
    by_cases h : k' = k
    · subst h; simp
    · have h' : (#k' : val) ≠ #k := fun e => h (go.intoVal_inj e)
      simp only [h', ite_false, GMap.lookup_insert_ne _ _ (Ne.symm h)]
      exact Hagree k'
  · intro kv
    by_cases h : kv = #k
    · intro _; exact ⟨k, h⟩
    · simp only [h, ite_false]; exact Hdom kv
  · rw [go.mapDefault_map_insert]; exact Hdefault

theorem wp_mapDelete (l : Loc) (m : GMap K V) (k : K) (key_type elem_type : go.GoType)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [go.MapType key_type elem_type])) (Val #l)) (Val #k)) @ s; E
    {{ RET #(); l ↦$ (GMap.delete k m) }} := by
  wp_start as Hm
  rw [ownMap_unseal]
  iNamed Hm
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  wp_apply _internal_wp_untyped_store $$ Hown with Hown
  iapply HΦ
  unfold ownMapDef
  simp only [named]
  iexists (mapDelete mv #k), (fun k' => if k' = #k then (false, mapDefault mv) else mp k')
  iframe Hown
  ipureintro
  refine ⟨go.is_map_pure_map_delete _ _ _ His_map, ?_, ?_, ?_⟩
  · intro k'
    by_cases h : k' = k
    · subst h; simp [Hdefault]
    · have h' : (#k' : val) ≠ #k := fun e => h (go.intoVal_inj e)
      simp only [h', ite_false, GMap.lookup_delete_ne _ (Ne.symm h)]
      exact Hagree k'
  · intro kv
    by_cases h : kv = #k
    · simp [h]
    · simp only [h, ite_false]; exact Hdom kv
  · rw [go.mapDefault_map_delete]; exact Hdefault

theorem wp_map_lookup2 (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V) (k : K)
    (dq : DFrac) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (App (Val (map.lookup2 key_type elem_type)) (Val #mref)) (Val #k)) @ s; E
    {{ RET (PairV #((m !! k).getD (zero_val V)) #(decide ((m !! k).isSome))); mref ↦${dq} m }} := by
  rw [ownMap_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  ihave %Hnn := heapPointsto_non_null _ _ _ $$ Hown
  wp_call
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  rw [decide_eq_false (show ¬ mref = map.nil from Hnn)]
  wp_pures
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  rw [go.mapLookup_pure #k mv mp His_map, Hagree k]
  cases hk : m !! k <;>
  · simp only [Option.getD_none, Option.getD_some, Option.isSome_none, Option.isSome_some,
      decide_true, decide_false, Bool.false_eq_true]
    wp_pures
    iapply HΦ
    unfold ownMapDef
    simp only [named]
    iexists mv
    iexists mp
    iframe Hown
    ipureintro
    exact ⟨His_map, Hagree, Hdom, Hdefault⟩

instance pure_wp_map_nil_lookup2 (key_type elem_type : go.GoType) (k : K)
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type]
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (App (Val (map.lookup2 key_type elem_type)) (Val #map.nil)) (Val #k))
      (Val (PairV #(zero_val V) #false)) :=
  pure_wp_val True _ (PairV #(zero_val V) #false) fun s E Φ _ => by
    iintro HΦ
    wp_call_lc Hlc
    wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
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
  wp_apply wp_alloc_untyped with %l Hl
  iapply HΦ
  rw [ownMap_unseal]; unfold ownMapDef; simp only [named]
  iexists _
  iexists (fun _ => (false, #(zero_val V)))
  iframe Hl
  ipureintro
  refine ⟨go.is_map_pure_map_empty _, ?_, ?_, go.mapDefault_map_empty _⟩
  · intro k; rfl
  · intro kv h; simp at h

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
  icases Hm' with ⟨%mv', %mp', Hown', %His_map', %Hagree', %Hdom', %Hdefault'⟩
  wp_apply _internal_wp_untyped_read $$ Hown' with Hown'
  wp_apply _internal_wp_untyped_store $$ Hown with Hown
  iapply HΦ
  simp only [named]
  iexists mv'
  iexists mp'
  iframe Hown
  ipureintro
  exact ⟨His_map', Hagree', Hdom', Hdefault'⟩

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
  iexists mv
  iexists mp
  iframe Hown
  ipureintro
  exact ⟨His_map, Hagree, Hdom, Hdefault⟩

instance ownMap_update_into_persistently (mref : Loc) (dq : DFrac) (m : GMap K V) :
    UpdateIntoPersistently (ownMap (GF := GF) mref dq m) (ownMap mref DFrac.discard m) where
  update_into_persistently := by
    iintro H
    imod ownMap_persist mref dq m $$ H with #H
    imodintro
    iexact H

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

section forRange
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_InternalMapForRange (mv : val) (m : val → Bool × val) (body : val)
    (key_type elem_type : go.GoType) (Φ : val → IProp GF) :
    (⌜is_map_pure mv m⌝ : IProp GF) -∗
    (∀ e', ⌜is_go_step_pure (InternalMapForRange key_type elem_type) (PairV mv body) e'⌝ -∗
      WP e' @ s; E {{ Φ }}) -∗
    WP (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) (Val (PairV mv body)))
      @ s; E {{ Φ }} := by
  iintro %Hm HΦ
  have hstep := go.internal_map_domain_literal_step_pure mv m body key_type elem_type Hm
  iapply wp_GoInstruction' (s := s) (E := E) (InternalMapForRange key_type elem_type) (PairV mv body) Φ
    (fun gs => by
      obtain ⟨ks, hks⟩ := go.is_map_domain_exists mv m Hm
      have h : ∃ e, is_go_step_pure (InternalMapForRange key_type elem_type) (PairV mv body) e := by
        rw [hstep]; exact ⟨_, ks, hks, rfl⟩
      obtain ⟨e, he⟩ := h
      exact ⟨e, gs, he, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure (InternalMapForRange key_type elem_type) (PairV mv body) e' := Hp
  imodintro
  iframe Hctx
  iapply HΦ $$ %e' %Hp'

variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- The postcondition of a `for range` loop body over a map. FIXME: seal. -/
def forMapPostcondition (P : IProp GF) (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continueVal⌝ ∗ P) ∨
    (⌜bv = executeVal⌝ ∗ P) ∨
    (⌜bv = breakVal⌝ ∗ Φ executeVal) ∨
    (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv))

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
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false Hnn]
  wp_pures
  rw [ownMap_unseal]
  iNamed Hm
  -- the map, re-sealed, once `FinishRead` has given the points-to back
  have hseal : (heapPointsto mref dq mv : IProp GF) ⊢ ownMapDef mref dq m := by
    iintro Hown
    unfold ownMapDef
    simp only [named]
    iexists mv, mp
    iframe Hown
    ipureintro
    exact ⟨His_map, Hagree, Hdom, Hdefault⟩
  wp_apply wp_start_read $$ Hown with ⟨Hown, Hclose⟩
  wp_bind (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) _)
  iapply wp_InternalMapForRange mv mp #body key_type elem_type _ $$ %His_map
  iintro %e' %He'
  rw [go.internal_map_domain_literal_step_pure mv mp #body key_type elem_type His_map] at He'
  obtain ⟨ks, hks, rfl⟩ := He'
  obtain ⟨Hnodup, Hks⟩ := go.is_map_domain_pure mv mp ks His_map hks
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall (intoVal (V := K)) ks
    (fun kv hkv => Hdom kv ((Hks kv).2 hkv))
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj (intoVal (V := K)) go.intoVal_inj, ← Hks, Hagree k]
    cases m !! k <;> simp
  have Hnd : keys.Nodup := list_nodup_of_map _ _ Hnodup
  have Hsize : keys.length = GMap.size m := (GMap.size_eq_length m keys Hnd Hmem).symm
  icases HΦ $$ %keys %(⟨Hmem, Hsize, Hnd⟩) with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map intoVal keys = List.map intoVal (keys.drop i) by rw [hi, List.drop_zero],
    show P keys 0 = P keys (i : Int) by rw [hi]; rfl]
  clear hi
  iloeb as IH generalizing %i %hile
  by_cases hlt : i < keys.length
  · have hkey : keys[i]? = some keys[i] := List.getElem?_eq_getElem hlt
    obtain ⟨v, hv⟩ : ∃ v, m !! keys[i] = some v :=
      Option.isSome_iff_exists.1 ((Hmem _).1 (List.getElem_mem hlt))
    rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.foldr_cons]
    simp only [Hagree keys[i], hv]
    ihave Hb := Hiter $$ %(i : Int) %(keys[i]) %v %(⟨by simpa using hkey, hv⟩) HP
    wp_bind (App (App (Val #body) (Val #(keys[i]))) (Val #v))
    iapply wp_wand $$ Hb
    iintro %bv Hpost
    unfold forMapPostcondition
    have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by push_cast; rfl
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩)
    · subst hbv
      rw [continueVal_unseal]; simp only [continueValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [executeVal_unseal]; simp only [executeValDef]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [breakVal_unseal]; simp only [breakValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with Hown
      · iframe Hown Hclose
      iapply HΦ'
      iapply hseal $$ Hown
    · subst hbv
      rw [returnVal_unseal]; simp only [returnValDef]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with Hown
      · iframe Hown Hclose
      iapply HΦ'
      iapply hseal $$ Hown
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    wp_apply wp_finish_read $$ [Hown Hclose] with Hown
    · iframe Hown Hclose
    have hsz : (i : Int) = (GMap.size m : Int) := by omega
    rw [hsz]
    iapply HΦ $$ HP
    iapply hseal $$ Hown


/-- `len(m)` of a map the caller owns. `t` is any type whose underlying type is
a map (`len_map` takes `[t ↓u go.MapType ..]`; Rocq states this at the literal
`go.MapType key_type elem_type`). The nil map is `pure_wp_map_nil_len`. -/
theorem wp_map_len {t key_type elem_type : go.GoType} [t ↓u go.MapType key_type elem_type]
    (mref : Loc) (m : GMap K V) (dq : DFrac) :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #mref)) @ s; E
    {{ RET #(W64 (GMap.size m)); mref ↦${dq} m }} := by
  wp_start as Hm
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  rw [decide_eq_false Hnn]
  wp_pures
  rw [ownMap_unseal]
  iNamed Hm
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  obtain ⟨ks, hks⟩ := go.is_map_domain_exists mv mp His_map
  obtain ⟨Hnodup, Hks⟩ := go.is_map_domain_pure mv mp ks His_map hks
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall (intoVal (V := K)) ks
    (fun kv hkv => Hdom kv ((Hks kv).2 hkv))
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj (intoVal (V := K)) go.intoVal_inj, ← Hks, Hagree k]
    cases m !! k <;> simp
  have Hnd : keys.Nodup := list_nodup_of_map _ _ Hnodup
  have Hsize : keys.length = GMap.size m := (GMap.size_eq_length m keys Hnd Hmem).symm
  haveI := go.internal_map_length_step_pure mv _ hks
  wp_pures
  rw [List.length_map, Hsize]
  iapply HΦ
  unfold ownMapDef
  simp only [named]
  iexists mv, mp
  iframe Hown
  ipureintro
  exact ⟨His_map, Hagree, Hdom, Hdefault⟩


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
