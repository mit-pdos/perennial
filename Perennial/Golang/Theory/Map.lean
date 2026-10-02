/-
Port of `new/golang/theory/map.v`: the map points-to `mref ↦${dq} m`
(`own_map`) and specs for the map operations (insert, delete, lookup, make,
clear, `for range`).

Differences from Rocq:
* stdpp's `gmap K V` (with `EqDecision K` and `Countable K`) is
  `Perennial.gmap K V`, which only needs `DecidableEq K`.
* In `wp_map_for_range`, Rocq's `list_to_set keys = dom m` is stated as
  `∀ k, k ∈ keys ↔ (m !! k).isSome`.
-/
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Theory.Array
import Perennial.Golang.Defn.Map
import Perennial.GooseLang.IPersist

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

noncomputable section defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- `k` is a safe map key at `key_type`: comparing it with itself does not
panic (see the comment in `Perennial/Golang/Defn/Map.lean`). -/
class SafeMapKey {K : Type} (key_type : go.type) (k : K) : Prop where
  wp_go_eq_safe_map_key : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF),
    (∀ v, Φ v) ⊢
      WP (App (Val (GoInstruction (GoOp GoEquals key_type))) (Val (PairV #k #k))) @ s; E {{ Φ }}

export SafeMapKey (wp_go_eq_safe_map_key)

instance safe_map_key_is_go_eq {K : Type} (key_type : go.type) (k : K) (b : Bool)
    [h : ⟦GoOp GoEquals key_type, (#k, #k)⟧ ⤳ #b] : SafeMapKey (GF := GF) key_type k where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

-- TODO: reading from nil map. Want to say that an owned map is not nil, which
-- requires knowing that wp_ref gives non-null pointers.

variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- The map points-to. -/
def own_map_def (mptr : loc) (dq : DFrac) (m : gmap K V) : IProp GF :=
  iprop(∃ (mv : val) (mp : val → Bool × val),
    "Hown" ∷ heap_pointsto mptr dq mv ∗
    "%His_map" ∷ ⌜is_map_pure mv mp⌝ ∗
    "%Hagree" ∷ ⌜∀ k : K, mp #k = (match m !! k with
                                   | none => (false, #(zero_val V))
                                   | some v => (true, #v))⌝ ∗
    "%Hdom" ∷ ⌜∀ kv, (mp kv).1 = true → ∃ k : K, kv = #k⌝ ∗
    "%Hdefault" ∷ ⌜map_default mv = #(zero_val V)⌝)

@[irreducible] def own_map (mptr : loc) (dq : DFrac) (m : gmap K V) : IProp GF :=
  own_map_def mptr dq m

theorem own_map_unseal : @own_map = @own_map_def := by
  funext; with_unfolding_all rfl

end defns

/-- `mref ↦${dq} m`: the map at `mref` has contents `m`. -/
scoped notation:50 mref:50 " ↦${" dq "} " m:50 => own_map mref dq m
/-- `mref ↦$ m`: the map points-to with full ownership. -/
scoped notation:50 mref:50 " ↦$ " m:50 => own_map mref (DFrac.own 1) m
/-- `mref ↦$□ m`: persistent map points-to. -/
scoped notation:50 mref:50 " ↦$□ " m:50 => own_map mref DFrac.discard m

section lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

instance own_map_timeless (mptr : loc) (dq : DFrac) (m : gmap K V) :
    Timeless (own_map (GF := GF) mptr dq m) := by
  rw [own_map_unseal]; unfold own_map_def; simp only [named]; infer_instance

theorem wp_map_insert (key_type : go.type) (l : loc) (m : gmap K V) (k : K) (v : V)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (App (Val (map.insert key_type)) (Val #l)) (Val #k)) (Val #v)) @ s; E
    {{ RET #(); l ↦$ (<[k := v]> m) }} := by
  rw [own_map_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  wp_call
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  wp_apply _internal_wp_untyped_store $$ Hown with Hown
  iapply HΦ
  unfold own_map_def
  simp only [named]
  iexists (map_insert mv #k #v), (fun k' => if k' = #k then (true, #v) else mp k')
  iframe Hown
  ipureintro
  refine ⟨go.is_map_pure_map_insert _ _ _ _ His_map, ?_, ?_, ?_⟩
  · intro k'
    by_cases h : k' = k
    · subst h; simp
    · have h' : (#k' : val) ≠ #k := fun e => h (go.into_val_inj e)
      simp only [h', ite_false, gmap.lookup_insert_ne _ _ (Ne.symm h)]
      exact Hagree k'
  · intro kv
    by_cases h : kv = #k
    · intro _; exact ⟨k, h⟩
    · simp only [h, ite_false]; exact Hdom kv
  · rw [go.map_default_map_insert]; exact Hdefault

theorem wp_map_delete (l : loc) (m : gmap K V) (k : K) (key_type elem_type : go.type)
    [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [go.MapType key_type elem_type])) (Val #l)) (Val #k)) @ s; E
    {{ RET #(); l ↦$ (gmap.delete k m) }} := by
  wp_start as Hm
  rw [own_map_unseal]
  iNamed Hm
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  wp_apply _internal_wp_untyped_store $$ Hown with Hown
  iapply HΦ
  unfold own_map_def
  simp only [named]
  iexists (map_delete mv #k), (fun k' => if k' = #k then (false, map_default mv) else mp k')
  iframe Hown
  ipureintro
  refine ⟨go.is_map_pure_map_delete _ _ _ His_map, ?_, ?_, ?_⟩
  · intro k'
    by_cases h : k' = k
    · subst h; simp [Hdefault]
    · have h' : (#k' : val) ≠ #k := fun e => h (go.into_val_inj e)
      simp only [h', ite_false, gmap.lookup_delete_ne _ (Ne.symm h)]
      exact Hagree k'
  · intro kv
    by_cases h : kv = #k
    · simp [h]
    · simp only [h, ite_false]; exact Hdom kv
  · rw [go.map_default_map_delete]; exact Hdefault

theorem wp_map_lookup2 (key_type elem_type : go.type) (mref : loc) (m : gmap K V) (k : K)
    (dq : DFrac) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (App (Val (map.lookup2 key_type elem_type)) (Val #mref)) (Val #k)) @ s; E
    {{ RET (PairV #((m !! k).getD (zero_val V)) #(decide ((m !! k).isSome))); mref ↦${dq} m }} := by
  rw [own_map_unseal]
  iintro %Φ Hm HΦ
  iNamed Hm
  ihave %Hnn := heap_pointsto_non_null _ _ _ $$ Hown
  wp_call
  wp_apply (wp_go_eq_safe_map_key (GF := GF) (key_type := key_type) (k := k)) with %_
  rw [decide_eq_false (show ¬ mref = map.nil from Hnn)]
  wp_pures
  wp_apply _internal_wp_untyped_read $$ Hown with Hown
  rw [go.map_lookup_pure #k mv mp His_map, Hagree k]
  cases hk : m !! k <;>
  · simp only [Option.getD_none, Option.getD_some, Option.isSome_none, Option.isSome_some,
      decide_true, decide_false, Bool.false_eq_true]
    wp_pures
    iapply HΦ
    unfold own_map_def
    simp only [named]
    iexists mv
    iexists mp
    iframe Hown
    ipureintro
    exact ⟨His_map, Hagree, Hdom, Hdefault⟩

instance pure_wp_map_nil_lookup2 (key_type elem_type : go.type) (k : K)
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

theorem wp_map_lookup1 (key_type elem_type : go.type) (mref : loc) (m : gmap K V) (k : K)
    (dq : DFrac) [Hsafe : SafeMapKey (GF := GF) key_type k] :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (App (Val (map.lookup1 key_type elem_type)) (Val #mref)) (Val #k)) @ s; E
    {{ RET #((m !! k).getD (zero_val V)); mref ↦${dq} m }} := by
  iintro %Φ Hm HΦ
  wp_call
  wp_apply wp_map_lookup2 key_type elem_type mref m k dq $$ Hm with Hm
  iapply HΦ $$ Hm

instance pure_wp_map_nil_lookup1 (key_type elem_type : go.type) (k : K)
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

theorem wp_map_make2 (len : w64) (key_type elem_type : go.type)
    [TypeRepr key_type K] -- to automatically fill in `K`
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.MapType key_type elem_type])) (Val #len)) @ s; E
    {{ (mref : loc), RET #mref; mref ↦$ (∅ : gmap K V) }} := by
  wp_start
  wp_apply wp_alloc_untyped with %l Hl
  iapply HΦ
  rw [own_map_unseal]; unfold own_map_def; simp only [named]
  iexists _
  iexists (fun _ => (false, #(zero_val V)))
  iframe Hl
  ipureintro
  refine ⟨go.is_map_pure_map_empty _, ?_, ?_, go.map_default_map_empty _⟩
  · intro k; rfl
  · intro kv h; simp at h

theorem wp_map_make1 (key_type elem_type : go.type) [TypeRepr key_type K]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [go.MapType key_type elem_type])) (Val #())) @ s; E
    {{ (mref : loc), RET #mref; mref ↦$ (∅ : gmap K V) }} := by
  wp_start
  wp_apply (wp_map_make2 (K := K) (V := V) (W64 0) key_type elem_type) with %mref Hm
  iapply HΦ $$ Hm

theorem wp_map_clear (mref : loc) (m : gmap K V) (key_type elem_type : go.type)
    [TypeRepr key_type K] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V elem_type] :
    {{ (mref ↦$ m : IProp GF) }}
      (App (Val #(functions go.clear [go.MapType key_type elem_type])) (Val #mref)) @ s; E
    {{ RET #(); mref ↦$ (∅ : gmap K V) }} := by
  wp_start as Hm
  wp_apply (wp_map_make1 (K := K) (V := V) key_type elem_type) with %m' Hm'
  rw [own_map_unseal]
  unfold own_map_def
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

theorem own_map_not_nil (mref : loc) (m : gmap K V) (dq : DFrac) :
    (mref ↦${dq} m : IProp GF) ⊢ ⌜mref ≠ map.nil⌝ := by
  rw [own_map_unseal]
  iintro Hm
  iNamed Hm
  ihave %H := heap_pointsto_non_null _ _ _ $$ Hown
  ipureintro; exact H

instance own_map_discarded_persist (mref : loc) (m : gmap K V) :
    Persistent (own_map (GF := GF) mref DFrac.discard m) := by
  rw [own_map_unseal]; unfold own_map_def; simp only [named]; infer_instance

theorem own_map_persist (mref : loc) (dq : DFrac) (m : gmap K V) :
    (mref ↦${dq} m : IProp GF) ⊢ |==> mref ↦$□ m := by
  rw [own_map_unseal]
  iintro Hm
  iNamed Hm
  imod heap_pointsto_persist _ _ _ $$ Hown with Hown
  imodintro
  unfold own_map_def
  simp only [named]
  iexists mv
  iexists mp
  iframe Hown
  ipureintro
  exact ⟨His_map, Hagree, Hdom, Hdefault⟩

instance own_map_update_into_persistently (mref : loc) (dq : DFrac) (m : gmap K V) :
    UpdateIntoPersistently (own_map (GF := GF) mref dq m) (own_map mref DFrac.discard m) where
  update_into_persistently := by
    iintro H
    imod own_map_persist mref dq m $$ H with #H
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

section for_range
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_InternalMapForRange (mv : val) (m : val → Bool × val) (body : val)
    (key_type elem_type : go.type) (Φ : val → IProp GF) :
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
def for_map_postcondition (P : IProp GF) (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continue_val⌝ ∗ P) ∨
    (⌜bv = execute_val⌝ ∗ P) ∨
    (⌜bv = break_val⌝ ∗ Φ execute_val) ∨
    (∃ v, ⌜bv = return_val v⌝ ∗ Φ bv))

theorem wp_map_for_range (P : List K → Int → IProp GF) (body : func.t)
    (key_type elem_type : go.type) (mref : loc) (m : gmap K V) (dq : DFrac)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦${dq} m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = gmap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 ∗
       □ (∀ (i : Int) (key : K) (v : V), ⌜keys[i.toNat]? = some key ∧ m !! key = some v⌝ -∗
          P keys i -∗
          WP (App (App (Val #body) (Val #key)) (Val #v)) @ s; E
            {{ v, for_map_postcondition (P keys (i + 1)) Φ v }}) ∗
       (P keys (gmap.size m) -∗ Φ execute_val))) -∗
    WP (App (App (Val (map.for_range key_type elem_type)) (Val #mref)) (Val #body)) @ s; E {{ Φ }} := by
  iintro Hm HΦ
  ihave %Hnn := own_map_not_nil _ _ _ $$ Hm
  wp_call
  rw [decide_eq_false Hnn]
  wp_pures
  rw [own_map_unseal]
  iNamed Hm
  wp_apply wp_start_read $$ Hown with ⟨Hown, Hclose⟩
  wp_bind (App (Val (GoInstruction (InternalMapForRange key_type elem_type))) _)
  iapply wp_InternalMapForRange mv mp #body key_type elem_type _ $$ %His_map
  iintro %e' %He'
  rw [go.internal_map_domain_literal_step_pure mv mp #body key_type elem_type His_map] at He'
  obtain ⟨ks, hks, rfl⟩ := He'
  obtain ⟨Hnodup, Hks⟩ := go.is_map_domain_pure mv mp ks His_map hks
  obtain ⟨keys, rfl⟩ := list_exists_map_of_forall (into_val (V := K)) ks
    (fun kv hkv => Hdom kv ((Hks kv).2 hkv))
  have Hmem : ∀ k, k ∈ keys ↔ (m !! k).isSome := by
    intro k
    rw [← list_mem_map_inj (into_val (V := K)) go.into_val_inj, ← Hks, Hagree k]
    cases m !! k <;> simp
  have Hnd : keys.Nodup := list_nodup_of_map _ _ Hnodup
  have Hsize : keys.length = gmap.size m := (gmap.size_eq_length m keys Hnd Hmem).symm
  icases HΦ $$ %keys %(⟨Hmem, Hsize, Hnd⟩) with ⟨HP, #Hiter, HΦ⟩
  obtain ⟨i, hi⟩ : ∃ i : Nat, i = 0 := ⟨0, rfl⟩
  have hile : i ≤ keys.length := by omega
  rw [show List.map into_val keys = List.map into_val (keys.drop i) by rw [hi, List.drop_zero],
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
    unfold for_map_postcondition
    have hcast : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by push_cast; rfl
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩)
    · subst hbv
      rw [continue_val_unseal]; simp only [continue_val_def]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [execute_val_unseal]; simp only [execute_val_def]
      wp_auto
      rw [← hcast]
      iapply IH $$ %(i + 1) %(by omega) Hown Hclose HP HΦ
    · subst hbv
      rw [break_val_unseal]; simp only [break_val_def]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with _
      · iframe Hown Hclose
      iexact HΦ'
    · subst hbv
      rw [return_val_unseal]; simp only [return_val_def]
      wp_auto
      wp_apply wp_finish_read $$ [Hown Hclose] with _
      · iframe Hown Hclose
      iexact HΦ'
  · rw [List.drop_of_length_le (by omega)]
    simp only [List.map_nil, List.foldr_nil]
    wp_auto
    wp_apply wp_finish_read $$ [Hown Hclose] with _
    · iframe Hown Hclose
    have hsz : (i : Int) = (gmap.size m : Int) := by omega
    rw [hsz]
    iapply HΦ $$ HP


instance wp_map_nil_for_range (body : func.t) (key_type elem_type : go.type) :
    PureWp (G := hG.goose_globalGS) (L := hG.goose_localGS) True
      (App (App (Val (map.for_range key_type elem_type)) (Val #map.nil)) (Val #body))
      (Val execute_val) :=
  pure_wp_val True _ execute_val fun s E Φ _ => by
    iintro HΦ
    wp_call_lc Hlc
    iapply HΦ $$ Hlc

end for_range

end Perennial
