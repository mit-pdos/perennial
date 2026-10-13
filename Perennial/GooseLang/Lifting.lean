/-
Program-logic base for GooseLang, without crash machinery.

Notes:
* No crash logic: the program logic is iris-lean's `wp` (with its own later
  credits).
* iris-lean's `IrisGS_gen` class is instantiated (`goose_irisGS`) from
  `gooseGlobalGS` and `gooseLocalGS`. `heapGS` bundles the
  two. `heapGS` does *not* contain the `GoGlobalContext` (the language instance
  itself depends on it, so it must be a separate instance argument). It does
  contain the one `allG GF` (`gooseAllG`), the ghost state of the thread tokens
  and of every proof under `heapGS`, which therefore does not assume its own
  `[allG GF]`.
* `numLatersPerStep` is `0`. Every step still yields one
  later credit (`£ 1`).
* The language instance is the bounded layer of `BoundedLang.lean`, whose
  state is `BcfgState = CfgState × Fuel` (the fuel `⟨s, t⟩`: step fuel and
  thread fuel); the state interpretation (`gooseBstateInterp`) adds to
  `gooseStateInterp` the authoritative counter of time receipts for the step
  fuel (`receiptFuel s`, i.e. `receiptAuth (N - (s + 1))` for the bound
  `N = receiptBound GF` of the receipt ghost state, `Receipts.lean`) and the
  thread tokens of the thread fuel (`threadFuel t = threadToks t`,
  `Threads.lean`). The lifting lemmas `goose_wp_lift_*` restate iris-lean's for
  the real `base_step` and `gooseStateInterp` (as `gooseCfgInterp`), for the
  plain redexes; Go instructions, the only counted steps, have their own lemma
  `wp_GoInstruction_receipt`, which handles the stutter by Löb induction and
  hands out a time receipt; `Fork` (`wp_fork_tok`, likewise by Löb induction)
  hands out a thread token and `ThreadExit` (`wp_ThreadExit`) takes one back.
* The state interpretation consists of a local part (`naHeapCtx`,
  `ffiLocalCtx`, `ownGoStateCtx`, `goLctx` equality) plus the global part
  (`ffiGlobalCtx`, iris-lean's prophecy map `prophMapInterp`).
* `Alloc` allocates a single cell, so `wp_allocN_seq` gives `pointstoVals l
  (.own 1) [v]`.
-/
module

public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Lifting
public import Perennial.ProgramLogic.EctxLifting
public import Iris.BI.Lib.ProphMap
public import Iris.Instances.Lib.GhostVar
public import Iris.Std.GenSets
public import Perennial.Algebra.NaHeap
public import Perennial.GooseLang.Lang
public import Perennial.GooseLang.BoundedLang
public import Perennial.GooseLang.Receipts
public import Perennial.GooseLang.Threads

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## `gset` as an iris-lean `LawfulSet` (used by the prophecy map)

This is a local instance whose set operations are given inline, so that it does
not export global `Singleton`/`Inter`/`SDiff` instances on `gset`. Membership,
union and the empty set agree definitionally with the `gmap` ones. -/

namespace GSet

variable {K : Type} [DecidableEq K]

theorem mem_iff_lookup {X : GSet K} {k : K} : k ∈ X ↔ X !! k = some () := by
  show (X.lookup k).isSome ↔ _
  cases X.lookup k <;> simp

@[reducible] def lawfulSet : LawfulSet (GSet K) K where
  mem X k := (X.lookup k).isSome
  singleton k := {[k := ()]}
  union X Y := X ∪ Y
  inter X Y := GMap.filter (fun k _ => decide ((Y.lookup k).isSome)) X
  sdiff X Y := GMap.filter (fun k _ => decide ¬ ((Y.lookup k).isSome)) X
  emptyCollection := ∅
  ext {X Y} h := by
    apply GMap.ext; intro k
    have h' : (X.lookup k).isSome ↔ (Y.lookup k).isSome := h k
    cases hX : X.lookup k <;> cases hY : Y.lookup k <;> simp_all
  mem_empty {x} := by
    show ¬ ((∅ : GSet K).lookup x).isSome
    simp
  mem_singleton {x y} := by
    show ((({[y := ()]} : GSet K)).lookup x).isSome ↔ _
    rw [show ({[y := ()]} : GSet K).lookup x = _ from GMap.lookup_singleton_iff y x ()]
    by_cases h : y = x
    · simp [h]
    · simp [h]; exact Ne.symm h
  mem_union {X Y x} := by
    show ((X ∪ Y).lookup x).isSome ↔ (X.lookup x).isSome ∨ (Y.lookup x).isSome
    rw [show (X ∪ Y).lookup x = _ from GMap.lookup_union X Y x]
    cases X.lookup x <;> cases Y.lookup x <;> simp
  mem_inter {X Y x} := by
    show ((GMap.filter _ X).lookup x).isSome ↔ (X.lookup x).isSome ∧ (Y.lookup x).isSome
    rw [show (GMap.filter _ X).lookup x = _ from GMap.lookup_filter _ X x]
    cases X.lookup x <;> simp [Option.filter]
  mem_diff {X Y x} := by
    show ((GMap.filter _ X).lookup x).isSome ↔ (X.lookup x).isSome ∧ ¬ (Y.lookup x).isSome
    rw [show (GMap.filter _ X).lookup x = _ from GMap.lookup_filter _ X x]
    cases X.lookup x <;> simp [Option.filter]

end GSet

attribute [local instance] GSet.lawfulSet

/-! ## The heap points-to -/

section definitions
variable [ext : FfiSyntax] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- A location in an allocated block (`locCar ≠ 0`, so non-null, and so is every location
of its block) with a non-atomic points-to. -/
def heapPointsto (l : Loc) (dq : DFrac) (v : val) : IProp GF :=
  iprop(⌜l.locCar ≠ 0⌝ ∗ naHeapPointsto l dq v)

end definitions

/- `l ↦{dq} v`, `l ↦ v` and `l ↦□ v` for `heapPointsto`, scoped to `goose_heap`. -/
namespace goose_heap
scoped notation:50 l:50 " ↦{" dq "} " v:50 => heapPointsto l dq v
scoped notation:50 l:50 " ↦ " v:50 => heapPointsto l (DFrac.own 1) v
scoped notation:50 l:50 " ↦□ " v:50 => heapPointsto l DFrac.discard v
end goose_heap

open goose_heap

section heapPointsto
variable [ext : FfiSyntax] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]
open ProofMode

instance heapPointsto_persistent (l : Loc) (v : val) :
    Persistent (heapPointsto (hG := hG) l .discard v) := by
  unfold heapPointsto; infer_instance

instance heapPointsto_timeless (l : Loc) (dq : DFrac) (v : val) :
    Timeless (heapPointsto (hG := hG) l dq v) := by
  unfold heapPointsto; infer_instance

theorem heapPointsto_persist (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ |==> heapPointsto l .discard v := by
  unfold heapPointsto
  iintro ⟨%Ha, Hb⟩
  imod naHeapPointsto_persist l dq v $$ Hb with Hb
  imodintro
  iframe Hb
  ipureintro; exact Ha

instance heapPointsto_dfractional (l : Loc) (v : val) :
    DFractional (fun dq => heapPointsto (hG := hG) l dq v) where
  dfractional dp dq := by
    unfold heapPointsto
    refine ⟨?_, ?_⟩
    · iintro ⟨%Hl, H⟩
      icases (dfractional (Φ := fun dq => naHeapPointsto (hG := hG) l dq v) dp dq).1 $$ H
        with ⟨H1, H2⟩
      isplitl [H1]
      · iframe H1; ipureintro; exact Hl
      · iframe H2; ipureintro; exact Hl
    · iintro ⟨⟨%Hl, H1⟩, ⟨_, H2⟩⟩
      iframe %Hl
      iapply (dfractional (Φ := fun dq => naHeapPointsto (hG := hG) l dq v) dp dq).2
      iframe
  dfractional_persistent := heapPointsto_persistent l v
  dfractional_persist dq := heapPointsto_persist l dq v

instance heapPointsto_as_dfractional (l : Loc) (dq : DFrac) (v : val) :
    AsDFractional (heapPointsto (hG := hG) l dq v) (fun dq => heapPointsto l dq v) dq :=
  ⟨.rfl, heapPointsto_dfractional l v⟩

instance heapPointsto_fractional (l : Loc) (v : val) :
    Fractional (fun q => heapPointsto (hG := hG) l (.own q) v) :=
  fractional_of_dfractional (fun dq => heapPointsto l dq v)

instance heapPointsto_as_fractional (l : Loc) (q : Qp) (v : val) :
    AsFractional (heapPointsto (hG := hG) l (.own q) v) ioΦ
      (fun q => heapPointsto l (.own q) v) ioq q :=
  ⟨.rfl, heapPointsto_fractional l v⟩

instance heapPointsto_combine_sep_gives (l : Loc) (dq1 dq2 : DFrac) (v1 v2 : val) :
    CombineSepGives (heapPointsto (hG := hG) l dq1 v1) (heapPointsto l dq2 v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    unfold heapPointsto
    iintro ⟨⟨_, H1⟩, ⟨_, H2⟩⟩
    icombine H1 H2 gives %H
    imodintro; ipureintro; exact H

theorem heapPointsto_agree (l : Loc) (dq1 dq2 : DFrac) (v1 v2 : val) :
    heapPointsto (hG := hG) l dq1 v1 ∗ heapPointsto l dq2 v2 ⊢ ⌜v1 = v2⌝ := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨_, H⟩
  ipureintro; exact H

theorem na_pointsto_to_heap (l : Loc) (dq : DFrac) (v : val) (H : l.locCar ≠ 0) :
    naHeapPointsto (hG := hG) l dq v ⊢ heapPointsto l dq v := by
  unfold heapPointsto
  iintro Hl
  iframe Hl
  ipureintro; exact H

theorem heapPointsto_na_acc (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢
      naHeapPointsto l dq v ∗ (∀ v', naHeapPointsto l dq v' -∗ heapPointsto l dq v') := by
  unfold heapPointsto
  iintro ⟨%Hl, H⟩
  iframe H
  iintro %v' H'
  iframe H'
  ipureintro; exact Hl

theorem heapPointsto_valid (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜✓ dq⌝ := by
  unfold heapPointsto
  iintro ⟨_, H⟩
  iapply naHeapPointsto_valid $$ H

theorem heapPointsto_frac_valid (l : Loc) (q : Qp) (v : val) :
    heapPointsto (hG := hG) l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  heapPointsto_valid l (.own q) v

theorem heapPointsto_car (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜l.locCar ≠ 0⌝ := by
  unfold heapPointsto
  iintro ⟨%Hl, _⟩
  ipureintro; exact Hl

theorem heapPointsto_non_null (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜l ≠ null⌝ := by
  unfold heapPointsto
  iintro ⟨%Hl, _⟩
  ipureintro
  intro h; subst h; exact Hl rfl

end heapPointsto

/-! ## Package-initialization state -/

section go_state_definitions

class GoStateGS (GF : BundledGFunctors) where
  package_inited_inG : GhostVarG GF (GMap GoString Bool)
  packageInitedName : GName

class GoStatePreG (GF : BundledGFunctors) where
  package_inited_preG_inG : GhostVarG GF (GMap GoString Bool)

attribute [reducible, instance] GoStateGS.package_inited_inG GoStatePreG.package_inited_preG_inG

abbrev goStateGSUpdatePre (GF : BundledGFunctors) (hT : GoStatePreG GF) (γ : GName) :
    GoStateGS GF :=
  ⟨hT.package_inited_preG_inG, γ⟩

abbrev goStateGSUpdate (GF : BundledGFunctors) (hT : GoStateGS GF) (γ : GName) :
    GoStateGS GF :=
  ⟨hT.package_inited_inG, γ⟩

variable {GF : BundledGFunctors}

def ownGoStateCtx [hG : GoStateGS GF] (package_inited : GMap GoString Bool) : IProp GF :=
  ghost_var hG.packageInitedName (.own (1 : Qp).half) package_inited

def ownGoState [hG : GoStateGS GF] (package_inited : GMap GoString Bool) : IProp GF :=
  ghost_var hG.packageInitedName (.own (1 : Qp).half) package_inited

instance ownGoStateCtx_combine_sep_gives [GoStateGS GF] (v1 v2 : GMap GoString Bool) :
    ProofMode.CombineSepGives (ownGoStateCtx (GF := GF) v1) (ownGoState v2)
      iprop(⌜v1 = v2⌝) where
  combine_sep_gives := by
    unfold ownGoStateCtx ownGoState
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨_, H⟩
    imodintro; ipureintro; exact H

instance ownGoState_timeless [GoStateGS GF] (v : GMap GoString Bool) :
    Timeless (ownGoState (GF := GF) v) := by
  unfold ownGoState; infer_instance

theorem ownGoState_update [GoStateGS GF] (v v' v'' : GMap GoString Bool) :
    ⊢@{IProp GF} ownGoState v -∗ ownGoStateCtx v' ==∗
      ownGoState v'' ∗ ownGoStateCtx v'' := by
  unfold ownGoState ownGoStateCtx
  iintro H1 H2
  iapply ghost_var_update_halves $$ H1 H2

theorem goState_init (hT : GoStatePreG GF) (package_inited : GMap GoString Bool) :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      ownGoStateCtx (hG := goStateGSUpdatePre GF hT γ) package_inited ∗
      ownGoState (hG := goStateGSUpdatePre GF hT γ) package_inited := by
  unfold ownGoState ownGoStateCtx
  imod ghost_var_alloc package_inited with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (ghost_var_split γ package_inited (1 : Qp).half (1 : Qp).half)
  rw [Qp.half_add_half]
  iexact H

end go_state_definitions

/-! ## FFI interpretation and GooseLang ghost state -/

/-- An FFI layer's ghost state: `ffiLocalGS`/`ffiGlobalGS` bundle the CMRAs and
ghost names it uses, and `ffiLocalCtx`/`ffiGlobalCtx` interpret its states.
(The start resources `ffiGlobalStart`/`ffiLocalStart` are in
`FfiInterpAdequacy`; there is no crash machinery.) -/
class FfiInterp (ffi : FfiModel) where
  ffiLocalGS : BundledGFunctors → Type
  ffiGlobalGS : BundledGFunctors → Type
  ffiGlobalCtx : ∀ {GF : BundledGFunctors}, ffiGlobalGS GF → ffi_global_state → IProp GF
  ffiLocalCtx : ∀ {GF : BundledGFunctors}, ffiLocalGS GF → ffi_state → IProp GF

export FfiInterp (ffiLocalGS ffiGlobalGS ffiGlobalCtx ffiLocalCtx)

section goose_lang
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]

/-- Global ghost state for GooseLang. -/
class GooseGlobalGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  /-- not an instance on purpose, to avoid diamonds with `IrisGS_gen` -/
  gooseInvGS : InvGS_gen hlc GF
  /-- The one `allG GF`: the ghost state of the thread tokens (`goose_threadGS`)
  and of every proof under `HeapGS`, which therefore does not assume its own
  `[AllG GF]` (`Ghost/All.lean`) -/
  gooseAllG : AllG GF
  goose_prophGS : prophMapGS proph_id val GF (GMap proph_id)
  gooseFfiGlobalGS : @ffiGlobalGS ffi _ GF
  /-- Time receipts, tied to the step fuel of the bounded semantics;
  carries the time-receipt bound `receiptBound GF` -/
  goose_receiptGS : ReceiptGS GF
  /-- Thread tokens, tied to the thread fuel of the bounded semantics;
  carries the thread bound `threadBound GF` -/
  goose_threadGS : ThreadGS GF

/-- Per-generation ("local") ghost state. -/
class GooseLocalGS (GF : BundledGFunctors) where
  gooseFfiLocalGS : @ffiLocalGS ffi _ GF
  goose_go_local_context : GoLocalContext
  goose_na_heapGS : NaHeapGS Loc val GF
  goose_go_stateGS : GoStateGS GF

attribute [reducible, instance] GooseGlobalGS.gooseAllG GooseGlobalGS.goose_prophGS
  GooseGlobalGS.goose_receiptGS GooseGlobalGS.goose_threadGS
  GooseLocalGS.goose_go_local_context
  GooseLocalGS.goose_na_heapGS GooseLocalGS.goose_go_stateGS

/-- Bundles the global and local ghost state (not including `GoGlobalContext`). -/
class HeapGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  goose_globalGS : GooseGlobalGS hlc GF
  goose_localGS : GooseLocalGS GF

attribute [reducible, instance] HeapGS.goose_globalGS HeapGS.goose_localGS

export GooseGlobalGS (gooseInvGS gooseFfiGlobalGS)
export GooseLocalGS (gooseFfiLocalGS goose_go_local_context)

/-- The lock state of a `naMode`. -/
def tls : NaMode → LockState
  | Writing => WSt
  | Reading n => RSt n

@[simp] theorem tls_Writing : tls Writing = WSt := rfl
@[simp] theorem tls_Reading (n : Nat) : tls (Reading n) = RSt n := rfl

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The GooseLang state interpretation: the per-generation part together with
the global part (FFI global state and prophecy map). -/
def gooseStateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : CfgState) (κs : List Observation) : IProp GF :=
  iprop(naHeapCtx tls σ.1.heap ∗
    ffiLocalCtx L.gooseFfiLocalGS σ.1.world ∗
    ownGoStateCtx σ.1.goState.packageState ∗
    ⌜σ.1.goState.goLctx = L.goose_go_local_context⌝ ∗
    ffiGlobalCtx G.gooseFfiGlobalGS σ.2.globalWorld ∗
    prophMapInterp κs σ.2.usedProphId)

/-- The state interpretation of the bounded language: `gooseStateInterp` of
the real configuration, the authoritative receipt counter for the step fuel and
the thread tokens of the thread fuel. -/
def gooseBstateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : BcfgState) (κs : List Observation) : IProp GF :=
  iprop(gooseStateInterp σ.1 κs ∗ receiptFuel σ.2.steps ∗ threadFuel σ.2.threads)

instance goose_stateInterp [GooseGlobalGS hlc GF] [GooseLocalGS GF] :
    StateInterp BcfgState Observation GF where
  stateInterp σ _ κs _ := gooseBstateInterp σ κs

variable [FfiSemantics ext ffi] [GoGlobalContext]

instance goose_irisGS [G : GooseGlobalGS hlc GF] [GooseLocalGS GF] : IrisGS_gen hlc Expr GF where
  invGS := G.gooseInvGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := G.gooseInvGS
    iintro $

end goose_lang

/-! ## Atomicity -/

/-! ## `heap_array` -/

section heap_array
variable {V : Type}

theorem heapArray_lookup_lt (l : Loc) (vs : List V) (i : Int) (h : i < 0) :
    heapArray l vs !! (l +ₗ i) = none := by
  induction vs generalizing l i with
  | nil => rfl
  | cons v vs ih =>
    show (<[l := v]> (heapArray (l +ₗ 1) vs)) !! (l +ₗ i) = none
    rw [GMap.lookup_insert_ne _ _ (fun e => by have := loc_add_eq_inv l i e.symm; omega)]
    have := ih (l +ₗ 1) (i - 1) (by omega)
    rwa [loc_add_assoc, show 1 + (i - 1) = i by omega] at this

end heap_array

theorem naModeRl_is_read_lock : IsReadLock tls naModeRl := by
  intro lk n h; cases lk <;> simp_all [tls, naModeRl]

theorem naModeUrl_is_read_unlock : IsReadUnlock tls naModeUrl := by
  intro lk n h; cases lk <;> simp_all [tls, naModeUrl]

section na_heap_alloc
variable [ext : FfiSyntax] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

theorem na_heap_alloc_list (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs : List val)
    (Hfresh : ∀ i : Int, σ !! (l +ₗ i) = none) :
    ⊢@{IProp GF} naHeapCtx tls σ ==∗ naHeapCtx tls (heapArray l (vs.map Free) ∪ σ) ∗
      [∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l with
  | nil =>
    iintro H
    imodintro
    have : heapArray l (([] : List val).map Free) ∪ σ = σ := by
      apply GMap.ext; intro k; rfl
    rw [this]
    iframe H
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons v vs ih =>
    iintro H
    imod ih (l +ₗ 1) (fun i => by rw [loc_add_assoc]; exact Hfresh _) $$ H with ⟨H, Hpts⟩
    have Hnone : (heapArray (l +ₗ 1) (vs.map Free) ∪ σ) !! l = none := by
      refine (GMap.lookup_union_None _ _ _).mpr ⟨?_, ?_⟩
      · have := heapArray_lookup_lt (l +ₗ 1) (vs.map Free) (-1) (by omega)
        rwa [loc_add_assoc, show (1 : Int) + -1 = 0 by omega, loc_add_0] at this
      · have := Hfresh 0; rwa [loc_add_0] at this
    imod na_heap_alloc tls _ l v (Reading 0) Hnone rfl $$ H with ⟨H, Hl⟩
    imodintro
    have Heq : heapArray l ((v :: vs).map Free) ∪ σ =
        <[l := (Reading 0, v)]> (heapArray (l +ₗ 1) (vs.map Free) ∪ σ) :=
      (GMap.insert_union_l _ _ _ _).symm
    rw [Heq]
    iframe H
    iapply BigSepL.bigSepL_cons.2
    have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    simp only [Int.natCast_zero, loc_add_0, Hk]
    iframe

/-- The cells `l, l +ₗ 1, …` of a list of points-tos are in the heap, readable. -/
theorem na_heap_read_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (dq : DFrac) (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) dq v) -∗
      ⌜∀ i (h : i < vs.length), ∃ k, σ !! (l +ₗ (i : Int)) = some (Reading k, vs[i])⌝ := by
  induction vs generalizing l with
  | nil => iintro _ _; ipureintro; intro i h; simp at h
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    rw [Int.natCast_zero, loc_add_0]
    icases na_heap_read tls σ l dq v $$ Hσ H0 with %⟨lk, n, H1, H2⟩
    have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    simp only [Hk]
    icases ih (l +ₗ 1) $$ Hσ Hl with %Hrest
    ipureintro
    intro i h
    cases i with
    | zero =>
      cases lk with
      | Reading k => exact ⟨k, by simpa using H1⟩
      | Writing => simp at H2
    | succ i =>
      obtain ⟨k, hk⟩ := Hrest i (by simp at h; omega)
      exact ⟨k, by rw [Hk]; simpa using hk⟩

/-- With full ownership, the cells are readable by no one else (`Reading 0`). -/
theorem na_heap_read_cells_1 (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v) -∗
      ⌜∀ i (h : i < vs.length), σ !! (l +ₗ (i : Int)) = some (Reading 0, vs[i])⌝ := by
  induction vs generalizing l with
  | nil => iintro _ _; ipureintro; intro i h; simp at h
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    rw [Int.natCast_zero, loc_add_0]
    icases na_heap_read_1 tls σ l v $$ Hσ H0 with %⟨lk, H1, H2⟩
    have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    simp only [Hk]
    icases ih (l +ₗ 1) $$ Hσ Hl with %Hrest
    ipureintro
    intro i h
    cases i with
    | zero =>
      cases lk with
      | Reading k => simp at H2; subst H2; simpa using H1
      | Writing => simp at H2
    | succ i =>
      have hk := Hrest i (by simp at h; omega)
      rw [Hk]; simpa using hk

/-- Writing all the cells `l, l +ₗ 1, …` (each readable by no one, `Reading 0`). -/
theorem na_heap_write_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs vs' : List val)
    (hlen : vs'.length = vs.length)
    (Hfree : ∀ i (h : i < vs.length), σ !! (l +ₗ (i : Int)) = some (Reading 0, vs[i])) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v) ==∗
      naHeapCtx tls (heapArray l (vs'.map Free) ∪ σ) ∗
      [∗list] i ↦ v ∈ vs', naHeapPointsto (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l vs' with
  | nil =>
    cases vs' with
    | cons => simp at hlen
    | nil =>
      iintro Hσ _
      imodintro
      have : heapArray l (([] : List val).map Free) ∪ σ = σ := by
        apply GMap.ext; intro k; rfl
      rw [this]
      iframe Hσ
      iapply BigSepL.bigSepL_nil.2
      itrivial
  | cons v vs ih =>
    cases vs' with
    | nil => simp at hlen
    | cons v' vs' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have Hk : ∀ k : Nat, l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
      intro k; rw [loc_add_assoc]; congr 1; omega
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [Hk]
    imod ih (l +ₗ 1) vs' hlen (fun i h => by
      have := Hfree (i + 1) (by simp; omega)
      rw [Hk] at this; simpa using this) $$ Hσ Hl with ⟨Hσ, Hl⟩
    have Hl0 : (heapArray (l +ₗ 1) (vs'.map Free) ∪ σ) !! l = some (Reading 0, v) := by
      rw [GMap.lookup_union]
      have := heapArray_lookup_lt (l +ₗ 1) (vs'.map Free) (-1) (by omega)
      rw [loc_add_assoc, show (1 : Int) + -1 = 0 by omega, loc_add_0] at this
      rw [this]
      have := Hfree 0 (by simp)
      simpa using this
    rw [Int.natCast_zero, loc_add_0]
    imod na_heap_write tls _ l (Reading 0) v v' rfl $$ Hσ H0 with ⟨Hσ, H0⟩
    imodintro
    have Heq : heapArray l ((v' :: vs').map Free) ∪ σ =
        <[l := (Reading 0, v')]> (heapArray (l +ₗ 1) (vs'.map Free) ∪ σ) :=
      (GMap.insert_union_l _ _ _ _).symm
    rw [Heq]
    iframe Hσ
    iapply BigSepL.bigSepL_cons.2
    rw [Int.natCast_zero, loc_add_0]
    iframe
    simp only [Hk]
    iexact Hl

end na_heap_alloc

/-! ### Multi-cell memory operations

An encoded value (`Encoding`) occupies the cells `l, l +ₗ 1, …` (`pointstoVals`). The
ghost lemmas below update the lock state of each of a list of cells in one step, as the
steps of `StartReadN`, `PrepareWriteN`, … do. -/

section cells_lemmas
variable [ext : FfiSyntax]

theorem loc_add_succ (l : Loc) (k : Nat) : l +ₗ ((k + 1 : Nat) : Int) = l +ₗ 1 +ₗ (k : Int) := by
  rw [loc_add_assoc]; congr 1; omega

theorem heapArray_union_lookup_self (l : Loc) (cs : List (NonAtomic val))
    (σ : GMap Loc (NonAtomic val)) : (heapArray (l +ₗ 1) cs ∪ σ) !! l = σ !! l := by
  rw [GMap.lookup_union]
  have := heapArray_lookup_lt (l +ₗ 1) cs (-1) (by omega)
  rw [loc_add_assoc, show (1 : Int) + -1 = 0 by omega, loc_add_0] at this
  rw [this]; cases σ !! l <;> rfl

theorem heapArray_cons_union (l : Loc) (c : NonAtomic val) (cs : List (NonAtomic val))
    (σ : GMap Loc (NonAtomic val)) :
    heapArray l (c :: cs) ∪ σ = <[l := c]> (heapArray (l +ₗ 1) cs ∪ σ) :=
  (GMap.insert_union_l _ _ _ _).symm

theorem cellsAt_cons (h : GMap Loc (NonAtomic val)) (l : Loc) (c : NonAtomic val)
    (cs : List (NonAtomic val)) :
    CellsAt h l (c :: cs) ↔ h !! l = some c ∧ CellsAt h (l +ₗ 1) cs := by
  constructor
  · intro H
    have h0 := H 0 (by simp)
    rw [List.getElem_cons_zero] at h0
    refine ⟨by simpa using h0, fun i hi => ?_⟩
    have := H (i + 1) (by simp; omega)
    rw [loc_add_succ] at this; simpa using this
  · rintro ⟨H0, H⟩ i hi
    cases i with
    | zero => simpa using H0
    | succ i => rw [loc_add_succ]; simpa using H i (by simp at hi; omega)

@[simp] theorem cellsAt_nil (h : GMap Loc (NonAtomic val)) (l : Loc) : CellsAt h l [] :=
  fun i hi => by simp at hi

@[simp] theorem heapArray_nil_union (l : Loc) (σ : GMap Loc (NonAtomic val)) :
    heapArray l ([] : List (NonAtomic val)) ∪ σ = σ := by
  apply GMap.ext; intro k; rfl

end cells_lemmas

section na_heap_cells
variable [ext : FfiSyntax] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- Read-lock each cell (the first half of a non-atomic read, `StartReadNS`). -/
theorem na_heap_read_prepare_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (dq : DFrac)
    (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) dq v) ==∗
      ∃ cs : List (NonAtomic val),
        ⌜cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧ ∀ c ∈ cs, ∃ n, c.1 = Reading n⌝ ∗
        naHeapCtx tls (heapArray l (cs.map fun c => (naModeRl c.1, c.2)) ∪ σ) ∗
        [∗list] i ↦ v ∈ vs, naHeapPointstoSt (RSt 1) (l +ₗ (i : Int)) dq v := by
  induction vs generalizing l with
  | nil =>
    iintro Hσ _
    imodintro
    iexists []
    simp only [List.map_nil, heapArray_nil_union]
    iframe Hσ
    isplitr
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    imod ih (l +ₗ 1) $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
    imod na_heap_read_prepare tls naModeRl _ l dq v naModeRl_is_read_lock $$ Hσ H0
      with ⟨%lk, %n, %⟨Hlk, Htls⟩, Hσ, H0⟩
    rw [heapArray_union_lookup_self] at Hlk
    cases lk with
    | Writing => cases Htls
    | Reading k =>
    imodintro
    iexists (Reading k, v) :: cs
    simp only [List.map_cons, heapArray_cons_union]
    iframe Hσ
    isplitr
    · ipureintro
      refine ⟨by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨k, rfl⟩
      · exact Hrd c hc
    iapply BigSepL.bigSepL_cons.2
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    iframe

/-- Read-unlock each cell (the second half of a non-atomic read, `FinishReadNS`). -/
theorem na_heap_read_finish_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (dq : DFrac)
    (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointstoSt (RSt 1) (l +ₗ (i : Int)) dq v) ==∗
      ∃ cs : List (NonAtomic val),
        ⌜cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧ ∀ c ∈ cs, ∃ n, c.1 = Reading (n + 1)⌝ ∗
        naHeapCtx tls (heapArray l (cs.map fun c => (naModeUrl c.1, c.2)) ∪ σ) ∗
        [∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) dq v := by
  induction vs generalizing l with
  | nil =>
    iintro Hσ _
    imodintro
    iexists []
    simp only [List.map_nil, heapArray_nil_union]
    iframe Hσ
    isplitr
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    imod ih (l +ₗ 1) $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
    imod na_heap_read_finish_vs tls naModeUrl l dq v naModeUrl_is_read_unlock $$ H0 %_ Hσ
      with ⟨%lk, %n, %⟨Hlk, Htls⟩, Hσ, H0⟩
    rw [heapArray_union_lookup_self] at Hlk
    cases lk with
    | Writing => cases Htls
    | Reading k =>
    simp only [tls_Reading, LockState.RSt.injEq] at Htls; subst Htls
    imodintro
    iexists (Reading (n + 1), v) :: cs
    simp only [List.map_cons, heapArray_cons_union]
    iframe Hσ
    isplitr
    · ipureintro
      refine ⟨by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨n, rfl⟩
      · exact Hrd c hc
    iapply BigSepL.bigSepL_cons.2
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    iframe

/-- Write-lock each cell (the first half of a non-atomic write, `PrepareWriteNS`). -/
theorem na_heap_write_prepare_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v) ==∗
      ∃ cs : List (NonAtomic val),
        ⌜cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧ ∀ c ∈ cs, c.1 = Reading 0⌝ ∗
        naHeapCtx tls (heapArray l (cs.map fun c => (Writing, c.2)) ∪ σ) ∗
        [∗list] i ↦ v ∈ vs, naHeapPointstoSt WSt (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l with
  | nil =>
    iintro Hσ _
    imodintro
    iexists []
    simp only [List.map_nil, heapArray_nil_union]
    iframe Hσ
    isplitr
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    imod ih (l +ₗ 1) $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
    imod na_heap_write_prepare tls _ l v Writing rfl $$ Hσ H0
      with ⟨%lk, %⟨Hlk, Htls⟩, Hσ, H0⟩
    rw [heapArray_union_lookup_self] at Hlk
    cases lk with
    | Writing => cases Htls
    | Reading k =>
    simp only [tls_Reading, LockState.RSt.injEq] at Htls; subst Htls
    imodintro
    iexists (Reading 0, v) :: cs
    simp only [List.map_cons, heapArray_cons_union]
    iframe Hσ
    isplitr
    · ipureintro
      refine ⟨by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · rfl
      · exact Hrd c hc
    iapply BigSepL.bigSepL_cons.2
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    iframe

/-- Write each write-locked cell (the second half of a non-atomic write,
`FinishStoreNS`). -/
theorem na_heap_write_finish_cells (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs vs' : List val)
    (hlen : vs'.length = vs.length) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointstoSt WSt (l +ₗ (i : Int)) (.own 1) v) ==∗
      ∃ cs : List (NonAtomic val),
        ⌜cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧ ∀ c ∈ cs, c.1 = Writing⌝ ∗
        naHeapCtx tls (heapArray l (vs'.map Free) ∪ σ) ∗
        [∗list] i ↦ v ∈ vs', naHeapPointsto (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l vs' with
  | nil =>
    cases vs' with
    | cons => simp at hlen
    | nil =>
    iintro Hσ _
    imodintro
    iexists []
    simp only [List.map_nil, heapArray_nil_union]
    iframe Hσ
    isplitr
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    cases vs' with
    | nil => simp at hlen
    | cons v' vs' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    imod ih (l +ₗ 1) vs' hlen $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hwr⟩, Hσ, Hl⟩
    imod na_heap_write_finish_vs tls l v v' (Reading 0) rfl $$ H0 %_ Hσ
      with ⟨%lk, %⟨Hlk, Htls⟩, Hσ, H0⟩
    rw [heapArray_union_lookup_self] at Hlk
    cases lk with
    | Reading k => cases Htls
    | Writing =>
    imodintro
    iexists (Writing, v) :: cs
    have Heq : heapArray l ((v' :: vs').map Free) ∪ σ =
        <[l := (Reading 0, v')]> (heapArray (l +ₗ 1) (vs'.map Free) ∪ σ) :=
      heapArray_cons_union _ _ _ _
    rw [Heq]
    iframe Hσ
    isplitr
    · ipureintro
      refine ⟨by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · rfl
      · exact Hwr c hc
    iapply BigSepL.bigSepL_cons.2
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    iframe

/-- The cells are readable (an atomic load, `LoadNS`). -/
theorem na_heap_read_cells' (σ : GMap Loc (NonAtomic val)) (l : Loc) (dq : DFrac)
    (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) dq v) -∗
      ⌜∃ cs : List (NonAtomic val), cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧
        ∀ c ∈ cs, ∃ n, c.1 = Reading n⌝ := by
  induction vs generalizing l with
  | nil => iintro _ _; ipureintro; exact ⟨[], rfl, cellsAt_nil _ _, by simp⟩
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    icases ih (l +ₗ 1) $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
    icases na_heap_read tls σ l dq v $$ Hσ H0 with %⟨lk, n, Hlk, Htls⟩
    ipureintro
    cases lk with
    | Writing => cases Htls
    | Reading k =>
    refine ⟨(Reading k, v) :: cs, by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨k, rfl⟩
    · exact Hrd c hc

/-- With full ownership, the cells are readable by no one else (an atomic write). -/
theorem na_heap_read_cells_1' (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs : List val) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v) -∗
      ⌜∃ cs : List (NonAtomic val), cs.map Prod.snd = vs ∧ CellsAt σ l cs ∧
        ∀ c ∈ cs, c.1 = Reading 0⌝ := by
  induction vs generalizing l with
  | nil => iintro _ _; ipureintro; exact ⟨[], rfl, cellsAt_nil _ _, by simp⟩
  | cons v vs ih =>
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    icases ih (l +ₗ 1) $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
    icases na_heap_read_1 tls σ l v $$ Hσ H0 with %⟨lk, Hlk, Htls⟩
    ipureintro
    cases lk with
    | Writing => cases Htls
    | Reading k =>
    simp only [tls_Reading, LockState.RSt.injEq] at Htls; subst Htls
    refine ⟨(Reading 0, v) :: cs, by simp [Hvs], (cellsAt_cons _ _ _ _).2 ⟨Hlk, Hcells⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · exact Hrd c hc

/-- Write each cell (with no reader) in one step (an atomic write). -/
theorem na_heap_write_cells' (σ : GMap Loc (NonAtomic val)) (l : Loc) (vs vs' : List val)
    (hlen : vs'.length = vs.length) :
    ⊢@{IProp GF} naHeapCtx tls σ -∗
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) (.own 1) v) ==∗
      naHeapCtx tls (heapArray l (vs'.map Free) ∪ σ) ∗
      [∗list] i ↦ v ∈ vs', naHeapPointsto (l +ₗ (i : Int)) (.own 1) v := by
  induction vs generalizing l vs' with
  | nil =>
    cases vs' with
    | cons => simp at hlen
    | nil =>
    iintro Hσ _
    imodintro
    simp only [List.map_nil, heapArray_nil_union]
    iframe Hσ
    iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs ih =>
    cases vs' with
    | nil => simp at hlen
    | cons v' vs' =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    iintro Hσ Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨H0, Hl⟩
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    imod ih (l +ₗ 1) vs' hlen $$ Hσ Hl with ⟨Hσ, Hl⟩
    imod na_heap_write tls _ l (Reading 0) v v' rfl $$ Hσ H0 with ⟨Hσ, H0⟩
    imodintro
    simp only [List.map_cons, heapArray_cons_union, Free]
    iframe Hσ
    iapply BigSepL.bigSepL_cons.2
    simp only [loc_add_succ, Int.natCast_zero, loc_add_0]
    iframe

end na_heap_cells

section atomic
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

open EctxLanguage in
/-- Atomicity from the real base step. Counted redexes (Go instructions) may
stutter in the bounded semantics and are not atomic, hence `hnc`. -/
theorem goose_atomic {e : Expr} (a : Language.Atomicity)
    (h : ∀ σ κ e' σ' efs, BaseStep e σ κ e' σ' efs → (toVal e').isSome)
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome)
    (hnc : redexKind e = .plain := by rfl) :
    Language.Atomic a e :=
  Language.stronglyAtomic_atomic
    (Atomic.ofBaseAtomic _ (fun σ obs e' σ' efs hs => by
        obtain ⟨_, _, hs⟩ := (boundedBaseStep_plain (σ := σ.1) (f := σ.2) hnc).1 hs
        exact h _ obs e' _ efs hs)
      (EctxItemLanguage.subredexes_are_values hsub))

/-- Discharges the `hsub` side condition of `goose_atomic`. -/
local macro "solve_sub_redexes" : tactic =>
  `(tactic| (intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl))

instance alloc_atomic (a : Language.Atomicity) (v : val) : Language.Atomic a (Alloc (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance allocN_atomic (a : Language.Atomicity) (n v : val) :
    Language.Atomic a (AllocN (Val n) (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl) (by solve_sub_redexes)

instance memOp1_atomic (a : Language.Atomicity) (op : MemOp1) (enc : Encoding) (v : val) :
    Language.Atomic a (Primitive1 (.MemOp1Op op enc) (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl) (by solve_sub_redexes)

instance memOp2_atomic (a : Language.Atomicity) (op : MemOp2) (enc : Encoding) (v1 v2 : val) :
    Language.Atomic a (Primitive2 (.MemOp2Op op enc) (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl) (by solve_sub_redexes)

instance checkCell_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (CheckCell (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

/-- `PrepareWrite` and `FinishStore` are individually atomic, but the two need to
be combined to actually write to the heap and that is not atomic. -/
instance prepare_write_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (PrepareWrite (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance load_atomic (a : Language.Atomicity) (v : val) : Language.Atomic a (Load (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance finish_store_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (FinishStore (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance atomic_swap_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (AtomicSwap (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance atomic_op_atomic (a : Language.Atomicity) (v1 v2 : val) :
    Language.Atomic a (AtomicAdd (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance cmpxchg_atomic (a : Language.Atomicity) (v0 v1 v2 : val) :
    Language.Atomic a (CmpXchg (Val v0) (Val v1) (Val v2)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h <;> rfl) (by solve_sub_redexes)

instance start_read_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (StartRead (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance finish_read_atomic (a : Language.Atomicity) (v : val) :
    Language.Atomic a (FinishRead (Val v)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance resolve_atomic (a : Language.Atomicity) (p w : val) :
    Language.Atomic a (ResolveProph (Val p) (Val w)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

end atomic

/-! ## Pure steps

iris-lean provides `PureExec` and `wp_pure_step_later`/`wp_pure_step_fupd`.
`pureExec_of_base_step` builds a one-step `PureExec` from the base step relation. -/

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

open EctxLanguage in
/-- A one-step `PureExec` from the real base step relation (for a plain
redex, which steps in the bounded semantics exactly as in the real one). -/
theorem pureExec_of_base_step {φ : Prop} {e₁ e₂ : Expr}
    (Hsafe : φ → ∀ σ, BaseStep e₁ σ [] e₂ σ [])
    (Hdet : φ → ∀ σ κ e' σ' efs, BaseStep e₁ σ κ e' σ' efs →
      κ = [] ∧ σ' = σ ∧ e' = e₂ ∧ efs = [])
    (hnc : redexKind e₁ = .plain := by rfl) :
    Language.PureExec φ 1 e₁ e₂ where
  pureExec hφ := by
    refine .tail e₁ (.rfl _) (purePrimStep_of_pureBaseStep
      ⟨fun σ => ⟨_, _, _, BoundedBaseStep.step (f := σ.2) hnc (Hsafe hφ σ.1)⟩, ?_⟩)
    intro σ₁ σ₂ obs e₂' eₜ h
    obtain ⟨σ', rfl, h'⟩ := (boundedBaseStep_plain (σ := σ₁.1) (f := σ₁.2) hnc).1 h
    obtain ⟨h1, h2, h3, h4⟩ := Hdet hφ _ _ _ _ _ h'
    subst h2
    exact ⟨h1, rfl, h3.symm, h4⟩

instance pure_recc (f x : Binder) (e : Expr) :
    Language.PureExec True 1 (Rec f x e) (Val (RecV f x e)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.RecS f x e σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_pairc (v1 v2 : val) :
    Language.PureExec True 1 (Pair (Val v1) (Val v2)) (Val (PairV v1 v2)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.PairS v1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_beta (f x : Binder) (e1 : Expr) (v2 : val) :
    Language.PureExec True 1 (App (Val (RecV f x e1)) (Val v2))
      (subst' x v2 (subst' f (RecV f x e1) e1)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.BetaS f x e1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem baseStep_If_inv {v : val} {e1 e2 : Expr} {σ σ' : CfgState} {κ : List Observation}
    {e' : Expr} {efs : List Expr} (h : BaseStep (If (Val v) e1 e2) σ κ e' σ' efs) :
    κ = [] ∧ σ' = σ ∧ efs = [] ∧ ((v = #true ∧ e' = e1) ∨ (v = #false ∧ e' = e2)) := by
  cases h
  · exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, .inr ⟨rfl, rfl⟩⟩

instance pure_if_true (e1 e2 : Expr) : Language.PureExec True 1 (If (Val #true) e1 e2) e1 :=
  pureExec_of_base_step (fun _ σ => BaseStep.IfTrueS e1 e2 σ) fun _ _ _ _ _ _ h => by
    obtain ⟨h1, h2, h3, ⟨_, h4⟩ | ⟨hv, _⟩⟩ := baseStep_If_inv h
    · exact ⟨h1, h2, h4, h3⟩
    · exact absurd (GoGlobalContext.intoVal_inj_bool hv) (by decide)

instance pure_if_false (e1 e2 : Expr) : Language.PureExec True 1 (If (Val #false) e1 e2) e2 :=
  pureExec_of_base_step (fun _ σ => BaseStep.IfFalseS e1 e2 σ) fun _ _ _ _ _ _ h => by
    obtain ⟨h1, h2, h3, ⟨hv, _⟩ | ⟨_, h4⟩⟩ := baseStep_If_inv h
    · exact absurd (GoGlobalContext.intoVal_inj_bool hv) (by decide)
    · exact ⟨h1, h2, h4, h3⟩

instance pure_fst (v1 v2 : val) : Language.PureExec True 1 (Fst (Val (PairV v1 v2))) (Val v1) :=
  pureExec_of_base_step (fun _ σ => BaseStep.FstS v1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_snd (v1 v2 : val) : Language.PureExec True 1 (Snd (Val (PairV v1 v2))) (Val v2) :=
  pureExec_of_base_step (fun _ σ => BaseStep.SndS v1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_literal_value (l : List keyed_element) :
    Language.PureExec True 1 (LiteralValue l) (Val (LiteralValueV l)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.LiteralValueS l σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_select_stmt_clauses (d : Option Expr) (cs : List comm_clause) :
    Language.PureExec True 1 (SelectStmtClauses d cs) (Val (SelectStmtClausesV d cs)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.SelectStmtClausesS d cs σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

end pure

/-! ## Inversion lemmas for `base_step` -/

section inversion
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]
variable {σ σ' : CfgState} {κ : List Observation} {e' : Expr} {efs : List Expr}

theorem baseStep_ArbitraryInt_inv (h : BaseStep ArbitraryInt σ κ e' σ' efs) :
    ∃ x : w64, κ = [] ∧ e' = Val #x ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem baseStep_Fork_inv {e : Expr} (h : BaseStep (Fork e) σ κ e' σ' efs) :
    κ = [] ∧ e' = Val #() ∧ σ' = (σ.1, { σ.2 with threads := σ.2.threads + 1 }) ∧
      efs = [Seq e ThreadExit] := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem baseStep_ThreadExit_inv (h : BaseStep ThreadExit σ κ e' σ' efs) :
    κ = [] ∧ e' = Val #() ∧ σ' = (σ.1, { σ.2 with threads := σ.2.threads - 1 }) ∧ efs = [] := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem baseStep_Alloc_inv {v : val} (h : BaseStep (Alloc (Val v)) σ κ e' σ' efs) :
    ∃ l, IsFresh σ l ∧ κ = [] ∧ e' = Val #l ∧ σ' = (stateInitHeap l v σ.1, σ.2) ∧ efs = [] := by
  cases h; exact ⟨_, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_StartRead_inv {v : val} (h : BaseStep (StartRead (Val v)) σ κ e' σ' efs) :
    ∃ l n w, v = #l ∧ σ.1.heap !! l = some (Reading n, w) ∧ κ = [] ∧ e' = Val w ∧
      σ' = setHeap (<[l := (Reading (n + 1), w)]> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_FinishRead_inv {v : val} (h : BaseStep (FinishRead (Val v)) σ κ e' σ' efs) :
    ∃ l n w, v = #l ∧ σ.1.heap !! l = some (Reading (n + 1), w) ∧ κ = [] ∧ e' = Val #() ∧
      σ' = setHeap (<[l := (Reading n, w)]> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_Load_inv {v : val} (h : BaseStep (Load (Val v)) σ κ e' σ' efs) :
    ∃ l n w, v = #l ∧ σ.1.heap !! l = some (Reading n, w) ∧ κ = [] ∧ e' = Val w ∧
      σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_PrepareWrite_inv {v : val}
    (h : BaseStep (PrepareWrite (Val v)) σ κ e' σ' efs) :
    ∃ l w, v = #l ∧ σ.1.heap !! l = some (Reading 0, w) ∧ κ = [] ∧ e' = Val #() ∧
      σ' = setHeap (<[l := (Writing, w)]> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_FinishStore_inv {v1 v2 : val}
    (h : BaseStep (FinishStore (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l, v1 = #l ∧ IsWriting (σ.1.heap !! l) ∧ κ = [] ∧ e' = Val #() ∧
      σ' = setHeap (<[l := Free v2]> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_AtomicSwap_inv {v1 v2 : val}
    (h : BaseStep (AtomicSwap (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l v0, v1 = #l ∧ σ.1.heap !! l = some (Reading 0, v0) ∧ κ = [] ∧ e' = Val v0 ∧
      σ' = setHeap (<[l := Free v2]> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_AtomicAdd_inv {v1 v2 : val}
    (h : BaseStep (AtomicAdd (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l v0 v', v1 = #l ∧ σ.1.heap !! l = some (Reading 0, v0) ∧ atomicAddEval v0 v2 = some v' ∧
      κ = [] ∧ e' = Val v' ∧ σ' = setHeap (<[l := Free v']> ·) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_CmpXchg_inv {v0 v1 v2 : val}
    (h : BaseStep (CmpXchg (Val v0) (Val v1) (Val v2)) σ κ e' σ' efs) :
    κ = [] ∧ efs = [] ∧
    ((∃ l n vl, v0 = #l ∧ σ.1.heap !! l = some (Reading n, vl) ∧ vl ≠ v1 ∧
        e' = Val (PairV vl #false) ∧ σ' = σ) ∨
     (∃ l vl, v0 = #l ∧ σ.1.heap !! l = some (Reading 0, vl) ∧ vl = v1 ∧
        e' = Val (PairV vl #true) ∧ σ' = setHeap (<[l := Free v2]> ·) σ)) := by
  cases h
  · exact ⟨rfl, rfl, .inl ⟨_, _, _, rfl, ‹_›, ‹_›, rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, .inr ⟨_, _, rfl, ‹_›, ‹_›, rfl, rfl⟩⟩

theorem baseStep_NewProph_inv (h : BaseStep NewProph σ κ e' σ' efs) :
    ∃ p : proph_id, p ∉ σ.2.usedProphId ∧ κ = [] ∧ e' = Val #p ∧
      σ' = (σ.1, { σ.2 with usedProphId := {[p := ()]} ∪ σ.2.usedProphId }) ∧ efs = [] := by
  cases h; exact ⟨_, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_ResolveProph_inv {v w : val}
    (h : BaseStep (ResolveProph (Val v) (Val w)) σ κ e' σ' efs) :
    ∃ p : proph_id, v = #p ∧ κ = [(p, w)] ∧ e' = Val #() ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem baseStep_GoInstruction_inv {op : GoInstruction} {arg : val}
    (h : BaseStep (App (Val (GoInstruction op)) (Val arg)) σ κ e' σ' efs) :
    ∃ s', @IsGoStep _ _ σ.1.goState.goLctx op arg e' σ.1.goState.packageState s' ∧
      κ = [] ∧ efs = [] ∧
      σ' = ({ σ.1 with goState := { σ.1.goState with packageState := s' } }, σ.2) := by
  cases h; exact ⟨_, ‹_›, rfl, rfl, rfl⟩

end inversion

/-! ## Lifting lemmas -/

section lifting
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open EctxLanguage ProofMode

/-- Real base reducibility. -/
def GooseBaseReducible (e : Expr) (σ : CfgState) : Prop :=
  ∃ κ e' σ' efs, BaseStep e σ κ e' σ' efs

/-- `gooseStateInterp` with the (unused) step and thread counts of iris-lean's
`stateInterp`, so that the `goose_wp_lift_*` lemmas have the shape of
iris-lean's lifting lemmas. -/
def gooseCfgInterp (σ : CfgState) (_ns : Nat) (κs : List Observation) (_nt : Nat) : IProp GF :=
  gooseStateInterp σ κs

theorem goose_stateInterp_eq (σ : CfgState) (ns : Nat) (κs : List Observation) (nt : Nat) :
    gooseCfgInterp (GF := GF) σ ns κs nt ⊣⊢
      iprop(naHeapCtx tls σ.1.heap ∗
        ffiLocalCtx L.gooseFfiLocalGS σ.1.world ∗
        ownGoStateCtx σ.1.goState.packageState ∗
        ⌜σ.1.goState.goLctx = L.goose_go_local_context⌝ ∗
        ffiGlobalCtx G.gooseFfiGlobalGS σ.2.globalWorld ∗
        prophMapInterp κs σ.2.usedProphId) := .rfl

theorem goose_bstateInterp_eq (σ : CfgState) (c : Fuel) (ns : Nat) (κs : List Observation)
    (nt : Nat) :
    stateInterp (GF := GF) ((σ, c) : BcfgState) ns κs nt ⊣⊢
      iprop(gooseCfgInterp σ ns κs nt ∗ receiptFuel c.steps ∗ threadFuel c.threads) := .rfl

theorem goose_baseReducible_of {e : Expr} {σ : CfgState} {c : Fuel} (hnc : redexKind e = .plain)
    (h : GooseBaseReducible e σ) : BaseStep.Reducible (e, ((σ, c) : BcfgState)) := by
  obtain ⟨κ, e', σ', efs, h⟩ := h
  exact ⟨κ, e', (σ', c), efs, .step hnc h⟩

/-- iris-lean's `wp_lift_base_step` for a plain redex, in terms of the real
`base_step` and `gooseStateInterp`. -/
theorem goose_wp_lift_base_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={∅,E}=∗
        gooseCfgInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_plain hnc).1 Hstep
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hwp Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step` for a plain redex. -/
theorem goose_wp_lift_atomic_base_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        gooseCfgInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ _v, True }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_plain hnc).1 Hstep
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, HΦ, Hefs⟩
  imodintro
  iframe HΦ Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step_no_fork` for a plain redex. -/
theorem goose_wp_lift_atomic_base_step_no_fork {e₁ : Expr} {Φ : val → IProp GF}
    (h : toVal e₁ = none) (hnc : redexKind e₁ = .plain) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        ⌜eₜ = []⌝ ∗ gooseCfgInterp σ₂ (ns + 1) obs' nt ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_atomic_base_step h hnc
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  imod H $$ %e₂ %σ₂ %eₜ %Hstep Hcred with ⟨%Hefs, Hσ, HΦ⟩
  subst Hefs
  imodintro
  simp only [List.length_nil, Nat.add_zero]
  iframe Hσ HΦ
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- A lifting lemma for atomic steps that only change the heap. -/
theorem wp_lift_atomic_heap_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) :
    (∀ σ₁ : CfgState, naHeapCtx tls σ₁.1.heap ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ κ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ κ e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        ⌜κ = [] ∧ eₜ = []⌝ ∗
        (∃ h', ⌜σ₂ = setHeap (fun _ => h') σ₁⌝ ∗ naHeapCtx tls h') ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_atomic_base_step_no_fork h hnc
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  imod H $$ %σ₁ Hheap with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  imod H $$ %obs %e₂ %σ₂ %eₜ %Hstep Hcred with ⟨%⟨rfl, rfl⟩, ⟨%h', %rfl, Hheap⟩, HΦ⟩
  imodintro
  isplitr
  · ipureintro; rfl
  iframe HΦ
  iapply (goose_stateInterp_eq _ (ns + 1) obs' nt).mpr
  dsimp only [setHeap, List.nil_append]
  iframe
  ipureintro; exact Hlctx

theorem wp_PanicOp (msg : String) (Φ : val → IProp GF) :
    ▷ False ⊢ WP (Panic msg) @ s; E {{ Φ }} := by
  iintro >%H
  exact H.elim

theorem wp_ArbitraryInt :
    {{ (True : IProp GF) }} ArbitraryInt @ s; E {{ (x : w64), RET #x; True }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, σ₁, [], BaseStep.ArbitraryIntS 0 σ₁⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  cases Hstep with
  | ArbitraryIntS x =>
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists #x
    isplit
    · ipureintro; rfl
    iapply HΦ $$ %x
    itrivial

theorem wp_load (l : Loc) (q : DFrac) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l q v }} (Load (Val #l)) @ s; E
    {{ RET v; heapPointsto l q v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l q v $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read tls σ₁.1.heap l q v $$ Hσ Hl with %⟨lk, n, Heq, Hlock⟩
  cases lk with
  | Writing => cases Hlock
  | Reading n' =>
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.LoadS l n' v σ₁ Heq⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', n'', w, Hl', Heq', rfl, rfl, rfl, rfl⟩ := baseStep_Load_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Heq] at Heq'; cases Heq'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

theorem wp_prepare_write (l : Loc) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v }} (PrepareWrite (Val #l)) @ s; E
    {{ RET #(); naHeapPointstoSt WSt l (.own 1) v ∗
        (∀ v', naHeapPointsto l (.own 1) v' -∗ heapPointsto l (.own 1) v') }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l (.own 1) v $$ Hl with ⟨Hl, Hl_rest⟩
  imod na_heap_write_prepare tls σ₁.1.heap l v Writing rfl $$ Hσ Hl
    with ⟨%lk1, %⟨Hlookup, Hlock⟩, Hσ, Hl⟩
  cases lk1 with
  | Writing => cases Hlock
  | Reading n =>
  simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.PrepareWriteS l v σ₁ Hlookup⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', w, Hl', Heq', rfl, rfl, rfl, rfl⟩ := baseStep_PrepareWrite_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Hlookup] at Heq'; cases Heq'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  iframe

theorem wp_finish_store (l : Loc) (v v' : val) :
    {{ ▷ naHeapPointstoSt (GF := GF) WSt l (.own 1) v' ∗
        (∀ v', naHeapPointsto l (.own 1) v' -∗ heapPointsto l (.own 1) v') }}
      (FinishStore (Val #l) (Val v)) @ s; E
    {{ RET #(); heapPointsto l (.own 1) v }} := by
  iintro %Φ ⟨>Hl, Hl_rest⟩ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_write_finish_vs tls l v' v (Reading 0) rfl $$ Hl %σ₁.1.heap Hσ
    with ⟨%lkw, %⟨Hlookup, Hlock⟩, Hσ, Hl⟩
  cases lkw with
  | Reading n => cases Hlock
  | Writing =>
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.FinishStoreS l v σ₁ ⟨_, Hlookup⟩⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', Hl', _, rfl, rfl, rfl, rfl⟩ := baseStep_FinishStore_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

theorem isWriting_Some {A : Type} (mna : Option (NonAtomic A)) (a : A)
    (h : mna = some (Writing, a)) : IsWriting mna :=
  ⟨a, h⟩


theorem wp_start_read (l : Loc) (q : DFrac) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l q v }} (StartRead (Val #l)) @ s; E
    {{ RET v; naHeapPointstoSt (RSt 1) l q v ∗
        (∀ v', naHeapPointsto l q v' -∗ heapPointsto l q v') }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l q v $$ Hl with ⟨Hl, Hl_rest⟩
  imod na_heap_read_prepare tls naModeRl σ₁.1.heap l q v naModeRl_is_read_lock $$ Hσ Hl
    with ⟨%lk1, %n1, %⟨Hlookup, Hlock⟩, Hσ, Hl⟩
  cases lk1 with
  | Writing => cases Hlock
  | Reading n =>
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.StartReadS l n v σ₁ Hlookup⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', n', w, Hl', Heq', rfl, rfl, rfl, rfl⟩ := baseStep_StartRead_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Hlookup] at Heq'; cases Heq'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ
  iframe

theorem wp_finish_read (l : Loc) (q : DFrac) (v : val) :
    {{ ▷ naHeapPointstoSt (GF := GF) (RSt 1) l q v ∗
        (∀ v', naHeapPointsto l q v' -∗ heapPointsto l q v') }}
      (FinishRead (Val #l)) @ s; E
    {{ RET #(); heapPointsto l q v }} := by
  iintro %Φ ⟨>Hl, Hl_rest⟩ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_read_finish_vs tls naModeUrl l q v naModeUrl_is_read_unlock $$ Hl %σ₁.1.heap Hσ
    with ⟨%lk1, %n1, %⟨Hlookup, Hlock⟩, Hσ, Hl⟩
  cases lk1 with
  | Writing => cases Hlock
  | Reading n =>
  simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.FinishReadS l n1 v σ₁ Hlookup⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', n', w, Hl', Heq', rfl, rfl, rfl, rfl⟩ := baseStep_FinishRead_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Hlookup] at Heq'; cases Heq'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

theorem wp_atomic_swap (l : Loc) (v0 v : val) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v0 }} (AtomicSwap (Val #l) (Val v)) @ s; E
    {{ RET v0; heapPointsto l (.own 1) v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l (.own 1) v0 $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read_1 tls σ₁.1.heap l v0 $$ Hσ Hl with %⟨lk, Hlookup, Hlock⟩
  cases lk with
  | Writing => cases Hlock
  | Reading n =>
  simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
  imod na_heap_write tls σ₁.1.heap l (Reading 0) v0 v rfl $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.AtomicSwapS l v0 v σ₁ Hlookup⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', w, Hl', Heq', rfl, rfl, rfl, rfl⟩ := baseStep_AtomicSwap_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Hlookup] at Heq'; cases Heq'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v0
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

theorem wp_atomic_add (l : Loc) (v0 v1 v : val) (Hev : atomicAddEval v0 v1 = some v) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v0 }} (AtomicAdd (Val #l) (Val v1)) @ s; E
    {{ RET v; heapPointsto l (.own 1) v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l (.own 1) v0 $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read_1 tls σ₁.1.heap l v0 $$ Hσ Hl with %⟨lk, Hlookup, Hlock⟩
  cases lk with
  | Writing => cases Hlock
  | Reading n =>
  simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
  imod na_heap_write tls σ₁.1.heap l (Reading 0) v0 v rfl $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.AtomicAddS l v0 v1 v σ₁ Hlookup Hev⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', w, w', Hl', Heq', Hev', rfl, rfl, rfl, rfl⟩ := baseStep_AtomicAdd_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [Hlookup] at Heq'; cases Heq'
  rw [Hev] at Hev'; cases Hev'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

theorem wp_cmpxchg_fail (l : Loc) (q : DFrac) (v' v1 v2 : val) (Hne : v' ≠ v1) :
    {{ ▷ heapPointsto (GF := GF) l q v' }} (CmpXchg (Val #l) (Val v1) (Val v2)) @ s; E
    {{ RET (PairV v' #false); heapPointsto l q v' }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l q v' $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read tls σ₁.1.heap l q v' $$ Hσ Hl with %⟨lk, n, Hlookup, Hlock⟩
  cases lk with
  | Writing => cases Hlock
  | Reading n' =>
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.CmpXchgFailS l n' v' v1 v2 σ₁ Hlookup Hne⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨rfl, rfl, Hcase⟩ := baseStep_CmpXchg_inv Hstep
  rcases Hcase with ⟨l', n'', vl, Hl', Heq', _, rfl, rfl⟩ | ⟨l', vl, Hl', Heq', Hvl, _, _⟩
  · cases GoGlobalContext.intoVal_inj_loc Hl'
    rw [Hlookup] at Heq'; cases Heq'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists PairV v' #false
    isplit
    · ipureintro; rfl
    iapply HΦ
    iapply Hl_rest $$ Hl
  · cases GoGlobalContext.intoVal_inj_loc Hl'
    rw [Hlookup] at Heq'; cases Heq'
    exact (Hne Hvl).elim

theorem wp_cmpxchg_suc (l : Loc) (v1 v2 v' : val) (Heq : v' = v1) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v' }} (CmpXchg (Val #l) (Val v1) (Val v2)) @ s; E
    {{ RET (PairV v' #true); heapPointsto l (.own 1) v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l (.own 1) v' $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read_1 tls σ₁.1.heap l v' $$ Hσ Hl with %⟨lk, Hlookup, Hlock⟩
  cases lk with
  | Writing => cases Hlock
  | Reading n =>
  simp only [tls_Reading, LockState.RSt.injEq] at Hlock; subst Hlock
  imod na_heap_write tls σ₁.1.heap l (Reading 0) v' v2 rfl $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.CmpXchgSucS l v' v1 v2 σ₁ Hlookup Heq⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨rfl, rfl, Hcase⟩ := baseStep_CmpXchg_inv Hstep
  rcases Hcase with ⟨l', n'', vl, Hl', Heq', Hvl, _, _⟩ | ⟨l', vl, Hl', Heq', _, rfl, rfl⟩
  · cases GoGlobalContext.intoVal_inj_loc Hl'
    rw [Hlookup] at Heq'; cases Heq'
    exact (Hvl Heq).elim
  · cases GoGlobalContext.intoVal_inj_loc Hl'
    rw [Hlookup] at Heq'; cases Heq'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists PairV v' #true
    isplit
    · ipureintro; rfl
    iapply HΦ
    iapply Hl_rest $$ Hl

/-! ### Allocation -/

theorem gmap_singleton_union_eq_insert {K V : Type} [DecidableEq K] (m : GMap K V) (k : K) (v : V) :
    ({[k := v]} : GMap K V) ∪ m = <[k := v]> m := by
  apply GMap.ext; intro k'
  rw [show (({[k := v]} : GMap K V) ∪ m).lookup k' = _ from GMap.lookup_union _ _ k']
  rw [show ((<[k := v]> m) : GMap K V).lookup k' = _ from GMap.lookup_insert_eq_iff m k k' v]
  rw [show ({[k := v]} : GMap K V).lookup k' = _ from GMap.lookup_singleton_iff k k' v]
  split <;> simp

/-- A fresh block is a real one (`locCar ≠ 0`): its start is non-null at offset `0`. -/
theorem IsFresh.car {σ : CfgState} {l : Loc} (h : IsFresh σ l) : l.locCar ≠ 0 := by
  intro hc
  apply (h.1 0).1
  have ho : l.locOff = 0 := h.2
  cases l; simp only [Loc.add, null] at *; congr <;> omega

theorem exists_isFresh (σ : CfgState) : ∃ l, IsFresh σ l := by
  refine ⟨freshLocs σ.1.heap.domList, fun i => ⟨freshLocs_non_null _ i, ?_⟩, freshLocs_off_0 _⟩
  cases h : σ.1.heap !! (freshLocs σ.1.heap.domList +ₗ i) with
  | none => rfl
  | some _ =>
    exact absurd ((GMap.mem_dom_list σ.1.heap _).mpr (by rw [h]; rfl)) (freshLocs_fresh _ i)

def pointstoVals (l : Loc) (q : DFrac) (vs : List val) : IProp GF :=
  [∗list] j ↦ vj ∈ vs, heapPointsto (l +ₗ (j : Int)) q vj

instance pointstoVals_timeless (l : Loc) (q : DFrac) (vs : List val) :
    Timeless (pointstoVals (GF := GF) l q vs) := by
  unfold pointstoVals; infer_instance

/-- The bytes `bs` as values. -/
def byteVals (bs : List w8) : List val := bs.map fun b => LitV (LitByte b)

theorem pointstoVals_to_na (l : Loc) (q : DFrac) (vs : List val) :
    pointstoVals l q vs ⊢ ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) q v : IProp GF) := by
  unfold pointstoVals
  apply BigSepL.bigSepL_mono
  intro k x _
  unfold heapPointsto
  iintro ⟨-, H⟩
  iexact H

theorem pointstoVals_of_na (l : Loc) (q : DFrac) (vs : List val) (hc : l.locCar ≠ 0) :
    ([∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) q v : IProp GF) ⊢ pointstoVals l q vs := by
  unfold pointstoVals
  apply BigSepL.bigSepL_mono
  intro k x _
  exact na_pointsto_to_heap _ _ _ hc

theorem pointstoVals_car (l : Loc) (q : DFrac) (vs : List val) (h : vs ≠ []) :
    pointstoVals l q vs ⊢ (⌜l.locCar ≠ 0⌝ : IProp GF) := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs =>
    unfold pointstoVals
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, -⟩
    unfold heapPointsto
    icases H0 with ⟨%hc, -⟩
    ipureintro; simpa using hc

theorem wp_allocN_seq (v : val) :
    {{ (True : IProp GF) }} (Alloc (Val v)) @ s; E
    {{ l, RET #l; pointstoVals l (.own 1) [v] }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    obtain ⟨l, hl⟩ := exists_isFresh σ₁
    exact ⟨[], _, _, [], BaseStep.AllocS v l σ₁ hl⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l, Hfresh, rfl, rfl, rfl, rfl⟩ := baseStep_Alloc_inv Hstep
  have Hnone : σ₁.1.heap !! l = none := by simpa using (Hfresh.1 0).2
  have Hnn : l.locCar ≠ 0 := Hfresh.car
  imod na_heap_alloc tls σ₁.1.heap l v (Reading 0) Hnone rfl $$ Hσ with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro
    simp only [setHeap, stateInitHeap, gmap_singleton_union_eq_insert]; rfl
  iexists #l
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply BigSepL.bigSepL_singleton.2
  rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
  iapply na_pointsto_to_heap l _ v Hnn $$ Hl

theorem wp_alloc_untyped (v : val) :
    {{ (True : IProp GF) }} (Alloc (Val v)) @ s; E
    {{ l, RET #l; heapPointsto l (.own 1) v }} := by
  iintro %Φ _ HΦ
  iapply wp_allocN_seq v
  · itrivial
  inext
  iintro %l Hl
  iapply HΦ
  unfold pointstoVals
  icases BigSepL.bigSepL_singleton.1 $$ Hl with Hl
  rw [show l +ₗ ((0 : Nat) : Int) = l by simp]
  iexact Hl

/-! ### Threads: `Fork` and `ThreadExit`

`Fork e` spawns the thread `e ;; ThreadExit`. In the bounded semantics it takes
one thread token out of the thread fuel (or stutters when the fuel is exhausted,
which `wp_fork_tok` absorbs by Löb induction as `wp_GoInstruction_preceipt`
does), and the forked thread's `ThreadExit` puts one back. `wp_fork_tok` is the
primitive rule: the forking thread receives the token and the forked thread
must end with one; `wp_fork` is the token-free form (the forked thread keeps its
token to itself). -/

/-- `ThreadExit`, the last step of a forked thread: it returns a thread token to
the thread fuel. -/
theorem wp_ThreadExit (Φ : val → IProp GF) :
    ⊢ threadTok -∗ ▷ Φ #() -∗ WP ThreadExit @ s; E {{ Φ }} := by
  iintro Htok HΦ
  iapply wp_lift_atomic_base_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, _, .exit (BaseStep.ThreadExitS σ)⟩
  inext
  iintro %e₂ %s₂ %eₜ %Hstep _
  cases Hstep with
  | step hp _ => cases hp
  | tick hc _ => cases hc
  | stutter hc _ => cases hc
  | exit Hb =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := baseStep_ThreadExit_inv Hb
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht Htok]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      isplitl [Hheap Hffi Hgs Hgffi Hproph]
      · iapply (goose_stateInterp_eq _ _ _ _).mpr
        dsimp only [List.nil_append]
        iframe
        ipureintro; exact Hlctx
      · iframe Hc
        iapply (threadFuel_exit (GF := GF) t)
        iframe
    isplitl [HΦ]
    · iexists #()
      isplit
      · ipureintro; rfl
      · iexact HΦ
    iapply BigSepL.bigSepL_nil.2
    itrivial

/-- The forked thread `e ;; ThreadExit` runs `e`, which must end with a thread
token, and returns the token at its `ThreadExit`. -/
theorem wp_seq_ThreadExit (e : Expr) :
    WP e @ s; ⊤ {{ _v, (threadTok : IProp GF) }} ⊢ WP (Seq e ThreadExit) @ s; ⊤ {{ _v, True }} := by
  refine .trans (wp_mono fun v => ?_)
    (wp_bind (fill [EctxItem.AppRCtx (Rec BAnon BAnon ThreadExit)]))
  refine (?_ : (threadTok : IProp GF) ⊢
    WP (App (Rec BAnon BAnon ThreadExit) (Val v)) @ s; ⊤ {{ _v, True }})
  refine .trans ?_ (wp_bind (fill [EctxItem.AppLCtx v]))
  refine .trans ?_ (wp_pure_step_later (Hexec := pure_recc BAnon BAnon ThreadExit) trivial)
  refine (?_ : (threadTok : IProp GF) ⊢ ▷ (£ 1 -∗ WP (Val (RecV BAnon BAnon ThreadExit)) @ s; ⊤
    {{ w, WP (App (Val w) (Val v)) @ s; ⊤ {{ _v, True }} }}))
  iintro Htok
  inext
  iintro _
  iapply wp_value'
  iapply wp_pure_step_later (e₂ := ThreadExit) (Hexec := pure_beta BAnon BAnon ThreadExit v) trivial
  inext
  iintro _
  iapply wp_ThreadExit $$ Htok
  inext
  itrivial

/-- `Fork e`: the forking thread receives a thread token (out of the thread fuel)
and the forked thread must end with one (it is returned at its `ThreadExit`).
Whether the token is kept by the forking thread, given to the forked thread or
deposited in an invariant is up to the proof. -/
theorem wp_fork_tok (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ WP e @ s; ⊤ {{ _v, threadTok }} ∗ Φ #()) -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro H
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  have Hred : BaseStep.Reducible (Fork e, ((σ, ⟨c, t⟩) : BcfgState)) := by
    cases t with
    | zero => exact ⟨[], _, _, [], .forkStutter⟩
    | succ t => exact ⟨[], _, _, _, .fork (BaseStep.ForkS e σ)⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_fill_of_baseStep_reducible (K := []) Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨e₂', rfl, Hbs⟩ :=
    exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible (K := []) Hred Hstep
  cases Hbs with
  | step hp _ => cases hp
  | tick hc _ => cases hc
  | stutter hc _ => cases hc
  | fork Hb =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := baseStep_Fork_inv Hb
    rename_i t
    icases threadFuel_fork t $$ Ht with ⟨Ht, Htok⟩
    icases H $$ Htok with ⟨He, HΦ⟩
    imod Hclose
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [HΦ]
    · iapply wp_value'
      iexact HΦ
    iapply BigSepL.bigSepL_singleton.2
    iapply wp_seq_ThreadExit $$ He
  | forkStutter =>
    imod Hclose
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [IH H]
    · iapply IH
      inext
      iexact H
    iapply BigSepL.bigSepL_nil.2
    itrivial

/-- `Fork e` without thread tokens: the forked thread's token stays with it. -/
theorem wp_fork (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ _v, True }} -∗ ▷ Φ #() -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_fork_tok
  inext
  iintro Htok
  iframe HΦ
  iapply (wp_wand (Φ := fun _ => iprop(threadTok ∗ True))) $$ [He Htok]
  · iapply (wp_frame_r (Φ := fun _ => iprop(True)))
    iframe
  iintro %_ ⟨Htok, -⟩
  iexact Htok

/-- `Fork e`, the fresh thread token going to the forked thread: its body receives the token and
must end with one. (`wp_fork` is this with the token framed through the body.) -/
theorem wp_fork_tok_body (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ WP e @ s; ⊤ {{ _v, threadTok }}) -∗ ▷ Φ #() -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_fork_tok
  inext
  iintro Htok
  iframe HΦ
  iapply He $$ Htok

/-- `Fork e`, the fresh thread token staying with the forking thread: the forked thread must end
with a token of its own, e.g. one it takes back out of an invariant at its `Done`, where the
forking thread deposited its own before the `go` statement. -/
theorem wp_fork_tok_self (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ _v, threadTok }} -∗ ▷ (threadTok -∗ Φ #()) -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_fork_tok
  inext
  iintro Htok
  iframe He
  iapply HΦ $$ Htok

/-! ### Go instructions -/

/-- WP for go instructions, with time receipts. Go instructions
are the counted steps of the bounded semantics: below the bound the step yields
an exclusive receipt `⧗ 1` and increments a persistent receipt `⧖ m` (the
paper's `{⧖ m} tick v {⧗ 1 ∗ ⧖ (m + 1)}`); at the bound the step stutters,
which is handled by Löb induction. -/
theorem wp_GoInstruction_preceipt (K : List EctxItem) (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (m : Nat) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s') :
    ⧖ m ∗ ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ⧗ 1 -∗ ⧖ (m + 1) -∗ ownGoStateCtx gs ={E}=∗
          ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro ⟨#Hm, HΦ⟩
  iapply wp_lift_step (EctxLanguage.fill_not_val K _ rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ₁ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht⟩
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  obtain ⟨e', s', h⟩ := Hok σ₁.1.goState.packageState
  have Hreal := BaseStep.GoInstructionS op arg e' s' σ₁ (Hlctx ▸ h)
  have Hred : BaseStep.Reducible
      (App (Val (GoInstruction op)) (Val arg), ((σ₁, ⟨c, t⟩) : BcfgState)) := by
    cases c with
    | zero => exact ⟨[], _, (σ₁, ⟨0, t⟩), [], .stutter rfl Hreal⟩
    | succ c => exact ⟨[], e', (_, ⟨c, t⟩), [], .tick rfl Hreal⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_fill_of_baseStep_reducible Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨e₂', rfl, Hbs⟩ :=
    exists_baseStep_of_primStep_fill_of_redex_baseStep_reducible Hred Hstep
  cases Hbs with
  | step hnc _ => cases hnc
  | tick _ Hbs =>
    obtain ⟨s', Hgo, rfl, rfl, rfl⟩ := baseStep_GoInstruction_inv Hbs
    rw [Hlctx] at Hgo
    imod Hclose
    imod receiptFuel_tick _ m $$ [Hc] with ⟨Hc, Hr, Hm'⟩
    · iframe Hc; iexact Hm
    imod HΦ $$ %e₂' %_ %s' %Hgo Hcred Hr Hm' Hgs with ⟨Hgs, Hwp⟩
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    iframe Hwp
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | stutter _ _ =>
    imod Hclose
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc Ht]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht
      iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [IH HΦ]
    · iapply IH
      iframe Hm
      inext
      iexact HΦ
    iapply BigSepL.bigSepL_nil.2
    itrivial

/-- `wp_GoInstruction_preceipt` without persistent receipts: a Go instruction
step yields an exclusive time receipt `⧗ 1`. -/
theorem wp_GoInstruction_receipt (K : List EctxItem) (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s') :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ⧗ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iintro HΦ
  imod preceipt_zero (GF := GF) with #H0
  iapply wp_GoInstruction_preceipt K op arg Φ 0 Hok
  iframe H0
  inext
  iintro %e' %gs %gs' %Hstep Hlc Hr _ Hgs
  iapply HΦ $$ %e' %gs %gs' %Hstep Hlc Hr Hgs

/-- WP for go instructions. -/
theorem wp_GoInstruction (K : List EctxItem) (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s') :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_GoInstruction_receipt K op arg Φ Hok
  inext
  iintro %e' %gs %gs' %Hstep Hlc _ Hgs
  iapply HΦ $$ %e' %gs %gs' %Hstep Hlc Hgs

/-- `wp_GoInstruction` with an empty evaluation context. -/
theorem wp_GoInstruction' (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s') :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP e' @ s; E {{ Φ }}))
    ⊢ WP (App (Val (GoInstruction op)) (Val arg)) @ s; E {{ Φ }} :=
  wp_GoInstruction [] op arg Φ Hok

/-! ### Prophecy variables -/

theorem goose_proph_new (p : proph_id) (ps : GSet proph_id) (pvs : List Observation)
    (Hp : p ∉ ps) :
    ⊢@{IProp GF} prophMapInterp pvs ps ==∗
      prophMapInterp pvs ({[p := ()]} ∪ ps) ∗ proph p (prophListResolves pvs p) :=
  ProphMap.new_proph p ps pvs Hp

theorem wp_new_proph :
    {{ (True : IProp GF) }} NewProph @ s; E
    {{ (pvs : List val) (p : proph_id), RET #p; proph p pvs }} := by
  iintro %Φ _ HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨p, hp⟩ := Iris.Std.List.fresh σ₁.2.usedProphId.domList
    exact ⟨[], _, _, [], BaseStep.NewProphS p σ₁ (fun h => hp ((GMap.mem_dom_list _ _).mpr h))⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨p, Hp, rfl, rfl, rfl, rfl⟩ := baseStep_NewProph_inv Hstep
  simp only [List.nil_append]
  imod goose_proph_new p σ₁.2.usedProphId obs' Hp $$ Hproph with ⟨Hproph, Htok⟩
  imodintro
  isplitr
  · ipureintro; trivial
  isplitl [Hheap Hffi Hgs Hgffi Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    dsimp only
    iframe
    ipureintro; exact Hlctx
  iexists #p
  isplit
  · ipureintro; rfl
  iapply HΦ $$ %_ %p Htok

theorem wp_resolve_proph (p : proph_id) (pvs : List val) (v : val) :
    {{ proph (GF := GF) p pvs }} (ResolveProph (Val #p) (Val v)) @ s; E
    {{ (pvs' : List val), RET #(); ⌜pvs = v :: pvs'⌝ ∗ proph p pvs' }} := by
  iintro %Φ Hp HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨_, _, _, [], BaseStep.ResolveProphS p v σ₁⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨p', Hp', rfl, rfl, rfl, rfl⟩ := baseStep_ResolveProph_inv Hstep
  cases GoGlobalContext.intoVal_inj_proph_id Hp'
  simp only [List.singleton_append]
  icombine Hproph Hp as Hcomb
  imod ProphMap.resolve_proph p v obs' _ pvs $$ Hcomb
    with ⟨%pvs', %Hpvs, Hproph, Hp⟩
  imodintro
  isplitr
  · ipureintro; trivial
  isplitl [Hheap Hffi Hgs Hgffi Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    iframe
    ipureintro; exact Hlctx
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ $$ %pvs'
  iframe Hp
  ipureintro; exact Hpvs

end lifting

/-! ### Encoded values: allocation, two-phase reads and writes, atomics -/

section enc_wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
variable {σ σ' : CfgState} {κ : List Observation} {e' : Expr} {efs : List Expr}
open ProofMode



theorem cellsAt_unique {h : GMap Loc (NonAtomic val)} {l : Loc} {cs cs' : List (NonAtomic val)}
    (H : CellsAt h l cs) (H' : CellsAt h l cs') (hlen : cs.length = cs'.length) : cs = cs' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have e1 := H i h1
  rw [H' i h2] at e1
  exact (Option.some.inj e1).symm

theorem cellsAt_eq_of_snd {h : GMap Loc (NonAtomic val)} {l : Loc} {cs cs' : List (NonAtomic val)}
    (H : CellsAt h l cs) (H' : CellsAt h l cs') (hlen : cs'.length = cs.length) : cs' = cs :=
  cellsAt_unique H' H hlen

theorem decode_ne_nil {enc : Encoding} {vs : List val} {v : val} (h : decode enc vs = some v) :
    vs ≠ [] := by
  rintro rfl
  cases enc with
  | word n =>
    simp [decode] at h
    omega
  | cell k => simp [decode] at h

theorem encode_length {enc : Encoding} {v : val} {vs : List val} (h : encode enc v = some vs) :
    vs.length = enc.size := by
  cases enc with
  | word n =>
    simp only [encode, Option.map_eq_some_iff] at h
    obtain ⟨z, -, rfl⟩ := h
    simp [leBytes_length, Encoding.size]
  | cell k =>
    simp only [encode] at h
    split at h
    · rename_i hk; cases h; simp [Encoding.size, tails]; have := hk.1; omega
    · cases h

theorem wordLitZ?_spec {n : Nat} {v : val} {z : Int} (h : wordLitZ? n v = some z) :
    (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ 0 ≤ z ∧ z < 2 ^ (8 * n) ∧ wordLit n z = v := by
  unfold wordLitZ? at h
  split at h <;> (try cases h)
  · rename_i x
    refine ⟨by decide, by omega, by have := x.isLt; simp; omega, ?_⟩
    show LitV (LitByte (BitVec.ofInt 8 (x.toNat : Int))) = _
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rename_i x
    refine ⟨by decide, by omega, by have := x.isLt; simp; omega, ?_⟩
    show LitV (LitInt16 (BitVec.ofInt 16 (x.toNat : Int))) = _
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rename_i x
    refine ⟨by decide, by omega, by have := x.isLt; simp; omega, ?_⟩
    show LitV (LitInt32 (BitVec.ofInt 32 (x.toNat : Int))) = _
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rename_i x
    refine ⟨by decide, by omega, by have := x.isLt; simp; omega, ?_⟩
    show LitV (LitInt (BitVec.ofInt 64 (x.toNat : Int))) = _
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mapM_byteOf_map (bs : List w8) :
    (bs.map fun b => LitV (LitByte b)).mapM byteOf? = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons, byteOf?, ih]

/-- An encoded value decodes to itself. -/
theorem decode_encode {enc : Encoding} {v : val} {vs : List val} (h : encode enc v = some vs) :
    decode enc vs = some v := by
  cases enc with
  | word n =>
    simp only [encode, Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨hn, h0, h1, hv⟩ := wordLitZ?_spec hz
    simp only [decode, if_pos hn, mapM_byteOf_map, Option.bind_some, leBytes_length,
      ↓reduceIte, leInt_leBytes, Int.emod_eq_of_lt h0 h1, hv]
  | cell k =>
    simp only [encode] at h
    split at h
    · rename_i hk; cases h; simp [decode, hk]
    · cases h

/-- An encoding is never empty. -/
theorem encode_some_ne_nil {enc : Encoding} {v : val} {vs : List val}
    (h : encode enc v = some vs) : vs ≠ [] := by
  cases enc with
  | word n =>
    simp only [encode, Option.map_eq_some_iff] at h
    obtain ⟨z, hz, rfl⟩ := h
    have hn := (wordLitZ?_spec hz).1
    intro e
    have := congrArg List.length e
    simp only [List.length_map, leBytes_length, List.length_nil] at this
    omega
  | cell k =>
    simp only [encode] at h
    split at h
    · cases h; simp
    · cases h

/-- The encoding of a value, when it has one. -/
noncomputable def encodeVals (enc : Encoding) (v : val) : List val := (encode enc v).getD []

theorem encodeVals_eq {enc : Encoding} {v : val} {vs : List val} (h : encode enc v = some vs) :
    encodeVals enc v = vs := by
  simp [encodeVals, h]


theorem heapPointsto_list_to_na (f : Nat → Loc) (q : DFrac) (vs : List val) :
    ([∗list] i ↦ v ∈ vs, heapPointsto (f i) q v) ⊢
      ([∗list] i ↦ v ∈ vs, naHeapPointsto (f i) q v : IProp GF) := by
  apply BigSepL.bigSepL_mono
  intro k x _
  unfold heapPointsto
  iintro ⟨-, H⟩
  iexact H

/-- A points-to of a non-empty list of cells shows its block is a real one. -/
theorem pointstoVals_split (l : Loc) (q : DFrac) (vs : List val) :
    pointstoVals l q vs ⊢
      (⌜vs = [] ∨ l.locCar ≠ 0⌝ ∗
        [∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) q v : IProp GF) := by
  cases vs with
  | nil =>
    iintro _
    isplitr
    · ipureintro; left; rfl
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | cons v vs =>
    unfold pointstoVals
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H0, H⟩
    ihave H := heapPointsto_list_to_na (fun k => l +ₗ ((k + 1 : Nat) : Int)) q vs $$ H
    unfold heapPointsto
    icases H0 with ⟨%hc, H0⟩
    isplitr
    · ipureintro; right; simpa using hc
    iapply BigSepL.bigSepL_cons.2
    iframe H0
    iexact H

theorem pointstoVals_split' (l : Loc) (q : DFrac) (vs : List val) (hne : vs ≠ []) :
    pointstoVals l q vs ⊢
      (⌜l.locCar ≠ 0⌝ ∗ [∗list] i ↦ v ∈ vs, naHeapPointsto (l +ₗ (i : Int)) q v : IProp GF) := by
  iintro H
  icases pointstoVals_split l q vs $$ H with ⟨%hc, H⟩
  iframe H
  ipureintro
  rcases hc with h | h
  · exact absurd h hne
  · exact h

/-! #### Inversion lemmas -/

theorem baseStep_AllocN_inv {n v : val} (h : BaseStep (AllocN (Val n) (Val v)) σ κ e' σ' efs) :
    ∃ (k a : w64) (l : Loc), n = PairV (LitV (LitInt k)) (LitV (LitInt a)) ∧
      κ = [] ∧ e' = Val #l ∧ efs = [] ∧
      ((uint.nat k ≠ 0 ∧ IsFreshAligned σ l (uint.nat a) ∧
          σ' = setCells l ((List.replicate (uint.nat k) v).map Free) σ) ∨
        (uint.nat k = 0 ∧ l.locCar ≠ 0 ∧ (uint.nat a : Int) ∣ l.locOff ∧ σ' = σ)) := by
  cases h with
  | AllocNS _ _ _ _ _ hk hf => exact ⟨_, _, _, rfl, rfl, rfl, rfl, .inl ⟨hk, hf, rfl⟩⟩
  | AllocN0S _ _ _ _ _ hk hc ha => exact ⟨_, _, _, rfl, rfl, rfl, rfl, .inr ⟨hk, hc, ha, rfl⟩⟩

theorem baseStep_StartReadN_inv {enc : Encoding} {v : val}
    (h : BaseStep (StartReadN enc (Val v)) σ κ e' σ' efs) :
    ∃ l cs w, v = #l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, ∃ n, c.1 = Reading n) ∧ decode enc (cs.map Prod.snd) = some w ∧
      κ = [] ∧ e' = Val w ∧ σ' = setCells l (cs.map fun c => (naModeRl c.1, c.2)) σ ∧
      efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_FinishReadN_inv {enc : Encoding} {v : val}
    (h : BaseStep (FinishReadN enc (Val v)) σ κ e' σ' efs) :
    ∃ l cs, v = #l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, ∃ n, c.1 = Reading (n + 1)) ∧
      κ = [] ∧ e' = Val #() ∧ σ' = setCells l (cs.map fun c => (naModeUrl c.1, c.2)) σ ∧
      efs = [] := by
  cases h; exact ⟨_, _, rfl, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_PrepareWriteN_inv {enc : Encoding} {v : val}
    (h : BaseStep (PrepareWriteN enc (Val v)) σ κ e' σ' efs) :
    ∃ l cs, v = #l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, c.1 = Reading 0) ∧ WriteCompat enc (cs.map Prod.snd) ∧
      κ = [] ∧ e' = Val #() ∧ σ' = setCells l (cs.map fun c => (Writing, c.2)) σ ∧
      efs = [] := by
  cases h; exact ⟨_, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_FinishStoreN_inv {enc : Encoding} {v1 v2 : val}
    (h : BaseStep (FinishStoreN enc (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l cs vs, v1 = #l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, c.1 = Writing) ∧ encode enc v2 = some vs ∧
      κ = [] ∧ e' = Val #() ∧ σ' = setCells l (vs.map Free) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_LoadN_inv {enc : Encoding} {v : val}
    (h : BaseStep (LoadN enc (Val v)) σ κ e' σ' efs) :
    ∃ l cs w, v = #l ∧ Aligned enc l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, ∃ n, c.1 = Reading n) ∧ decode enc (cs.map Prod.snd) = some w ∧
      κ = [] ∧ e' = Val w ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_SwapN_inv {enc : Encoding} {v1 v2 : val}
    (h : BaseStep (SwapN enc (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l cs w vs, v1 = #l ∧ Aligned enc l ∧ cs.length = enc.size ∧ CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, c.1 = Reading 0) ∧ decode enc (cs.map Prod.snd) = some w ∧
      encode enc v2 = some vs ∧
      κ = [] ∧ e' = Val w ∧ σ' = setCells l (vs.map Free) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_AddN_inv {enc : Encoding} {v1 v2 : val}
    (h : BaseStep (AddN enc (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ n l cs w w' vs, enc = .word n ∧ v1 = #l ∧ Aligned (.word n) l ∧ cs.length = n ∧
      CellsAt σ.1.heap l cs ∧
      (∀ c ∈ cs, c.1 = Reading 0) ∧ decode (.word n) (cs.map Prod.snd) = some w ∧
      atomicAddEval w v2 = some w' ∧ encode (.word n) w' = some vs ∧
      κ = [] ∧ e' = Val w' ∧ σ' = setCells l (vs.map Free) σ ∧ efs = [] := by
  cases h; exact ⟨_, _, _, _, _, _, rfl, rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, rfl, rfl⟩

theorem baseStep_CmpXchgN_inv {enc : Encoding} {v1 v2 : val}
    (h : BaseStep (CmpXchgN enc (Val v1) (Val v2)) σ κ e' σ' efs) :
    ∃ l cs w o n, v1 = #l ∧ v2 = PairV o n ∧ Aligned enc l ∧ cs.length = enc.size ∧
      CellsAt σ.1.heap l cs ∧ decode enc (cs.map Prod.snd) = some w ∧ κ = [] ∧ efs = [] ∧
      (((∀ c ∈ cs, ∃ n, c.1 = Reading n) ∧ w ≠ o ∧ e' = Val (PairV w #false) ∧ σ' = σ) ∨
       ((∀ c ∈ cs, c.1 = Reading 0) ∧ w = o ∧ ∃ vs, encode enc n = some vs ∧
         e' = Val (PairV w #true) ∧ σ' = setCells l (vs.map Free) σ)) := by
  cases h with
  | CmpXchgNFailS =>
    exact ⟨_, _, _, _, _, rfl, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl, Or.inl ⟨‹_›, ‹_›, rfl, rfl⟩⟩
  | CmpXchgNSucS =>
    exact ⟨_, _, _, _, _, rfl, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl, rfl,
      Or.inr ⟨‹_›, ‹_›, _, ‹_›, rfl, rfl⟩⟩

theorem baseStep_CheckCell_inv {v : val} (h : BaseStep (CheckCell (Val v)) σ κ e' σ' efs) :
    ∃ l, v = #l ∧ (σ.1.heap !! l).isSome ∧ κ = [] ∧ e' = Val #() ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, rfl, ‹_›, rfl, rfl, rfl, rfl⟩

/-! #### WPs -/

theorem exists_isFreshAligned (σ : CfgState) (a : Nat) : ∃ l, IsFreshAligned σ l a := by
  obtain ⟨l, hl⟩ := exists_isFresh σ
  exact ⟨l, hl.1, by have := hl.2; simp [Loc.addrOffset] at this; omega,
    by have := hl.2; simp [Loc.addrOffset] at this; omega,
    by have := hl.2; simp [Loc.addrOffset] at this; rw [this]; exact Int.dvd_zero _⟩

theorem IsFreshAligned.car {σ : CfgState} {l : Loc} {a : Nat} (h : IsFreshAligned σ l a) :
    l.locCar ≠ 0 := by
  intro hc
  apply (h.1 (-l.locOff)).1
  cases l; simp only [Loc.add, null] at *; congr <;> omega

/-- `AllocN (n, a) v`: `n` owned cells holding `v` (none if `n = 0`), at a non-null
location aligned to `a`. -/
theorem wp_allocN (n a : w64) (v : val) :
    {{ (True : IProp GF) }}
      (AllocN (Val (PairV (LitV (LitInt n)) (LitV (LitInt a)))) (Val v)) @ s; E
    {{ l, RET #l; ⌜l.locCar ≠ 0 ∧ ((uint.nat a : Nat) : Int) ∣ l.locOff⌝ ∗
        pointstoVals l (.own 1) (List.replicate (uint.nat n) v) }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    obtain ⟨l, hl⟩ := exists_isFreshAligned σ₁ (uint.nat a)
    by_cases hn : uint.nat n = 0
    · exact ⟨[], _, _, [], BaseStep.AllocN0S n a v l σ₁ hn hl.car hl.2.2.2⟩
    · exact ⟨[], _, _, [], BaseStep.AllocNS n a v l σ₁ hn hl⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨k, a', l, Hk, rfl, rfl, rfl, Hcase⟩ := baseStep_AllocN_inv Hstep
  cases Hk
  rcases Hcase with ⟨_, Hfresh, rfl⟩ | ⟨hk, hc, ha, rfl⟩
  · have Hnn : l.locCar ≠ 0 := Hfresh.car
    imod na_heap_alloc_list σ₁.1.heap l (List.replicate (uint.nat n) v) (fun i => (Hfresh.1 i).2)
      $$ Hσ with ⟨Hσ, Hl⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists #l
    isplit
    · ipureintro; rfl
    iapply HΦ
    isplitl []
    · ipureintro; exact ⟨Hnn, Hfresh.2.2.2⟩
    unfold pointstoVals
    iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
      na_pointsto_to_heap (l +ₗ (i : Int)) _ x Hnn)) $$ Hl
  · imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists #l
    isplit
    · ipureintro; rfl
    iapply HΦ
    isplitl []
    · ipureintro; exact ⟨hc, ha⟩
    rw [hk]
    unfold pointstoVals
    simp only [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    itrivial

/-- The cells of an encoded value being read (between `StartReadN` and `FinishReadN`). -/
def readingCells (l : Loc) (q : DFrac) (vs : List val) : IProp GF :=
  iprop(⌜l.locCar ≠ 0⌝ ∗ [∗list] i ↦ v ∈ vs, naHeapPointstoSt (RSt 1) (l +ₗ (i : Int)) q v)

/-- The cells of an encoded value being written (between `PrepareWriteN` and
`FinishStoreN`). -/
def writingCells (l : Loc) (vs : List val) : IProp GF :=
  iprop(⌜l.locCar ≠ 0⌝ ∗ [∗list] i ↦ v ∈ vs, naHeapPointstoSt WSt (l +ₗ (i : Int)) (.own 1) v)

theorem wp_start_readN (enc : Encoding) (l : Loc) (q : DFrac) (vs : List val) (v : val)
    (hlen : vs.length = enc.size) (hdec : decode enc vs = some v) :
    {{ ▷ pointstoVals (GF := GF) l q vs }} (StartReadN enc (Val #l)) @ s; E
    {{ RET v; readingCells l q vs }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l q vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_read_prepare_cells σ₁.1.heap l q vs $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.StartReadNS enc l cs v σ₁ hlen' Hcells Hrd (by rw [Hvs]; exact hdec)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', w, Hl', hlen'', Hcells', -, Hdec', rfl, rfl, rfl, rfl⟩ :=
    baseStep_StartReadN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold readingCells
  iframe Hl
  ipureintro; exact hc

theorem wp_finish_readN (enc : Encoding) (l : Loc) (q : DFrac) (vs : List val)
    (hlen : vs.length = enc.size) :
    {{ ▷ readingCells (GF := GF) l q vs }} (FinishReadN enc (Val #l)) @ s; E
    {{ RET #(); pointstoVals l q vs }} := by
  iintro %Φ Hl HΦ
  unfold readingCells
  icases Hl with ⟨>%hc, >Hl⟩
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_read_finish_cells σ₁.1.heap l q vs $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.FinishReadNS enc l cs σ₁ hlen' Hcells Hrd⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', Hl', hlen'', Hcells', -, rfl, rfl, rfl, rfl⟩ := baseStep_FinishReadN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
    na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_prepare_writeN (enc : Encoding) (l : Loc) (vs : List val)
    (hlen : vs.length = enc.size) (hne : vs ≠ []) (hcompat : WriteCompat enc vs) :
    {{ ▷ pointstoVals (GF := GF) l (.own 1) vs }} (PrepareWriteN enc (Val #l)) @ s; E
    {{ RET #(); writingCells l vs }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l _ vs hne $$ Hl with ⟨%hc, Hl⟩
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_write_prepare_cells σ₁.1.heap l vs $$ Hσ Hl with ⟨%cs, %⟨Hvs, Hcells, Hrd⟩, Hσ, Hl⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.PrepareWriteNS enc l cs σ₁ hlen' Hcells Hrd
      (by rw [Hvs]; exact hcompat)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', Hl', hlen'', Hcells', -, -, rfl, rfl, rfl, rfl⟩ := baseStep_PrepareWriteN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold writingCells
  iframe Hl
  ipureintro; exact hc

theorem wp_finish_storeN (enc : Encoding) (l : Loc) (vs vs' : List val) (v : val)
    (hlen : vs.length = enc.size) (henc : encode enc v = some vs') :
    {{ ▷ writingCells (GF := GF) l vs }} (FinishStoreN enc (Val #l) (Val v)) @ s; E
    {{ RET #(); pointstoVals l (.own 1) vs' }} := by
  iintro %Φ Hl HΦ
  unfold writingCells
  icases Hl with ⟨>%hc, >Hl⟩
  have hlen2 : vs'.length = vs.length := by rw [encode_length henc, hlen]
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  imod na_heap_write_finish_cells σ₁.1.heap l vs vs' hlen2 $$ Hσ Hl
    with ⟨%cs, %⟨Hvs, Hcells, Hwr⟩, Hσ, Hl⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.FinishStoreNS enc l v cs vs' σ₁ hlen' Hcells Hwr henc⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', vs'', Hl', -, -, -, Henc', rfl, rfl, rfl, rfl⟩ := baseStep_FinishStoreN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  rw [henc] at Henc'; cases Henc'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
    na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_loadN (enc : Encoding) (l : Loc) (q : DFrac) (vs : List val) (v : val)
    (hal : Aligned enc l) (hlen : vs.length = enc.size) (hdec : decode enc vs = some v) :
    {{ ▷ pointstoVals (GF := GF) l q vs }} (LoadN enc (Val #l)) @ s; E
    {{ RET v; pointstoVals l q vs }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l q vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases na_heap_read_cells' σ₁.1.heap l q vs $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.LoadNS enc l cs v σ₁ hal hlen' Hcells Hrd (by rw [Hvs]; exact hdec)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', w, Hl', -, hlen'', Hcells', -, Hdec', rfl, rfl, rfl, rfl⟩ :=
    baseStep_LoadN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
    na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_swapN (enc : Encoding) (l : Loc) (vs vs' : List val) (v0 v : val)
    (hal : Aligned enc l) (hlen : vs.length = enc.size) (hdec : decode enc vs = some v0)
    (henc : encode enc v = some vs') :
    {{ ▷ pointstoVals (GF := GF) l (.own 1) vs }} (SwapN enc (Val #l) (Val v)) @ s; E
    {{ RET v0; pointstoVals l (.own 1) vs' }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l _ vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  have hlen2 : vs'.length = vs.length := by rw [encode_length henc, hlen]
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases na_heap_read_cells_1' σ₁.1.heap l vs $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imod na_heap_write_cells' σ₁.1.heap l vs vs' hlen2 $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.SwapNS enc l cs v0 v vs' σ₁ hal hlen' Hcells Hrd
      (by rw [Hvs]; exact hdec) henc⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', w, vs'', Hl', -, hlen'', Hcells', -, Hdec', Henc', rfl, rfl, rfl, rfl⟩ :=
    baseStep_SwapN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  rw [henc] at Henc'; cases Henc'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v0
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
    na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_addN (n : Nat) (l : Loc) (vs vs' : List val) (v0 v v' : val)
    (hal : Aligned (.word n) l) (hlen : vs.length = n) (hdec : decode (.word n) vs = some v0)
    (hadd : atomicAddEval v0 v = some v') (henc : encode (.word n) v' = some vs') :
    {{ ▷ pointstoVals (GF := GF) l (.own 1) vs }} (AddN (.word n) (Val #l) (Val v)) @ s; E
    {{ RET v'; pointstoVals l (.own 1) vs' }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l _ vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  have hlen2 : vs'.length = vs.length := by rw [encode_length henc, hlen]; rfl
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases na_heap_read_cells_1' σ₁.1.heap l vs $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
  have hlen' : cs.length = n := by rw [← hlen, ← Hvs, List.length_map]
  imod na_heap_write_cells' σ₁.1.heap l vs vs' hlen2 $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.AddNS n l cs v0 v v' vs' σ₁ hal hlen' Hcells Hrd
      (by rw [Hvs]; exact hdec) hadd henc⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨n', l', cs', w, w', vs'', Hn, Hl', -, hlen'', Hcells', -, Hdec', Hadd', Henc',
    rfl, rfl, rfl, rfl⟩ := baseStep_AddN_inv Hstep
  cases Hn
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  rw [hadd] at Hadd'; cases Hadd'
  rw [henc] at Henc'; cases Henc'
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists v'
  isplit
  · ipureintro; rfl
  iapply HΦ
  unfold pointstoVals
  iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
    na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_cmpxchgN_fail (enc : Encoding) (l : Loc) (q : DFrac) (vs : List val) (vl v1 v2 : val)
    (hal : Aligned enc l) (hlen : vs.length = enc.size) (hdec : decode enc vs = some vl)
    (hne : vl ≠ v1) :
    {{ ▷ pointstoVals (GF := GF) l q vs }} (CmpXchgN enc (Val #l) (Val (PairV v1 v2))) @ s; E
    {{ RET (PairV vl #false); pointstoVals l q vs }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l q vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases na_heap_read_cells' σ₁.1.heap l q vs $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.CmpXchgNFailS enc l cs vl v1 v2 σ₁ hal hlen' Hcells Hrd
      (by rw [Hvs]; exact hdec) hne⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', w, o, n, Hl', Hv2, -, hlen'', Hcells', Hdec', rfl, rfl, Hcase⟩ :=
    baseStep_CmpXchgN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases Hv2
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  rcases Hcase with ⟨-, -, rfl, rfl⟩ | ⟨-, Heq, -⟩
  · imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists PairV vl #false
    isplit
    · ipureintro; rfl
    iapply HΦ
    unfold pointstoVals
    iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
      na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl
  · exact absurd Heq hne

theorem wp_cmpxchgN_suc (enc : Encoding) (l : Loc) (vs vs' : List val) (vl v1 v2 : val)
    (hal : Aligned enc l) (hlen : vs.length = enc.size) (hdec : decode enc vs = some vl)
    (heq : vl = v1) (henc : encode enc v2 = some vs') :
    {{ ▷ pointstoVals (GF := GF) l (.own 1) vs }}
      (CmpXchgN enc (Val #l) (Val (PairV v1 v2))) @ s; E
    {{ RET (PairV vl #true); pointstoVals l (.own 1) vs' }} := by
  iintro %Φ >Hl HΦ
  icases pointstoVals_split' l _ vs (decode_ne_nil hdec) $$ Hl with ⟨%hc, Hl⟩
  have hlen2 : vs'.length = vs.length := by rw [encode_length henc, hlen]
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases na_heap_read_cells_1' σ₁.1.heap l vs $$ Hσ Hl with %⟨cs, Hvs, Hcells, Hrd⟩
  have hlen' : cs.length = enc.size := by rw [← hlen, ← Hvs, List.length_map]
  imod na_heap_write_cells' σ₁.1.heap l vs vs' hlen2 $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.CmpXchgNSucS enc l cs vl v1 v2 vs' σ₁ hal hlen' Hcells Hrd
      (by rw [Hvs]; exact hdec) heq henc⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', cs', w, o, n, Hl', Hv2, -, hlen'', Hcells', Hdec', rfl, rfl, Hcase⟩ :=
    baseStep_CmpXchgN_inv Hstep
  cases GoGlobalContext.intoVal_inj_loc Hl'
  cases Hv2
  cases cellsAt_eq_of_snd Hcells Hcells' (by omega)
  rw [Hvs, hdec] at Hdec'; cases Hdec'
  rcases Hcase with ⟨-, Hne, -⟩ | ⟨-, -, vs'', Henc', rfl, rfl⟩
  · exact absurd heq Hne
  · rw [henc] at Henc'; cases Henc'
    imodintro
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl [Hσ]
    · iexists _; iframe Hσ; ipureintro; rfl
    iexists PairV vl #true
    isplit
    · ipureintro; rfl
    iapply HΦ
    unfold pointstoVals
    iapply (BigSepL.bigSepL_mono (fun {i x} _ =>
      na_pointsto_to_heap (l +ₗ (i : Int)) _ x hc)) $$ Hl

theorem wp_checkCell (l : Loc) (q : DFrac) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l q v }} (CheckCell (Val #l)) @ s; E
    {{ RET #(); heapPointsto l q v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl
  iintro %σ₁ Hσ
  icases heapPointsto_na_acc l q v $$ Hl with ⟨Hl, Hl_rest⟩
  icases na_heap_read tls σ₁.1.heap l q v $$ Hσ Hl with %⟨lk, n, Hlookup, -⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, [], BaseStep.CheckCellS l σ₁ (by rw [Hlookup]; rfl)⟩
  inext
  iintro %κ %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨l', Hl', -, rfl, rfl, rfl, rfl⟩ := baseStep_CheckCell_inv Hstep
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [Hσ]
  · iexists _; iframe Hσ; ipureintro; rfl
  iexists #()
  isplit
  · ipureintro; rfl
  iapply HΦ
  iapply Hl_rest $$ Hl

end enc_wps

end Perennial
