/-
Program-logic base for GooseLang. Port of `src/goose_lang/lifting.v`, without
the crash machinery.

Differences from the Rocq version:
* No crash logic: no `wpc`, `crash_borrow`, crash generations, `cred_*` credit
  tokens or `pinv_tok`. iris-lean's `wp` (with its own later credits) is used.
* iris-lean has a single `IrisGS_gen` class; it is instantiated
  (`goose_irisGS`) from `gooseGlobalGS` and `gooseLocalGS`. `heapGS` bundles the
  two. `heapGS` does *not* contain the `GoGlobalContext` (the language instance
  itself depends on it, so it must be a separate instance argument), nor the
  `New.ghost` `allG` ghost state.
* `numLatersPerStep` is `0` (Rocq: `3^(n+1)`). Every step still yields one
  later credit (`£ 1`).
* (Lean addition) The language instance is the step-bounded layer of
  `BoundedLang.lean`, whose state is `BcfgState = CfgState × Nat` (the `Nat`
  is the fuel `f`); the state interpretation (`gooseBstateInterp`) adds the
  authoritative counter of time receipts for that fuel (`receiptFuel f`, i.e.
  `receiptAuth (N - (f + 1))` for the bound `N = receiptBound GF` of the
  receipt ghost state, `Receipts.lean`) to `gooseStateInterp`. The
  lifting lemmas `goose_wp_lift_*` restate iris-lean's for the real `base_step`
  and `gooseStateInterp` (as `gooseCfgInterp`); Go instructions, the only
  counted steps, have their own lemma `wp_GoInstruction_receipt`, which handles
  the stutter by Löb induction and hands out a time receipt.
* The state interpretation is that of Rocq's `goose_generationGS` (`naHeapCtx`,
  `ffiLocalCtx`, `ownGoStateCtx`, `goLctx` equality) plus the global part
  (`ffiGlobalCtx`, iris-lean's prophecy map `prophMapInterp`).
* `Alloc` allocates a single cell, so `wp_allocN_seq` gives `pointstoVals l
  (.own 1) [v]`; the `na_block_size`/`meta_token` parts of
  `wp_allocN_seq_sized_meta` are dropped along with that ghost state.
-/
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Perennial.ProgramLogic.EctxLifting
import Iris.BI.Lib.ProphMap
import Iris.Instances.Lib.GhostVar
import Iris.Std.GenSets
import Perennial.Algebra.NaHeap
import Perennial.GooseLang.Lang
import Perennial.GooseLang.BoundedLang
import Perennial.GooseLang.Receipts

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
variable [ext : ffi_syntax] {GF : BundledGFunctors} [hG : NaHeapGS loc val GF]

/-- Rocq `heapPointsto`: a non-null location with a non-atomic points-to. -/
def heapPointsto (l : loc) (dq : DFrac) (v : val) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ naHeapPointsto l dq v)

end definitions

/- `l ↦{dq} v`, `l ↦ v` and `l ↦□ v` for `heapPointsto`. Rocq makes these
notations local to `lifting.v`; here they are scoped to `goose_heap`. -/
namespace goose_heap
scoped notation:50 l:50 " ↦{" dq "} " v:50 => heapPointsto l dq v
scoped notation:50 l:50 " ↦ " v:50 => heapPointsto l (DFrac.own 1) v
scoped notation:50 l:50 " ↦□ " v:50 => heapPointsto l DFrac.discard v
end goose_heap

open goose_heap

section heapPointsto
variable [ext : ffi_syntax] {GF : BundledGFunctors} [hG : NaHeapGS loc val GF]
open ProofMode

instance heapPointsto_persistent (l : loc) (v : val) :
    Persistent (heapPointsto (hG := hG) l .discard v) := by
  unfold heapPointsto; infer_instance

instance heapPointsto_timeless (l : loc) (dq : DFrac) (v : val) :
    Timeless (heapPointsto (hG := hG) l dq v) := by
  unfold heapPointsto; infer_instance

theorem heapPointsto_persist (l : loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ |==> heapPointsto l .discard v := by
  unfold heapPointsto
  iintro ⟨%Ha, Hb⟩
  imod naHeapPointsto_persist l dq v $$ Hb with Hb
  imodintro
  iframe Hb
  ipureintro; exact Ha

instance heapPointsto_dfractional (l : loc) (v : val) :
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

instance heapPointsto_as_dfractional (l : loc) (dq : DFrac) (v : val) :
    AsDFractional (heapPointsto (hG := hG) l dq v) (fun dq => heapPointsto l dq v) dq :=
  ⟨.rfl, heapPointsto_dfractional l v⟩

instance heapPointsto_fractional (l : loc) (v : val) :
    Fractional (fun q => heapPointsto (hG := hG) l (.own q) v) :=
  fractional_of_dfractional (fun dq => heapPointsto l dq v)

instance heapPointsto_as_fractional (l : loc) (q : Qp) (v : val) :
    AsFractional (heapPointsto (hG := hG) l (.own q) v) ioΦ
      (fun q => heapPointsto l (.own q) v) ioq q :=
  ⟨.rfl, heapPointsto_fractional l v⟩

instance heapPointsto_combine_sep_gives (l : loc) (dq1 dq2 : DFrac) (v1 v2 : val) :
    CombineSepGives (heapPointsto (hG := hG) l dq1 v1) (heapPointsto l dq2 v2)
      iprop(⌜✓ (dq1 • dq2) ∧ v1 = v2⌝) where
  combine_sep_gives := by
    unfold heapPointsto
    iintro ⟨⟨_, H1⟩, ⟨_, H2⟩⟩
    icombine H1 H2 gives %H
    imodintro; ipureintro; exact H

theorem heapPointsto_agree (l : loc) (dq1 dq2 : DFrac) (v1 v2 : val) :
    heapPointsto (hG := hG) l dq1 v1 ∗ heapPointsto l dq2 v2 ⊢ ⌜v1 = v2⌝ := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨_, H⟩
  ipureintro; exact H

theorem na_pointsto_to_heap (l : loc) (dq : DFrac) (v : val) (H : l ≠ null) :
    naHeapPointsto (hG := hG) l dq v ⊢ heapPointsto l dq v := by
  unfold heapPointsto
  iintro Hl
  iframe Hl
  ipureintro; exact H

theorem heapPointsto_na_acc (l : loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢
      naHeapPointsto l dq v ∗ (∀ v', naHeapPointsto l dq v' -∗ heapPointsto l dq v') := by
  unfold heapPointsto
  iintro ⟨%Hl, H⟩
  iframe H
  iintro %v' H'
  iframe H'
  ipureintro; exact Hl

theorem heapPointsto_valid (l : loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜✓ dq⌝ := by
  unfold heapPointsto
  iintro ⟨_, H⟩
  iapply naHeapPointsto_valid $$ H

theorem heapPointsto_frac_valid (l : loc) (q : Qp) (v : val) :
    heapPointsto (hG := hG) l (.own q) v ⊢ ⌜q.val ≤ 1⌝ :=
  heapPointsto_valid l (.own q) v

theorem heapPointsto_non_null (l : loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜l ≠ null⌝ := by
  unfold heapPointsto
  iintro ⟨%Hl, _⟩
  ipureintro; exact Hl

end heapPointsto

/-! ## Package-initialization state -/

section go_state_definitions

class GoStateGS (GF : BundledGFunctors) where
  package_inited_inG : GhostVarG GF (GMap go_string Bool)
  packageInitedName : GName

class GoStatePreG (GF : BundledGFunctors) where
  package_inited_preG_inG : GhostVarG GF (GMap go_string Bool)

attribute [reducible, instance] GoStateGS.package_inited_inG GoStatePreG.package_inited_preG_inG

abbrev goStateGSUpdatePre (GF : BundledGFunctors) (hT : GoStatePreG GF) (γ : GName) :
    GoStateGS GF :=
  ⟨hT.package_inited_preG_inG, γ⟩

abbrev goStateGSUpdate (GF : BundledGFunctors) (hT : GoStateGS GF) (γ : GName) :
    GoStateGS GF :=
  ⟨hT.package_inited_inG, γ⟩

variable {GF : BundledGFunctors}

def ownGoStateCtx [hG : GoStateGS GF] (package_inited : GMap go_string Bool) : IProp GF :=
  ghost_var hG.packageInitedName (.own (1 : Qp).half) package_inited

def ownGoState [hG : GoStateGS GF] (package_inited : GMap go_string Bool) : IProp GF :=
  ghost_var hG.packageInitedName (.own (1 : Qp).half) package_inited

instance ownGoStateCtx_combine_sep_gives [GoStateGS GF] (v1 v2 : GMap go_string Bool) :
    ProofMode.CombineSepGives (ownGoStateCtx (GF := GF) v1) (ownGoState v2)
      iprop(⌜v1 = v2⌝) where
  combine_sep_gives := by
    unfold ownGoStateCtx ownGoState
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %⟨_, H⟩
    imodintro; ipureintro; exact H

instance ownGoState_timeless [GoStateGS GF] (v : GMap go_string Bool) :
    Timeless (ownGoState (GF := GF) v) := by
  unfold ownGoState; infer_instance

theorem ownGoState_update [GoStateGS GF] (v v' v'' : GMap go_string Bool) :
    ⊢@{IProp GF} ownGoState v -∗ ownGoStateCtx v' ==∗
      ownGoState v'' ∗ ownGoStateCtx v'' := by
  unfold ownGoState ownGoStateCtx
  iintro H1 H2
  iapply ghost_var_update_halves $$ H1 H2

theorem goState_init (hT : GoStatePreG GF) (package_inited : GMap go_string Bool) :
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
(Rocq's `ffiGlobalStart`, `ffiLocalStart`, `ffi_restart` and
`ffi_crash_rel` are crash/adequacy machinery and are omitted.) -/
class ffi_interp (ffi : ffi_model) where
  ffiLocalGS : BundledGFunctors → Type
  ffiGlobalGS : BundledGFunctors → Type
  ffiGlobalCtx : ∀ {GF : BundledGFunctors}, ffiGlobalGS GF → ffi_global_state → IProp GF
  ffiLocalCtx : ∀ {GF : BundledGFunctors}, ffiLocalGS GF → ffi_state → IProp GF

export ffi_interp (ffiLocalGS ffiGlobalGS ffiGlobalCtx ffiLocalCtx)

section goose_lang
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]

/-- Global ghost state for GooseLang. -/
class GooseGlobalGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  /-- not an instance on purpose, to avoid diamonds with `IrisGS_gen` -/
  gooseInvGS : InvGS_gen hlc GF
  goose_prophGS : prophMapGS proph_id val GF (GMap proph_id)
  gooseFfiGlobalGS : @ffiGlobalGS ffi _ GF
  /-- (Lean addition) time receipts, tied to the step fuel of the bounded semantics;
  carries the time-receipt bound `receiptBound GF` -/
  goose_receiptGS : ReceiptGS GF

/-- Per-generation ("local") ghost state. -/
class GooseLocalGS (GF : BundledGFunctors) where
  gooseFfiLocalGS : @ffiLocalGS ffi _ GF
  goose_go_local_context : GoLocalContext
  goose_na_heapGS : NaHeapGS loc val GF
  goose_go_stateGS : GoStateGS GF

attribute [reducible, instance] GooseGlobalGS.goose_prophGS GooseGlobalGS.goose_receiptGS
  GooseLocalGS.goose_go_local_context
  GooseLocalGS.goose_na_heapGS GooseLocalGS.goose_go_stateGS

/-- Bundles the global and local ghost state (Rocq `heapGS`, minus `allG` and
`GoGlobalContext`). -/
class heapGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  goose_globalGS : GooseGlobalGS hlc GF
  goose_localGS : GooseLocalGS GF

attribute [reducible, instance] heapGS.goose_globalGS heapGS.goose_localGS

export GooseGlobalGS (gooseInvGS gooseFfiGlobalGS)
export GooseLocalGS (gooseFfiLocalGS goose_go_local_context)

/-- The lock state of a `naMode`. -/
def tls : NaMode → LockState
  | Writing => WSt
  | Reading n => RSt n

@[simp] theorem tls_Writing : tls Writing = WSt := rfl
@[simp] theorem tls_Reading (n : Nat) : tls (Reading n) = RSt n := rfl

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The GooseLang state interpretation (Rocq `goose_generationGS.state_interp`
together with the non-crash parts of `goose_irisGS.global_state_interp`). -/
def gooseStateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : CfgState) (κs : List Observation) : IProp GF :=
  iprop(naHeapCtx tls σ.1.heap ∗
    ffiLocalCtx L.gooseFfiLocalGS σ.1.world ∗
    ownGoStateCtx σ.1.goState.packageState ∗
    ⌜σ.1.goState.goLctx = L.goose_go_local_context⌝ ∗
    ffiGlobalCtx G.gooseFfiGlobalGS σ.2.globalWorld ∗
    prophMapInterp κs σ.2.usedProphId)

/-- The state interpretation of the bounded language: `gooseStateInterp` of
the real configuration and the authoritative receipt counter for the fuel
(Lean addition). -/
def gooseBstateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : BcfgState) (κs : List Observation) : IProp GF :=
  iprop(gooseStateInterp σ.1 κs ∗ receiptFuel σ.2)

instance goose_stateInterp [GooseGlobalGS hlc GF] [GooseLocalGS GF] :
    StateInterp BcfgState Observation GF where
  stateInterp σ _ κs _ := gooseBstateInterp σ κs

variable [ffi_semantics ext ffi] [GoGlobalContext]

instance goose_irisGS [G : GooseGlobalGS hlc GF] [GooseLocalGS GF] : IrisGS_gen hlc expr GF where
  invGS := G.gooseInvGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := G.gooseInvGS
    iintro $

end goose_lang

/-! ## Atomicity -/

section atomic
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

open EctxLanguage in
/-- Atomicity from the real base step. Counted redexes (Go instructions) may
stutter in the bounded semantics and are not atomic, hence `hnc`. -/
theorem goose_atomic {e : expr} (a : Language.Atomicity)
    (h : ∀ σ κ e' σ' efs, BaseStep e σ κ e' σ' efs → (toVal e').isSome)
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome)
    (hnc : isCounted e = false := by rfl) :
    Language.Atomic a e :=
  Language.stronglyAtomic_atomic
    (Atomic.ofBaseAtomic _ (fun σ obs e' σ' efs hs => by
        obtain ⟨_, _, hs⟩ := (boundedBaseStep_uncounted (σ := σ.1) (f := σ.2) hnc).1 hs
        exact h _ obs e' _ efs hs)
      (EctxItemLanguage.subredexes_are_values hsub))

/-- Discharges the `hsub` side condition of `goose_atomic`. -/
local macro "solve_sub_redexes" : tactic =>
  `(tactic| (intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl))

instance alloc_atomic (a : Language.Atomicity) (v : val) : Language.Atomic a (Alloc (Val v)) :=
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

instance fork_atomic (a : Language.Atomicity) (e : expr) : Language.Atomic a (Fork e) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

instance resolve_atomic (a : Language.Atomicity) (p w : val) :
    Language.Atomic a (ResolveProph (Val p) (Val w)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

end atomic

/-! ## Pure steps

iris-lean provides `PureExec` and `wp_pure_step_later`/`wp_pure_step_fupd`.
`pureExec_of_base_step` builds a one-step `PureExec` from the base step relation. -/

section pure
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

open EctxLanguage in
/-- A one-step `PureExec` from the real base step relation (for an uncounted
redex, which steps in the bounded semantics exactly as in the real one). -/
theorem pureExec_of_base_step {φ : Prop} {e₁ e₂ : expr}
    (Hsafe : φ → ∀ σ, BaseStep e₁ σ [] e₂ σ [])
    (Hdet : φ → ∀ σ κ e' σ' efs, BaseStep e₁ σ κ e' σ' efs →
      κ = [] ∧ σ' = σ ∧ e' = e₂ ∧ efs = [])
    (hnc : isCounted e₁ = false := by rfl) :
    Language.PureExec φ 1 e₁ e₂ where
  pureExec hφ := by
    refine .tail e₁ (.rfl _) (purePrimStep_of_pureBaseStep
      ⟨fun σ => ⟨_, _, _, BoundedBaseStep.step (f := σ.2) hnc (Hsafe hφ σ.1)⟩, ?_⟩)
    intro σ₁ σ₂ obs e₂' eₜ h
    obtain ⟨σ', rfl, h'⟩ := (boundedBaseStep_uncounted (σ := σ₁.1) (f := σ₁.2) hnc).1 h
    obtain ⟨h1, h2, h3, h4⟩ := Hdet hφ _ _ _ _ _ h'
    subst h2
    exact ⟨h1, rfl, h3.symm, h4⟩

instance pure_recc (f x : binder) (e : expr) :
    Language.PureExec True 1 (Rec f x e) (Val (RecV f x e)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.RecS f x e σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_pairc (v1 v2 : val) :
    Language.PureExec True 1 (Pair (Val v1) (Val v2)) (Val (PairV v1 v2)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.PairS v1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_beta (f x : binder) (e1 : expr) (v2 : val) :
    Language.PureExec True 1 (App (Val (RecV f x e1)) (Val v2))
      (subst' x v2 (subst' f (RecV f x e1) e1)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.BetaS f x e1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem baseStep_If_inv {v : val} {e1 e2 : expr} {σ σ' : CfgState} {κ : List Observation}
    {e' : expr} {efs : List expr} (h : BaseStep (If (Val v) e1 e2) σ κ e' σ' efs) :
    κ = [] ∧ σ' = σ ∧ efs = [] ∧ ((v = #true ∧ e' = e1) ∨ (v = #false ∧ e' = e2)) := by
  cases h
  · exact ⟨rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, .inr ⟨rfl, rfl⟩⟩

instance pure_if_true (e1 e2 : expr) : Language.PureExec True 1 (If (Val #true) e1 e2) e1 :=
  pureExec_of_base_step (fun _ σ => BaseStep.IfTrueS e1 e2 σ) fun _ _ _ _ _ _ h => by
    obtain ⟨h1, h2, h3, ⟨_, h4⟩ | ⟨hv, _⟩⟩ := baseStep_If_inv h
    · exact ⟨h1, h2, h4, h3⟩
    · exact absurd (GoGlobalContext.intoVal_inj_bool hv) (by decide)

instance pure_if_false (e1 e2 : expr) : Language.PureExec True 1 (If (Val #false) e1 e2) e2 :=
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

instance pure_select_stmt_clauses (d : Option expr) (cs : List comm_clause) :
    Language.PureExec True 1 (SelectStmtClauses d cs) (Val (SelectStmtClausesV d cs)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.SelectStmtClausesS d cs σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

end pure

/-! ## Inversion lemmas for `base_step` -/

section inversion
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]
variable {σ σ' : CfgState} {κ : List Observation} {e' : expr} {efs : List expr}

theorem baseStep_ArbitraryInt_inv (h : BaseStep ArbitraryInt σ κ e' σ' efs) :
    ∃ x : w64, κ = [] ∧ e' = Val #x ∧ σ' = σ ∧ efs = [] := by
  cases h; exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem baseStep_Fork_inv {e : expr} (h : BaseStep (Fork e) σ κ e' σ' efs) :
    κ = [] ∧ e' = Val #() ∧ σ' = σ ∧ efs = [e] := by
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

theorem baseStep_GoInstruction_inv {op : go_instruction} {arg : val}
    (h : BaseStep (App (Val (GoInstruction op)) (Val arg)) σ κ e' σ' efs) :
    ∃ s', @IsGoStep _ _ σ.1.goState.goLctx op arg e' σ.1.goState.packageState s' ∧
      κ = [] ∧ efs = [] ∧
      σ' = ({ σ.1 with goState := { σ.1.goState with packageState := s' } }, σ.2) := by
  cases h; exact ⟨_, ‹_›, rfl, rfl, rfl⟩

end inversion

/-! ## Lifting lemmas -/

section lifting
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open EctxLanguage ProofMode

/-- Real base reducibility. -/
def GooseBaseReducible (e : expr) (σ : CfgState) : Prop :=
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

theorem goose_bstateInterp_eq (σ : CfgState) (c : Nat) (ns : Nat) (κs : List Observation)
    (nt : Nat) :
    stateInterp (GF := GF) ((σ, c) : BcfgState) ns κs nt ⊣⊢
      iprop(gooseCfgInterp σ ns κs nt ∗ receiptFuel c) := .rfl

theorem goose_baseReducible_of {e : expr} {σ : CfgState} {c : Nat} (hnc : isCounted e = false)
    (h : GooseBaseReducible e σ) : BaseStep.Reducible (e, ((σ, c) : BcfgState)) := by
  obtain ⟨κ, e', σ', efs, h⟩ := h
  exact ⟨κ, e', (σ', c), efs, .step hnc h⟩

/-- iris-lean's `wp_lift_base_step` for an uncounted redex, in terms of the real
`base_step` and `gooseStateInterp`. -/
theorem goose_wp_lift_base_step {e₁ : expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : isCounted e₁ = false) :
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
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_uncounted hnc).1 Hstep
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hwp Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step` for an uncounted redex. -/
theorem goose_wp_lift_atomic_base_step {e₁ : expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : isCounted e₁ = false) :
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
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_uncounted hnc).1 Hstep
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, HΦ, Hefs⟩
  imodintro
  iframe HΦ Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step_no_fork` for an uncounted redex. -/
theorem goose_wp_lift_atomic_base_step_no_fork {e₁ : expr} {Φ : val → IProp GF}
    (h : toVal e₁ = none) (hnc : isCounted e₁ = false) :
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
theorem wp_lift_atomic_heap_step {e₁ : expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : isCounted e₁ = false) :
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

theorem wp_panic (msg : String) (Φ : val → IProp GF) :
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

theorem wp_load (l : loc) (q : DFrac) (v : val) :
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

theorem wp_prepare_write (l : loc) (v : val) :
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

theorem wp_finish_store (l : loc) (v v' : val) :
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

/-- Rocq's read-lock function for `naMode`. -/
def naModeRl : NaMode → NaMode
  | Reading n => Reading (n + 1)
  | m => m

def naModeUrl : NaMode → NaMode
  | Reading (n + 1) => Reading n
  | m => m

theorem naModeRl_is_read_lock : IsReadLock tls naModeRl := by
  intro lk n h; cases lk <;> simp_all [tls, naModeRl]

theorem naModeUrl_is_read_unlock : IsReadUnlock tls naModeUrl := by
  intro lk n h; cases lk <;> simp_all [tls, naModeUrl]

theorem wp_start_read (l : loc) (q : DFrac) (v : val) :
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

theorem wp_finish_read (l : loc) (q : DFrac) (v : val) :
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

theorem wp_atomic_swap (l : loc) (v0 v : val) :
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

theorem wp_atomic_add (l : loc) (v0 v1 v : val) (Hev : atomicAddEval v0 v1 = some v) :
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

theorem wp_cmpxchg_fail (l : loc) (q : DFrac) (v' v1 v2 : val) (Hne : v' ≠ v1) :
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

theorem wp_cmpxchg_suc (l : loc) (v1 v2 v' : val) (Heq : v' = v1) :
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

theorem exists_isFresh (σ : CfgState) : ∃ l, IsFresh σ l := by
  refine ⟨freshLocs σ.1.heap.domList, fun i => ⟨freshLocs_non_null _ i, ?_⟩, freshLocs_off_0 _⟩
  cases h : σ.1.heap !! (freshLocs σ.1.heap.domList +ₗ i) with
  | none => rfl
  | some _ =>
    exact absurd ((GMap.mem_dom_list σ.1.heap _).mpr (by rw [h]; rfl)) (freshLocs_fresh _ i)

/-- Rocq `pointstoVals`. -/
def pointstoVals (l : loc) (q : DFrac) (vs : List val) : IProp GF :=
  [∗list] j ↦ vj ∈ vs, heapPointsto (l +ₗ (j : Int)) q vj

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
  have Hnn : l ≠ null := by simpa using (Hfresh.1 0).1
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

/-! ### Fork -/

theorem wp_fork (e : expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ _v, True }} -∗ ▷ Φ #() -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply goose_wp_lift_atomic_base_step rfl rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, _, BaseStep.ForkS e σ₁⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨rfl, rfl, rfl, rfl⟩ := baseStep_Fork_inv Hstep
  simp only [List.nil_append]
  imodintro
  isplitl [Hσ]
  · iapply (goose_stateInterp_eq _ _ _ _).2
    iapply (goose_stateInterp_eq _ _ _ _).1 $$ Hσ
  isplitl [HΦ]
  · iexists #()
    isplit
    · ipureintro; rfl
    · iexact HΦ
  iapply BigSepL.bigSepL_singleton.2
  iexact He

/-! ### Go instructions -/

/-- WP for go instructions, with time receipts (Lean addition). Go instructions
are the counted steps of the bounded semantics: below the bound the step yields
an exclusive receipt `⧗ 1` and increments a persistent receipt `⧖ m` (the
paper's `{⧖ m} tick v {⧗ 1 ∗ ⧖ (m + 1)}`); at the bound the step stutters,
which is handled by Löb induction. -/
theorem wp_GoInstruction_preceipt (K : List EctxItem) (op : go_instruction) (arg : val)
    (Φ : val → IProp GF) (m : Nat) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s') :
    ⧖ m ∗ ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ⧗ 1 -∗ ⧖ (m + 1) -∗ ownGoStateCtx gs ={E}=∗
          ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro ⟨#Hm, HΦ⟩
  iapply wp_lift_step (EctxLanguage.fill_not_val K _ rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc⟩
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  obtain ⟨e', s', h⟩ := Hok σ₁.1.goState.packageState
  have Hreal := BaseStep.GoInstructionS op arg e' s' σ₁ (Hlctx ▸ h)
  have Hred : BaseStep.Reducible (App (Val (GoInstruction op)) (Val arg), ((σ₁, c) : BcfgState)) := by
    cases c with
    | zero => exact ⟨[], _, (σ₁, 0), [], .stutter rfl Hreal⟩
    | succ c => exact ⟨[], e', (_, c), [], .tick rfl Hreal⟩
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
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc
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
    isplitl [Hheap Hffi Hgs Hgffi Hproph Hc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc
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
theorem wp_GoInstruction_receipt (K : List EctxItem) (op : go_instruction) (arg : val)
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
theorem wp_GoInstruction (K : List EctxItem) (op : go_instruction) (arg : val)
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
theorem wp_GoInstruction' (op : go_instruction) (arg : val)
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

end Perennial
