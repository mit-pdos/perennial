/-
Program-logic base for GooseLang.

Notes:
* The program logic is iris-lean's `wp` (with its own later credits); there is
  no crash WP. The ghost state is split into the global part (`GooseGlobalGS`)
  and the per-generation part (`GooseLocalGS`), which a crash replaces
  (`CrashAdequacy.lean`); the bounded state interpretation owns the
  generation's `notCrashed` (`CrashToken.lean`).
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
  plain redexes that do not unwind a panic (`Unwinds`; the panic steps are
  `pure_unwind`, `wp_unwind` and `wp_catch`, section "Panics"); Go instructions, the only counted steps, have their own lemma
  `wp_GoInstruction_receipt`, which handles the stutter by Löb induction and
  hands out a time receipt; `Fork` (`wp_fork_tok`, likewise by Löb induction)
  hands out a thread token and `ThreadExit` (`wp_ThreadExit`) takes one back.
* The state interpretation consists of a local part (`naHeapCtx`, the
  extensions' `Exts.localCtx`, `ownGoStateCtx`, `goLctx` equality) plus the
  global part (`Exts.globalCtx`, iris-lean's prophecy map `prophMapInterp`).
* Each extension (`Ext.lean`) has its ghost state (`ExtInterp`); `HasExt E`
  says that the program's extensions include `E` with its semantics and ghost
  state, and `wp_extStep` lifts a step of `E`'s operations to a WP, with
  access to the heap and `E`'s state only.
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
public import Perennial.GooseLang.CrashToken

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
variable [GooseExts] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]

/-- A non-null location with a non-atomic points-to. -/
def heapPointsto (l : Loc) (dq : DFrac) (v : val) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ naHeapPointsto l dq v)

end definitions

/- `l ↦{dq} v`, `l ↦ v` and `l ↦□ v` for `heapPointsto`, scoped to `goose_heap`. -/
namespace goose_heap
scoped notation:50 l:50 " ↦{" dq "} " v:50 => heapPointsto l dq v
scoped notation:50 l:50 " ↦ " v:50 => heapPointsto l (DFrac.own 1) v
scoped notation:50 l:50 " ↦□ " v:50 => heapPointsto l DFrac.discard v
end goose_heap

open goose_heap

section heapPointsto
variable [GooseExts] {GF : BundledGFunctors} [hG : NaHeapGS Loc val GF]
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

theorem na_pointsto_to_heap (l : Loc) (dq : DFrac) (v : val) (H : l ≠ null) :
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

theorem heapPointsto_non_null (l : Loc) (dq : DFrac) (v : val) :
    heapPointsto (hG := hG) l dq v ⊢ ⌜l ≠ null⌝ := by
  unfold heapPointsto
  iintro ⟨%Hl, _⟩
  ipureintro; exact Hl

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

/-! ## The ghost state of extensions -/

/-- The ghost state of the extension `E`: `LocalGS`/`GlobalGS` bundle the CMRAs
and ghost names it uses, and `localCtx`/`globalCtx` interpret its states in the
state interpretation. For adequacy, it says how to allocate them (from `PreG`)
for initial states satisfying `initP`/`initgP`, handing the program the start
resources `localStart`/`globalStart`. -/
class ExtInterp (E : GooseExt) where
  LocalGS : BundledGFunctors → Type
  GlobalGS : BundledGFunctors → Type
  localCtx : ∀ {GF : BundledGFunctors}, LocalGS GF → E.LocalState → IProp GF
  globalCtx : ∀ {GF : BundledGFunctors}, GlobalGS GF → E.GlobalState → IProp GF
  /-- The ghost state that the adequacy theorem must provide (in `GooseGpreS`). -/
  PreG : BundledGFunctors → Type
  initgP : E.GlobalState → Prop
  /-- Valid local starting states may depend on the global state. -/
  initP : E.LocalState → E.GlobalState → Prop
  /-- Resources handed to the program for the initial global state. -/
  globalStart : ∀ {GF : BundledGFunctors}, GlobalGS GF → E.GlobalState → IProp GF
  /-- Resources handed to the program for the initial local state. -/
  localStart : ∀ {GF : BundledGFunctors}, LocalGS GF → E.LocalState → IProp GF
  global_init : ∀ (GF : BundledGFunctors) (_hPre : PreG GF) (g : E.GlobalState), initgP g →
    ⊢@{IProp GF} |==> ∃ hG : GlobalGS GF, globalCtx hG g ∗ globalStart hG g
  local_init : ∀ (GF : BundledGFunctors) (_hPre : PreG GF) (σ : E.LocalState)
    (g : E.GlobalState), initP σ g →
    ⊢@{IProp GF} |==> ∃ hL : LocalGS GF, localCtx hL σ ∗ localStart hL σ

/-- The ghost state of the extensions of the program: one `ExtInterp` for each. -/
class GooseInterp [GooseExts] where
  interps : ExtTuple ExtInterp exts

/-! ### The ghost state of a list of extensions

The ghost state of a list `l` of extensions with ghost states `Is`: the products
of their ghost states, the separating conjunctions of their interpretations and
start resources, the conjunctions of their initial-state conditions. -/

namespace Exts
variable {GF : BundledGFunctors}

def LocalGS : (l : List GooseExt) → ExtTuple ExtInterp l → BundledGFunctors → Type
  | [], _, _ => PUnit
  | _ :: l, Is, GF => Is.1.LocalGS GF × LocalGS l Is.2 GF

def GlobalGS : (l : List GooseExt) → ExtTuple ExtInterp l → BundledGFunctors → Type
  | [], _, _ => PUnit
  | _ :: l, Is, GF => Is.1.GlobalGS GF × GlobalGS l Is.2 GF

def PreG : (l : List GooseExt) → ExtTuple ExtInterp l → BundledGFunctors → Type
  | [], _, _ => PUnit
  | _ :: l, Is, GF => Is.1.PreG GF × PreG l Is.2 GF

def localCtx : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) → LocalGS l Is GF →
    ExtsLocalState l → IProp GF
  | [], _, _, _ => iprop(emp)
  | _ :: l, Is, gs, w => iprop(Is.1.localCtx gs.1 w.1 ∗ localCtx l Is.2 gs.2 w.2)

def globalCtx : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) → GlobalGS l Is GF →
    ExtsGlobalState l → IProp GF
  | [], _, _, _ => iprop(emp)
  | _ :: l, Is, gs, w => iprop(Is.1.globalCtx gs.1 w.1 ∗ globalCtx l Is.2 gs.2 w.2)

def localStart : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) → LocalGS l Is GF →
    ExtsLocalState l → IProp GF
  | [], _, _, _ => iprop(emp)
  | _ :: l, Is, gs, w => iprop(Is.1.localStart gs.1 w.1 ∗ localStart l Is.2 gs.2 w.2)

def globalStart : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) → GlobalGS l Is GF →
    ExtsGlobalState l → IProp GF
  | [], _, _, _ => iprop(emp)
  | _ :: l, Is, gs, w => iprop(Is.1.globalStart gs.1 w.1 ∗ globalStart l Is.2 gs.2 w.2)

def initgP : (l : List GooseExt) → ExtTuple ExtInterp l → ExtsGlobalState l → Prop
  | [], _, _ => True
  | _ :: l, Is, g => Is.1.initgP g.1 ∧ initgP l Is.2 g.2

def initP : (l : List GooseExt) → ExtTuple ExtInterp l → ExtsLocalState l →
    ExtsGlobalState l → Prop
  | [], _, _, _ => True
  | _ :: l, Is, σ, g => Is.1.initP σ.1 g.1 ∧ initP l Is.2 σ.2 g.2

open ProofMode in
theorem global_init : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) →
    (hPre : PreG l Is GF) → (g : ExtsGlobalState l) → initgP l Is g →
    ⊢@{IProp GF} |==> ∃ hG : GlobalGS l Is GF, globalCtx l Is hG g ∗ globalStart l Is hG g
  | [], _, _, _, _ => by
    iapply bupd_intro; iexists PUnit.unit; dsimp only [globalCtx, globalStart]
    isplitl [] <;> iempintro
  | _ :: l, Is, hPre, g, ⟨h1, h2⟩ => by
    imod Is.1.global_init GF hPre.1 g.1 h1 with ⟨%hG1, Hc1, Hs1⟩
    imod global_init l Is.2 hPre.2 g.2 h2 with ⟨%hG2, Hc2, Hs2⟩
    imodintro
    iexists ((hG1, hG2) : GlobalGS (_ :: l) Is GF)
    dsimp only [globalCtx, globalStart]
    isplitl [Hc1 Hc2]
    · isplitl [Hc1] <;> iassumption
    · isplitl [Hs1] <;> iassumption

open ProofMode in
theorem local_init : (l : List GooseExt) → (Is : ExtTuple ExtInterp l) →
    (hPre : PreG l Is GF) → (σ : ExtsLocalState l) → (g : ExtsGlobalState l) →
    initP l Is σ g →
    ⊢@{IProp GF} |==> ∃ hL : LocalGS l Is GF, localCtx l Is hL σ ∗ localStart l Is hL σ
  | [], _, _, _, _, _ => by
    iapply bupd_intro; iexists PUnit.unit; dsimp only [localCtx, localStart]
    isplitl [] <;> iempintro
  | _ :: l, Is, hPre, σ, g, ⟨h1, h2⟩ => by
    imod Is.1.local_init GF hPre.1 σ.1 g.1 h1 with ⟨%hL1, Hc1, Hs1⟩
    imod local_init l Is.2 hPre.2 σ.2 g.2 h2 with ⟨%hL2, Hc2, Hs2⟩
    imodintro
    iexists ((hL1, hL2) : LocalGS (_ :: l) Is GF)
    dsimp only [localCtx, localStart]
    isplitl [Hc1 Hc2]
    · isplitl [Hc1] <;> iassumption
    · isplitl [Hs1] <;> iassumption

end Exts

namespace ExtIn
variable {E : GooseExt} {GF : BundledGFunctors}

/-- The local ghost state of the extension at position `m`. -/
def localGS : {l : List GooseExt} → (m : ExtIn E l) → {Is : ExtTuple ExtInterp l} →
    Exts.LocalGS l Is GF → (m.get Is).LocalGS GF
  | _ :: _, .here, _, gs => gs.1
  | _ :: _, .there m, _, gs => m.localGS gs.2

/-- The global ghost state of the extension at position `m`. -/
def globalGS : {l : List GooseExt} → (m : ExtIn E l) → {Is : ExtTuple ExtInterp l} →
    Exts.GlobalGS l Is GF → (m.get Is).GlobalGS GF
  | _ :: _, .here, _, gs => gs.1
  | _ :: _, .there m, _, gs => m.globalGS gs.2

open ProofMode in
/-- Take out the interpretation of the local state of the extension at position
`m`, to put back that of a new state. -/
theorem localCtx_acc {l : List GooseExt} (m : ExtIn E l) (Is : ExtTuple ExtInterp l)
    (gs : Exts.LocalGS l Is GF) (w : ExtsLocalState l) :
    Exts.localCtx l Is gs w ⊢ (m.get Is).localCtx (m.localGS gs) (m.get w) ∗
      ∀ x, (m.get Is).localCtx (m.localGS gs) x -∗ Exts.localCtx l Is gs (m.set w x) := by
  induction m with
  | here =>
    show iprop(Is.1.localCtx gs.1 w.1 ∗ Exts.localCtx _ Is.2 gs.2 w.2) ⊢ Is.1.localCtx gs.1 w.1 ∗
      ∀ x, Is.1.localCtx gs.1 x -∗ iprop(Is.1.localCtx gs.1 x ∗ Exts.localCtx _ Is.2 gs.2 w.2)
    iintro ⟨H, Hr⟩
    isplitl [H]
    · iexact H
    iintro %x Hx
    isplitl [Hx] <;> iassumption
  | there m ih =>
    show iprop(Is.1.localCtx gs.1 w.1 ∗ Exts.localCtx _ Is.2 gs.2 w.2) ⊢ (m.get Is.2).localCtx (m.localGS gs.2) (m.get w.2) ∗
      ∀ x, (m.get Is.2).localCtx (m.localGS gs.2) x -∗
        iprop(Is.1.localCtx gs.1 w.1 ∗ Exts.localCtx _ Is.2 gs.2 (m.set w.2 x))
    iintro ⟨Hh, Hr⟩
    icases ih Is.2 gs.2 w.2 $$ Hr with ⟨H, Hclose⟩
    isplitl [H]
    · iexact H
    iintro %x Hx
    isplitl [Hh]
    · iexact Hh
    iapply Hclose $$ Hx

open ProofMode in
/-- Take out the interpretation of the global state of the extension at position
`m`, to put back that of a new state. -/
theorem globalCtx_acc {l : List GooseExt} (m : ExtIn E l) (Is : ExtTuple ExtInterp l)
    (gs : Exts.GlobalGS l Is GF) (w : ExtsGlobalState l) :
    Exts.globalCtx l Is gs w ⊢ (m.get Is).globalCtx (m.globalGS gs) (m.get w) ∗
      ∀ x, (m.get Is).globalCtx (m.globalGS gs) x -∗ Exts.globalCtx l Is gs (m.set w x) := by
  induction m with
  | here =>
    show iprop(Is.1.globalCtx gs.1 w.1 ∗ Exts.globalCtx _ Is.2 gs.2 w.2) ⊢ Is.1.globalCtx gs.1 w.1 ∗
      ∀ x, Is.1.globalCtx gs.1 x -∗ iprop(Is.1.globalCtx gs.1 x ∗ Exts.globalCtx _ Is.2 gs.2 w.2)
    iintro ⟨H, Hr⟩
    isplitl [H]
    · iexact H
    iintro %x Hx
    isplitl [Hx] <;> iassumption
  | there m ih =>
    show iprop(Is.1.globalCtx gs.1 w.1 ∗ Exts.globalCtx _ Is.2 gs.2 w.2) ⊢ (m.get Is.2).globalCtx (m.globalGS gs.2) (m.get w.2) ∗
      ∀ x, (m.get Is.2).globalCtx (m.globalGS gs.2) x -∗
        iprop(Is.1.globalCtx gs.1 w.1 ∗ Exts.globalCtx _ Is.2 gs.2 (m.set w.2 x))
    iintro ⟨Hh, Hr⟩
    icases ih Is.2 gs.2 w.2 $$ Hr with ⟨H, Hclose⟩
    isplitl [H]
    · iexact H
    iintro %x Hx
    isplitl [Hh]
    · iexact Hh
    iapply Hclose $$ Hx

end ExtIn

section goose_lang
variable [GooseExts] [GooseInterp]

/-- Global ghost state for GooseLang. -/
class GooseGlobalGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  /-- not an instance on purpose, to avoid diamonds with `IrisGS_gen` -/
  gooseInvGS : InvGS_gen hlc GF
  /-- The one `allG GF`: the ghost state of the thread tokens (`goose_threadGS`)
  and of every proof under `HeapGS`, which therefore does not assume its own
  `[AllG GF]` (`Ghost/All.lean`) -/
  gooseAllG : AllG GF
  goose_prophGS : prophMapGS proph_id val GF (GMap proph_id)
  /-- the global ghost state of the extensions -/
  gooseExtsGlobalGS : Exts.GlobalGS exts GooseInterp.interps GF
  /-- Time receipts, tied to the step fuel of the bounded semantics;
  carries the time-receipt bound `receiptBound GF`. Global: the step bound
  counts the steps of all generations. -/
  goose_receiptGS : ReceiptGS GF

/-- Per-generation ("local") ghost state: a crash (`CrashAdequacy.lean`)
replaces it by a new one. -/
class GooseLocalGS (GF : BundledGFunctors) where
  /-- the local ghost state of the extensions -/
  gooseExtsLocalGS : Exts.LocalGS exts GooseInterp.interps GF
  goose_go_local_context : GoLocalContext
  goose_na_heapGS : NaHeapGS Loc val GF
  goose_go_stateGS : GoStateGS GF
  /-- Thread tokens, tied to the thread fuel of the bounded semantics;
  carries the thread bound `threadBound GF`. Per generation: a crash kills
  every thread. -/
  goose_threadGS : ThreadGS GF
  /-- The generation's crash token (`notCrashed`, `crashed`) -/
  goose_crashGS : CrashGS GF

attribute [reducible, instance] GooseGlobalGS.gooseAllG GooseGlobalGS.goose_prophGS
  GooseGlobalGS.goose_receiptGS GooseLocalGS.goose_threadGS
  GooseLocalGS.goose_go_local_context
  GooseLocalGS.goose_na_heapGS GooseLocalGS.goose_go_stateGS GooseLocalGS.goose_crashGS

/-- Bundles the global and local ghost state (not including `GoGlobalContext`). -/
class HeapGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  goose_globalGS : GooseGlobalGS hlc GF
  goose_localGS : GooseLocalGS GF

attribute [reducible, instance] HeapGS.goose_globalGS HeapGS.goose_localGS

export GooseGlobalGS (gooseInvGS gooseExtsGlobalGS)
export GooseLocalGS (gooseExtsLocalGS goose_go_local_context)

variable {hlc : HasLC} {GF : BundledGFunctors} in
/-- The interpretation of the local states of the extensions. -/
abbrev extsLocalCtx [L : GooseLocalGS GF] (w : ExtsLocalState exts) : IProp GF :=
  Exts.localCtx exts GooseInterp.interps L.gooseExtsLocalGS w

variable {hlc : HasLC} {GF : BundledGFunctors} in
/-- The interpretation of the global states of the extensions. -/
abbrev extsGlobalCtx [G : GooseGlobalGS hlc GF] (w : ExtsGlobalState exts) : IProp GF :=
  Exts.globalCtx exts GooseInterp.interps G.gooseExtsGlobalGS w

/-- The lock state of a `naMode`. -/
def tls : NaMode → LockState
  | Writing => WSt
  | Reading n => RSt n

@[simp] theorem tls_Writing : tls Writing = WSt := rfl
@[simp] theorem tls_Reading (n : Nat) : tls (Reading n) = RSt n := rfl

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The GooseLang state interpretation: the per-generation part together with
the global part (global state of the extensions and prophecy map). -/
def gooseStateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : CfgState) (κs : List Observation) : IProp GF :=
  iprop(naHeapCtx tls σ.1.heap ∗
    extsLocalCtx σ.1.world ∗
    ownGoStateCtx σ.1.goState.packageState ∗
    ⌜σ.1.goState.goLctx = L.goose_go_local_context⌝ ∗
    extsGlobalCtx σ.2.globalWorld ∗
    prophMapInterp κs σ.2.usedProphId)

/-- The state interpretation of the bounded language: `gooseStateInterp` of
the real configuration, the authoritative receipt counter for the step fuel,
the thread tokens of the thread fuel and the generation's `notCrashed`. -/
def gooseBstateInterp [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
    (σ : BcfgState) (κs : List Observation) : IProp GF :=
  iprop(gooseStateInterp σ.1 κs ∗ receiptFuel σ.2.steps ∗ threadFuel σ.2.threads ∗ notCrashed)

instance goose_stateInterp [GooseGlobalGS hlc GF] [GooseLocalGS GF] :
    StateInterp BcfgState Observation GF where
  stateInterp σ _ κs _ := gooseBstateInterp σ κs

variable [GooseSemantics] [GoGlobalContext]

instance goose_irisGS [G : GooseGlobalGS hlc GF] [GooseLocalGS GF] : IrisGS_gen hlc Expr GF where
  invGS := G.gooseInvGS
  numLatersPerStep _ := 0
  forkPost v := iprop(⌜v.isPanic = false⌝)
  stateInterp_mono σ ns obs nt := by
    let := G.gooseInvGS
    iintro $

end goose_lang

/-! ## Membership of an extension, with its semantics and ghost state -/

/-- The extensions of the program include `E`, with its semantics `S` and its
ghost state `I` (iris's `ElemG`, for the semantics and the ghost state as well):
the assumption of code and proofs about `E`. -/
class HasExt [GooseExts] [GooseSemantics] [GooseInterp] (E : GooseExt) [S : ExtSemantics E]
    [I : ExtInterp E] extends ElemExt E where
  sem_eq : mem.get GooseSemantics.sems = S
  interp_eq : mem.get GooseInterp.interps = I

section has_ext
variable [GooseExts] [GooseSemantics] [GooseInterp] {X : GooseExt} [ExtSemantics X]
  [I : ExtInterp X] [hX : HasExt X] {hlc : HasLC} {GF : BundledGFunctors}

/-- The local ghost state of the extension `X`. -/
def extLocalGS (X : GooseExt) [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X]
    [L : GooseLocalGS GF] : I.LocalGS GF :=
  cast (congrArg (fun J : ExtInterp X => J.LocalGS GF) hX.interp_eq) (hX.mem.localGS L.gooseExtsLocalGS)

/-- The global ghost state of the extension `X`. -/
def extGlobalGS (X : GooseExt) [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X]
    [G : GooseGlobalGS hlc GF] : I.GlobalGS GF :=
  cast (congrArg (fun J : ExtInterp X => J.GlobalGS GF) hX.interp_eq) (hX.mem.globalGS G.gooseExtsGlobalGS)

theorem ExtInterp.localCtx_cast {J K : ExtInterp X} (h : J = K) (x : J.LocalGS GF)
    (σ : X.LocalState) :
    J.localCtx x σ = K.localCtx (cast (congrArg (fun J : ExtInterp X => J.LocalGS GF) h) x) σ := by
  subst h; rfl

theorem ExtInterp.globalCtx_cast {J K : ExtInterp X} (h : J = K) (x : J.GlobalGS GF)
    (g : X.GlobalState) :
    J.globalCtx x g = K.globalCtx (cast (congrArg (fun J : ExtInterp X => J.GlobalGS GF) h) x) g := by
  subst h; rfl

open ProofMode in
/-- Take out the interpretation of `X`'s local state, to put back that of a new state. -/
theorem HasExt.localCtx_acc [L : GooseLocalGS GF] (w : ExtsLocalState exts) :
    Exts.localCtx exts GooseInterp.interps L.gooseExtsLocalGS w ⊢
      I.localCtx (extLocalGS X) (hX.mem.get w) ∗
      ∀ x, I.localCtx (extLocalGS X) x -∗
        Exts.localCtx exts GooseInterp.interps L.gooseExtsLocalGS (hX.mem.set w x) := by
  have H := hX.mem.localCtx_acc GooseInterp.interps L.gooseExtsLocalGS w
  simp only [ExtInterp.localCtx_cast hX.interp_eq] at H
  exact H

open ProofMode in
/-- Take out the interpretation of `X`'s global state, to put back that of a new state. -/
theorem HasExt.globalCtx_acc [G : GooseGlobalGS hlc GF] (w : ExtsGlobalState exts) :
    Exts.globalCtx exts GooseInterp.interps G.gooseExtsGlobalGS w ⊢
      I.globalCtx (extGlobalGS X) (hX.mem.get w) ∗
      ∀ x, I.globalCtx (extGlobalGS X) x -∗
        Exts.globalCtx exts GooseInterp.interps G.gooseExtsGlobalGS (hX.mem.set w x) := by
  have H := hX.mem.globalCtx_acc GooseInterp.interps G.gooseExtsGlobalGS w
  simp only [ExtInterp.globalCtx_cast hX.interp_eq] at H
  exact H

/-- The step of `X`'s operations in the program is `X`'s step. -/
theorem HasExt.step_iff [GoGlobalContext] (o : X.Op) (v : val) (h : GMap Loc (NonAtomic val))
    (σ : X.LocalState) (g : X.GlobalState) (e' : Expr) (h' : GMap Loc (NonAtomic val))
    (σ' : X.LocalState) (g' : X.GlobalState) :
    @ExtSemantics.step X (hX.mem.get GooseSemantics.sems) _ ⟨hX.mem⟩ _ o v h σ g e' h' σ' g' ↔
      ExtSemantics.step o v h σ g e' h' σ' g' := by
  rw [hX.sem_eq]

end has_ext

/-! ## Atomicity -/

section atomic
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage in
/-- Atomicity from the real base step (an unwinding step ends in a value too).
Counted redexes (Go instructions) may stutter in the bounded semantics and are
not atomic, hence `hnc`. -/
theorem goose_atomic {e : Expr} (a : Language.Atomicity)
    (h : ∀ σ κ e' σ' efs, BaseStep e σ κ e' σ' efs → (toVal e').isSome)
    (hsub : ∀ Ki e', e = fillItem Ki e' → (toVal e').isSome)
    (hnc : redexKind e = .plain := by rfl) :
    Language.Atomic a e :=
  Language.stronglyAtomic_atomic
    (Atomic.ofBaseAtomic _ (fun σ obs e' σ' efs hs => by
        obtain ⟨_, _, hs⟩ := (boundedBaseStep_plain (σ := σ.1) (f := σ.2) hnc).1 hs
        cases hs with
        | unwind => rfl
        | base _ hs => exact h _ obs e' _ efs hs)
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

instance resolve_atomic (a : Language.Atomicity) (p w : val) :
    Language.Atomic a (ResolveProph (Val p) (Val w)) :=
  goose_atomic a (fun _ _ _ _ _ h => by cases h; rfl) (by solve_sub_redexes)

end atomic

/-! ## Pure steps

iris-lean provides `PureExec` and `wp_pure_step_later`/`wp_pure_step_fupd`.
`pureExec_of_base_step` builds a one-step `PureExec` from the base step relation. -/

section pure
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage in
/-- A one-step `PureExec` from the real base step relation (for a plain
redex that does not unwind, which steps in the bounded semantics exactly as in
the real one). -/
theorem pureExec_of_base_step {φ : Prop} {e₁ e₂ : Expr}
    (Hsafe : φ → ∀ σ, BaseStep e₁ σ [] e₂ σ [])
    (Hdet : φ → ∀ σ κ e' σ' efs, BaseStep e₁ σ κ e' σ' efs →
      κ = [] ∧ σ' = σ ∧ e' = e₂ ∧ efs = [])
    (hnc : redexKind e₁ = .plain := by rfl)
    (Hnu : φ → ∀ p, ¬ Unwinds e₁ p := by intro _; not_unwinds) :
    Language.PureExec φ 1 e₁ e₂ where
  pureExec hφ := by
    refine .tail e₁ (.rfl _) (purePrimStep_of_pureBaseStep
      ⟨fun σ => ⟨_, _, _, BoundedBaseStep.step (f := σ.2) hnc (.base (Hnu hφ) (Hsafe hφ σ.1))⟩,
        ?_⟩)
    intro σ₁ σ₂ obs e₂' eₜ h
    obtain ⟨σ', rfl, h'⟩ := (boundedBaseStep_plain (σ := σ₁.1) (f := σ₁.2) hnc).1 h
    rcases h' with ⟨hu⟩ | ⟨_, h'⟩
    · exact absurd hu (Hnu hφ _)
    obtain ⟨h1, h2, h3, h4⟩ := Hdet hφ _ _ _ _ _ h'
    subst h2
    exact ⟨h1, rfl, h3.symm, h4⟩

instance pure_recc (f x : Binder) (e : Expr) :
    Language.PureExec True 1 (Rec f x e) (Val (RecV f x e)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.RecS f x e σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_pairc (v1 v2 : val) :
    Language.PureExec (v1.isPanic = false ∧ v2.isPanic = false) 1 (Pair (Val v1) (Val v2))
      (Val (PairV v1 v2)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.PairS v1 v2 σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_beta (f x : Binder) (e1 : Expr) (v2 : val) :
    Language.PureExec (v2.isPanic = false) 1 (App (Val (RecV f x e1)) (Val v2))
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

instance pure_raise (v : val) :
    Language.PureExec (v.isPanic = false) 1 (Raise (Val v)) (Val (PanicV v)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.RaiseS v σ)
    (fun _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl, rfl, rfl⟩)

instance pure_catch_panic (p : val) (h k : Expr) :
    Language.PureExec True 1 (Catch (Val (PanicV p)) h k) (App h (Val p)) :=
  pureExec_of_base_step (fun _ σ => BaseStep.CatchPanicS p h k σ)
    (fun _ _ _ _ _ _ hs => by cases hs <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | simp_all)

instance pure_catch_val (v : val) (h k : Expr) :
    Language.PureExec (v.isPanic = false) 1 (Catch (Val v) h k) (App k (Val v)) :=
  pureExec_of_base_step (fun hv σ => BaseStep.CatchValS v h k σ hv)
    (fun hv _ _ _ _ _ hs => by cases hs <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | simp_all)

end pure

/-! ## Inversion lemmas for `base_step` -/

section inversion
variable [GooseExts] [GooseSemantics] [GoGlobalContext]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
        extsLocalCtx σ.1.world ∗
        ownGoStateCtx σ.1.goState.packageState ∗
        ⌜σ.1.goState.goLctx = L.goose_go_local_context⌝ ∗
        extsGlobalCtx σ.2.globalWorld ∗
        prophMapInterp κs σ.2.usedProphId) := .rfl

theorem goose_bstateInterp_eq (σ : CfgState) (c : Fuel) (ns : Nat) (κs : List Observation)
    (nt : Nat) :
    stateInterp (GF := GF) ((σ, c) : BcfgState) ns κs nt ⊣⊢
      iprop(gooseCfgInterp σ ns κs nt ∗ receiptFuel c.steps ∗ threadFuel c.threads ∗
        notCrashed) := .rfl

theorem goose_baseReducible_of {e : Expr} {σ : CfgState} {c : Fuel} (hnc : redexKind e = .plain)
    (hnu : ∀ p, ¬ Unwinds e p) (h : GooseBaseReducible e σ) :
    BaseStep.Reducible (e, ((σ, c) : BcfgState)) := by
  obtain ⟨κ, e', σ', efs, h⟩ := h
  exact ⟨κ, e', (σ', c), efs, .step hnc (.base hnu h)⟩

/-- A head step of a redex that does not unwind is a base step. -/
theorem baseStep_of_headStep {e : Expr} {σ : CfgState} {κ : List Observation} {e' : Expr}
    {σ' : CfgState} {efs : List Expr} (hnu : ∀ p, ¬ Unwinds e p)
    (h : HeadStep e σ κ e' σ' efs) : BaseStep e σ κ e' σ' efs := by
  rcases h with ⟨hu⟩ | ⟨_, h⟩
  · exact absurd hu (hnu _)
  · exact h

/-- iris-lean's `wp_lift_base_step` for a plain redex, in terms of the real
`base_step` and `gooseStateInterp`. -/
theorem goose_wp_lift_base_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={∅,E}=∗
        gooseCfgInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc hnu Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_plain hnc).1 Hstep
  replace Hstep' := baseStep_of_headStep hnu Hstep'
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hwp Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step` for a plain redex. -/
theorem goose_wp_lift_atomic_base_step {e₁ : Expr} {Φ : val → IProp GF} (h : toVal e₁ = none)
    (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        gooseCfgInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact goose_baseReducible_of hnc hnu Hred
  inext
  iintro %e₂ %s₂ %eₜ %Hstep Hcred
  obtain ⟨σ₂, rfl, Hstep'⟩ := (boundedBaseStep_plain hnc).1 Hstep
  replace Hstep' := baseStep_of_headStep hnu Hstep'
  imod H $$ %e₂ %σ₂ %eₜ %Hstep' Hcred with ⟨Hσ, HΦ, Hefs⟩
  imodintro
  iframe HΦ Hefs
  iapply (goose_bstateInterp_eq σ₂ c _ _ _).2
  iframe

/-- iris-lean's `wp_lift_atomic_base_step_no_fork` for a plain redex. -/
theorem goose_wp_lift_atomic_base_step_no_fork {e₁ : Expr} {Φ : val → IProp GF}
    (h : toVal e₁ = none) (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ ns obs obs' nt, gooseCfgInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ obs e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        ⌜eₜ = []⌝ ∗ gooseCfgInterp σ₂ (ns + 1) obs' nt ∗ (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_atomic_base_step h hnc hnu
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
    (hnc : redexKind e₁ = .plain) (hnu : ∀ p, ¬ Unwinds e₁ p) :
    (∀ σ₁ : CfgState, naHeapCtx tls σ₁.1.heap ={E}=∗
      ⌜GooseBaseReducible e₁ σ₁⌝ ∗
      ▷ ∀ κ e₂ σ₂ eₜ, ⌜BaseStep e₁ σ₁ κ e₂ σ₂ eₜ⌝ -∗ £ 1 ={E}=∗
        ⌜κ = [] ∧ eₜ = []⌝ ∗
        (∃ h', ⌜σ₂ = setHeap (fun _ => h') σ₁⌝ ∗ naHeapCtx tls h') ∗
        (∃ v, ⌜toVal e₂ = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_atomic_base_step_no_fork h hnc hnu
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
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

/-- The lifting lemma for an operation `o` of the extension `X`: a step of `X`
with access to the heap and to `X`'s state. -/
theorem wp_extStep {X : GooseExt} [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X]
    (o : X.Op) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false) :
    (∀ h σ g, naHeapCtx tls h -∗ I.localCtx (extLocalGS X) σ -∗
      I.globalCtx (extGlobalGS X) g ={E,∅}=∗
      ⌜∃ e' h' σ' g', ExtSemantics.step o v h σ g e' h' σ' g'⌝ ∗
      ▷ ∀ e' h' σ' g', ⌜ExtSemantics.step o v h σ g e' h' σ' g'⌝ -∗ £ 1 ={∅,E}=∗
        naHeapCtx tls h' ∗ I.localCtx (extLocalGS X) σ' ∗ I.globalCtx (extGlobalGS X) g' ∗
        WP e' @ s; E {{ Φ }})
    ⊢ WP (ExternalOp (extOp X o) (Val v)) @ s; E {{ Φ }} := by
  iintro H
  iapply goose_wp_lift_base_step rfl rfl (by not_unwinds)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  icases HasExt.localCtx_acc (X := X) _ $$ Hext with ⟨Hl, Hlclose⟩
  icases HasExt.globalCtx_acc (X := X) _ $$ Hgext with ⟨Hg, Hgclose⟩
  imod H $$ %σ₁.1.heap %(hX.mem.get σ₁.1.world) %(hX.mem.get σ₁.2.globalWorld) Hheap Hl Hg
    with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨e', h', σ', g', Hst⟩ := Hred
    exact ⟨[], e', _, [], BaseStep.ExternalOpS _ _ _ σ₁ _
      ((extStep_injOp _ _ _ _ _ _).2 ⟨h', σ', g', (HasExt.step_iff ..).2 Hst, rfl⟩)⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hbs Hcred
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hst =>
  obtain ⟨h', σ', g', Hst', rfl⟩ := (extStep_injOp _ _ _ _ _ _).1 Hst
  imod H $$ %e₂ %h' %σ' %g' %((HasExt.step_iff ..).1 Hst') Hcred with ⟨Hheap, Hl, Hg, Hwp⟩
  imodintro
  isplitl [Hheap Hl Hg Hlclose Hgclose Hgs Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    dsimp only [List.nil_append]
    iframe Hheap Hgs Hproph
    isplitl [Hl Hlclose]
    · iapply Hlclose $$ Hl
    isplitr
    · ipureintro; exact Hlctx
    iapply Hgclose $$ Hg
  iframe Hwp
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- Access to the interpretation of the extension `X`'s state before any step
of a non-value `e`. -/
theorem wp_ext_acc {X : GooseExt} [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X]
    (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    (∀ σ g, I.localCtx (extLocalGS X) σ -∗ I.globalCtx (extGlobalGS X) g ={E}=∗
      I.localCtx (extLocalGS X) σ ∗ I.globalCtx (extGlobalGS X) g ∗ WP e @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  iintro Hacc
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc⟩
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  icases HasExt.localCtx_acc (X := X) _ $$ Hext with ⟨Hl, Hlclose⟩
  icases HasExt.globalCtx_acc (X := X) _ $$ Hgext with ⟨Hg, Hgclose⟩
  imod Hacc $$ %(hX.mem.get σ₁.1.world) %(hX.mem.get σ₁.2.globalWorld) Hl Hg with ⟨Hl, Hg, Hwp⟩
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iapply Hwp $$ %(σ₁, c) %ns %obs %obs' %nt
  iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
  iframe Hc
  iapply (goose_stateInterp_eq _ _ _ _).mpr
  ihave Hl := Hlclose $$ Hl
  ihave Hg := Hgclose $$ Hg
  rw [ExtIn.set_get, ExtIn.set_get]
  iframe
  ipureintro; exact Hlctx

/-- `Panic msg` (a run-time panic of a builtin: an index out of range, a failed
type assertion, ...) is stuck: proofs show that it is unreachable. A panic that
unwinds is `go.panic`'s (`Raise`, `wp_panic`). -/
theorem wp_PanicOp (msg : String) (Φ : val → IProp GF) :
    ▷ False ⊢ WP (Panic msg) @ s; E {{ Φ }} := by
  iintro >%H
  exact H.elim

theorem wp_ArbitraryInt :
    {{ (True : IProp GF) }} ArbitraryInt @ s; E {{ (x : w64), RET #x; True }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem wp_finish_store (l : Loc) (v v' : val) (Hv : v.isPanic = false := by simp) :
    {{ ▷ naHeapPointstoSt (GF := GF) WSt l (.own 1) v' ∗
        (∀ v', naHeapPointsto l (.own 1) v' -∗ heapPointsto l (.own 1) v') }}
      (FinishStore (Val #l) (Val v)) @ s; E
    {{ RET #(); heapPointsto l (.own 1) v }} := by
  iintro %Φ ⟨>Hl, Hl_rest⟩ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

/-- The read-lock function for `naMode`. -/
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

theorem wp_start_read (l : Loc) (q : DFrac) (v : val) :
    {{ ▷ heapPointsto (GF := GF) l q v }} (StartRead (Val #l)) @ s; E
    {{ RET v; naHeapPointstoSt (RSt 1) l q v ∗
        (∀ v', naHeapPointsto l q v' -∗ heapPointsto l q v') }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem wp_atomic_swap (l : Loc) (v0 v : val) (Hv : v.isPanic = false := by simp) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v0 }} (AtomicSwap (Val #l) (Val v)) @ s; E
    {{ RET v0; heapPointsto l (.own 1) v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem atomicAddEval_not_panic {v0 v1 v : val} (Hev : atomicAddEval v0 v1 = some v) :
    v1.isPanic = false := by
  unfold atomicAddEval at Hev; split at Hev <;> simp_all [val.isPanic]

theorem wp_atomic_add (l : Loc) (v0 v1 v : val) (Hev : atomicAddEval v0 v1 = some v) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v0 }} (AtomicAdd (Val #l) (Val v1)) @ s; E
    {{ RET v; heapPointsto l (.own 1) v }} := by
  have Hv1 := atomicAddEval_not_panic Hev
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem wp_cmpxchg_fail (l : Loc) (q : DFrac) (v' v1 v2 : val) (Hne : v' ≠ v1)
    (Hv1 : v1.isPanic = false := by simp) (Hv2 : v2.isPanic = false := by simp) :
    {{ ▷ heapPointsto (GF := GF) l q v' }} (CmpXchg (Val #l) (Val v1) (Val v2)) @ s; E
    {{ RET (PairV v' #false); heapPointsto l q v' }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem wp_cmpxchg_suc (l : Loc) (v1 v2 v' : val) (Heq : v' = v1)
    (Hv1 : v1.isPanic = false := by simp) (Hv2 : v2.isPanic = false := by simp) :
    {{ ▷ heapPointsto (GF := GF) l (.own 1) v' }} (CmpXchg (Val #l) (Val v1) (Val v2)) @ s; E
    {{ RET (PairV v' #true); heapPointsto l (.own 1) v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

def pointstoVals (l : Loc) (q : DFrac) (vs : List val) : IProp GF :=
  [∗list] j ↦ vj ∈ vs, heapPointsto (l +ₗ (j : Int)) q vj

theorem wp_allocN_seq (v : val) (Hv : v.isPanic = false := by simp) :
    {{ (True : IProp GF) }} (Alloc (Val v)) @ s; E
    {{ l, RET #l; pointstoVals l (.own 1) [v] }} := by
  iintro %Φ _ HΦ
  iapply wp_lift_atomic_heap_step rfl rfl (by not_unwinds)
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

theorem wp_alloc_untyped (v : val) (Hv : v.isPanic = false := by simp) :
    {{ (True : IProp GF) }} (Alloc (Val v)) @ s; E
    {{ l, RET #l; heapPointsto l (.own 1) v }} := by
  iintro %Φ _ HΦ
  iapply wp_allocN_seq v Hv
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
  icases (goose_bstateInterp_eq σ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  imodintro
  isplitr
  · ipureintro; exact ⟨[], _, _, _, .exit (.base not_unwinds_ThreadExit (BaseStep.ThreadExitS σ))⟩
  inext
  iintro %e₂ %s₂ %eₜ %Hstep _
  cases Hstep with
  | step hp _ => cases hp
  | tick hc _ => cases hc
  | stutter hc _ => cases hc
  | exit Hb =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      baseStep_ThreadExit_inv (baseStep_of_headStep not_unwinds_ThreadExit Hb)
    imodintro
    isplitl [Hheap Hext Hgs Hgext Hproph Hc Ht Hnc Htok]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      isplitl [Hheap Hext Hgs Hgext Hproph]
      · iapply (goose_stateInterp_eq _ _ _ _).mpr
        dsimp only [List.nil_append]
        iframe
        ipureintro; exact Hlctx
      · iframe Hc Hnc
        iapply (threadFuel_exit (GF := GF) t)
        iframe
    isplitl [HΦ]
    · iexists #()
      isplit
      · ipureintro; rfl
      · iexact HΦ
    iapply BigSepL.bigSepL_nil.2
    itrivial

/-- The forked thread `e ;; ThreadExit` runs `e`, which must not panic and must
end with a thread token, and returns the token at its `ThreadExit`. -/
theorem wp_seq_ThreadExit (e : Expr) :
    WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ (threadTok : IProp GF) }} ⊢
      WP (Seq e ThreadExit) @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ }} := by
  refine .trans (wp_mono fun v => ?_)
    (wp_bind (fill [EctxItem.AppRCtx (Rec BAnon BAnon ThreadExit)]))
  refine (?_ : iprop(⌜v.isPanic = false⌝ ∗ (threadTok : IProp GF)) ⊢
    WP (App (Rec BAnon BAnon ThreadExit) (Val v)) @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ }})
  iintro ⟨%hv, Htok⟩
  iapply (wp_bind (fill [EctxItem.AppLCtx v hv]) : WP (Rec BAnon BAnon ThreadExit) @ s; ⊤
    {{ w, WP (App (Val w) (Val v)) @ s; ⊤ {{ w, ⌜val.isPanic w = false⌝ }} }} ⊢
    WP (App (Rec BAnon BAnon ThreadExit) (Val v)) @ s; ⊤ {{ w, ⌜val.isPanic w = false⌝ }})
  iapply (wp_pure_step_later (Hexec := pure_recc BAnon BAnon ThreadExit) trivial)
  inext
  iintro _
  iapply wp_value'
  iapply wp_pure_step_later (e₂ := ThreadExit) (Hexec := pure_beta BAnon BAnon ThreadExit v) hv
  inext
  iintro _
  iapply wp_ThreadExit $$ Htok
  inext
  ipureintro
  exact isPanic_intoVal ()

/-- `Fork e`, with a ghost update at the fork: the forking thread receives a thread token (out of
the thread fuel) and a later credit, and turns them, by an update at its own mask, into the forked
thread's `WP` (which must end with a thread token, returned at its `ThreadExit`) and its own
continuation. `Fork` may stutter, so it is not atomic and an invariant cannot be opened around it;
the update here is how a proof opens one at the fork itself, e.g. to put the fresh token where a
resource the forked thread needs was (`wp_fork_tok` is this without the update). -/
theorem wp_fork_tok_upd (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ £ 1 -∗ |={E}=> (WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} ∗
        Φ #())) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro H
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  have Hred : BaseStep.Reducible (Fork e, ((σ, ⟨c, t⟩) : BcfgState)) := by
    cases t with
    | zero => exact ⟨[], _, _, [], .forkStutter⟩
    | succ t => exact ⟨[], _, _, _, .fork (.base (not_unwinds_Fork e) (BaseStep.ForkS e σ))⟩
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
    obtain ⟨rfl, rfl, rfl, rfl⟩ := baseStep_Fork_inv (baseStep_of_headStep (not_unwinds_Fork e) Hb)
    rename_i t
    icases threadFuel_fork t $$ Ht with ⟨Ht, Htok⟩
    imod Hclose
    imod H $$ Htok Hcred with ⟨He, HΦ⟩
    imodintro
    isplitl [Hheap Hext Hgs Hgext Hproph Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht Hnc
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
    isplitl [Hheap Hext Hgs Hgext Hproph Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht Hnc
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

/-- `Fork e`: the forking thread receives a thread token (out of the thread fuel)
and the forked thread must end with one (it is returned at its `ThreadExit`).
Whether the token is kept by the forking thread, given to the forked thread or
deposited in an invariant is up to the proof. -/
theorem wp_fork_tok (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} ∗ Φ #()) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_fork_tok_upd
  inext
  iintro Htok _
  imodintro
  iapply H $$ Htok

/-- `Fork e` without thread tokens: the forked thread's token stays with it. The
forked thread must not panic (a panic that unwinds a goroutine kills the
program). -/
theorem wp_fork (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ }} -∗ ▷ Φ #() -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_fork_tok
  inext
  iintro Htok
  iframe HΦ
  iapply (wp_wand (Φ := fun (v : val) => iprop(threadTok ∗ ⌜v.isPanic = false⌝))) $$ [He Htok]
  · iapply (wp_frame_l (Φ := fun (v : val) => iprop(⌜v.isPanic = false⌝)))
    iframe
  iintro %_ ⟨Htok, %Hv⟩
  iframe Htok
  ipureintro; exact Hv

/-- `Fork e`, the fresh thread token going to the forked thread: its body receives the token and
must end with one. (`wp_fork` is this with the token framed through the body.) -/
theorem wp_fork_tok_body (e : Expr) (Φ : val → IProp GF) :
    ⊢ ▷ (threadTok -∗ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) -∗ ▷ Φ #() -∗
      WP (Fork e) @ s; E {{ Φ }} := by
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
    ⊢ ▷ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }} -∗ ▷ (threadTok -∗ Φ #()) -∗
      WP (Fork e) @ s; E {{ Φ }} := by
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
    (Φ : val → IProp GF) (m : Nat) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s')
    (Harg : arg.isPanic = false) :
    ⧖ m ∗ ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ⧗ 1 -∗ ⧖ (m + 1) -∗ ownGoStateCtx gs ={E}=∗
          ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro ⟨#Hm, HΦ⟩
  iapply wp_lift_step (EctxLanguage.fill_not_val K _ rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, ⟨c, t⟩⟩
  icases (goose_bstateInterp_eq σ₁ ⟨c, t⟩ ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  obtain ⟨e', s', h⟩ := Hok σ₁.1.goState.packageState
  have Hreal := HeadStep.base (not_unwinds_GoInstruction Harg)
    (BaseStep.GoInstructionS op arg e' s' σ₁ (Hlctx ▸ h))
  have Hred : BaseStep.Reducible
      (App (Val (GoInstruction op)) (Val arg), ((σ₁, ⟨c, t⟩) : BcfgState)) := by
    cases c with
    | zero => exact ⟨[], _, (σ₁, ⟨0, t⟩), [], .stutter (redexKind_GoInstruction Harg) Hreal⟩
    | succ c => exact ⟨[], e', (_, ⟨c, t⟩), [], .tick (redexKind_GoInstruction Harg) Hreal⟩
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
  | step hnc _ => rw [redexKind_GoInstruction Harg] at hnc; cases hnc
  | tick _ Hbs =>
    obtain ⟨s', Hgo, rfl, rfl, rfl⟩ :=
      baseStep_GoInstruction_inv (baseStep_of_headStep (not_unwinds_GoInstruction Harg) Hbs)
    rw [Hlctx] at Hgo
    imod Hclose
    imod receiptFuel_tick _ m $$ [Hc] with ⟨Hc, Hr, Hm'⟩
    · iframe Hc; iexact Hm
    imod HΦ $$ %e₂' %_ %s' %Hgo Hcred Hr Hm' Hgs with ⟨Hgs, Hwp⟩
    imodintro
    isplitl [Hheap Hext Hgs Hgext Hproph Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht Hnc
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
    isplitl [Hheap Hext Hgs Hgext Hproph Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq _ _ _ _ _).2
      iframe Hc Ht Hnc
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
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s')
    (Harg : arg.isPanic = false) :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ⧗ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iintro HΦ
  imod preceipt_zero (GF := GF) with #H0
  iapply wp_GoInstruction_preceipt K op arg Φ 0 Hok Harg
  iframe H0
  inext
  iintro %e' %gs %gs' %Hstep Hlc Hr _ Hgs
  iapply HΦ $$ %e' %gs %gs' %Hstep Hlc Hr Hgs

/-- WP for go instructions. -/
theorem wp_GoInstruction (K : List EctxItem) (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s')
    (Harg : arg.isPanic = false) :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP (fill K e') @ s; E {{ Φ }}))
    ⊢ WP (fill K (App (Val (GoInstruction op)) (Val arg))) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_GoInstruction_receipt K op arg Φ Hok Harg
  inext
  iintro %e' %gs %gs' %Hstep Hlc _ Hgs
  iapply HΦ $$ %e' %gs %gs' %Hstep Hlc Hgs

/-- `wp_GoInstruction` with an empty evaluation context. -/
theorem wp_GoInstruction' (op : GoInstruction) (arg : val)
    (Φ : val → IProp GF) (Hok : ∀ s, ∃ e' s', IsGoStep op arg e' s s')
    (Harg : arg.isPanic = false := by simp) :
    ▷ (∀ e' gs gs', ⌜IsGoStep op arg e' gs gs'⌝ →
        (£ 1 -∗ ownGoStateCtx gs ={E}=∗ ownGoStateCtx gs' ∗ WP e' @ s; E {{ Φ }}))
    ⊢ WP (App (Val (GoInstruction op)) (Val arg)) @ s; E {{ Φ }} :=
  wp_GoInstruction [] op arg Φ Hok Harg

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
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl (by not_unwinds)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
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
  isplitl [Hheap Hext Hgs Hgext Hproph]
  · iapply (goose_stateInterp_eq _ _ _ _).mpr
    dsimp only
    iframe
    ipureintro; exact Hlctx
  iexists #p
  isplit
  · ipureintro; rfl
  iapply HΦ $$ %_ %p Htok

theorem wp_resolve_proph (p : proph_id) (pvs : List val) (v : val)
    (Hv : v.isPanic = false := by simp) :
    {{ proph (GF := GF) p pvs }} (ResolveProph (Val #p) (Val v)) @ s; E
    {{ (pvs' : List val), RET #(); ⌜pvs = v :: pvs'⌝ ∗ proph p pvs' }} := by
  iintro %Φ Hp HΦ
  iapply goose_wp_lift_atomic_base_step_no_fork rfl rfl (by not_unwinds)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
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
  isplitl [Hheap Hext Hgs Hgext Hproph]
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

/-! ## Panics

A panic outcome `PanicV p` unwinds every evaluation frame but `Catch`'s
(`HeadStep.unwind`), so a postcondition `Φ` also receives panics: `wp_unwind`
takes `Φ (PanicV p)` through a `Catch`-free evaluation context, and `wp_catch`
splits on the outcome of the expression under a `Catch`. A spec
`{{ P }} e {{ RET v; Q }}` names a normal value (no Go value is a panic,
`isPanic_intoVal`), so it excludes panics. -/

section panic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

open EctxLanguage

/-- The panic in an unwinding redex is unique. -/
theorem unwinds_det {Ki Ki' : EctxItem} {p p' : val}
    (h : fillItem Ki (Val (PanicV p)) = fillItem Ki' (Val (PanicV p'))) : p = p' := by
  cases Ki <;> cases Ki' <;> simp only [fillItem, reduceCtorEq, Expr.App.injEq, Expr.Pair.injEq,
    Expr.If.injEq, Expr.Fst.injEq, Expr.Snd.injEq, Expr.Primitive1.injEq, Expr.Primitive2.injEq,
    Expr.ExternalOp.injEq, Expr.CmpXchg.injEq, Expr.ResolveProph.injEq, Expr.Catch.injEq,
    Expr.Val.injEq, val.PanicV.injEq] at h <;>
    (repeat (obtain ⟨h₁, h⟩ := h; try subst h₁)) <;> (try subst h) <;> simp_all [val.isPanic]

/-- The unwinding step: a frame other than `Catch`'s around a panic steps to the panic. -/
theorem pure_unwind (Ki : EctxItem) (p : val) (hK : Ki.unwinds = true) :
    Language.PureExec True 1 (fillItem Ki (Val (PanicV p))) (Val (PanicV p)) where
  pureExec _ := by
    have hnc := redexKind_unwind Ki p
    refine .tail _ (.rfl _) (purePrimStep_of_pureBaseStep
      ⟨fun σ => ⟨_, _, _, BoundedBaseStep.step (f := σ.2) hnc (.unwind ⟨Ki, hK, rfl⟩)⟩, ?_⟩)
    intro σ₁ σ₂ obs e₂' eₜ h
    obtain ⟨σ', rfl, h'⟩ := (boundedBaseStep_plain (σ := σ₁.1) (f := σ₁.2) hnc).1 h
    rcases h' with ⟨⟨Ki', _, hu⟩⟩ | ⟨hnu, _⟩
    · cases unwinds_det hu; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact absurd ⟨Ki, hK, rfl⟩ (hnu p)

/-- `Raise v` panics with `v`. -/
theorem wp_raise (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false) :
    Φ (PanicV v) ⊢ WP (Raise (Val v)) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply (wp_pure_step_later (Hexec := pure_raise v) hv)
  inext
  iintro _
  iapply wp_value'
  iexact HΦ

/-- A panic unwinds an evaluation context without a `Catch` frame. -/
theorem wp_unwind (K : List EctxItem) (hK : ∀ Ki ∈ K, Ki.unwinds = true) (p : val)
    (Φ : val → IProp GF) :
    Φ (PanicV p) ⊢ WP (fill K (Val (PanicV p))) @ s; E {{ Φ }} := by
  induction K generalizing Φ with
  | nil => exact wp_value'
  | cons Ki K ih =>
    rw [EctxItemLanguage.fill_cons]
    refine .trans ?_ (wp_bind (fill K))
    refine .trans (ih (fun Ki h => hK Ki (List.mem_cons_of_mem _ h)) _) ?_
    refine (?_ : WP (fill K (Val (PanicV p))) @ s; E {{ Φ }} ⊢ _)
    iintro H
    iapply (wp_pure_step_later (Hexec := pure_unwind Ki p (hK Ki List.mem_cons_self)) trivial)
    inext
    iintro _
    iapply wp_value'
    iexact H

/-- `Catch e h k`: evaluate `e` first (`wp_catch_panic`, `wp_catch_val` take the
`Catch` step on its outcome). -/
theorem wp_catch (e h k : Expr) (Φ : val → IProp GF) :
    WP e @ s; E {{ v, WP (Catch (Val v) h k) @ s; E {{ Φ }} }} ⊢
      WP (Catch e h k) @ s; E {{ Φ }} :=
  wp_bind (fill [EctxItem.CatchCtx h k])

/-- A panic reaching a `Catch` continues with the handler. -/
theorem wp_catch_panic (p : val) (h k : Expr) (Φ : val → IProp GF) :
    ▷ (£ 1 -∗ WP (App h (Val p)) @ s; E {{ Φ }}) ⊢ WP (Catch (Val (PanicV p)) h k) @ s; E {{ Φ }} :=
  wp_pure_step_later (Hexec := pure_catch_panic p h k) trivial

/-- A value reaching a `Catch` continues with the normal continuation. -/
theorem wp_catch_val (v : val) (h k : Expr) (Φ : val → IProp GF) (hv : v.isPanic = false) :
    ▷ (£ 1 -∗ WP (App k (Val v)) @ s; E {{ Φ }}) ⊢ WP (Catch (Val v) h k) @ s; E {{ Φ }} :=
  wp_pure_step_later (Hexec := pure_catch_val v h k) hv

end panic

end Perennial
