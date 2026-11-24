/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/grovefile`:
the adequacy, on a single Grove node (fail-stop), of the program that initializes
the package and runs `Run`.

The proof gets the points-to of the node's initial files
(`grove_single_node_adequacy`); with the file `"f"` among them, `Run`'s spec
applies, and its result is that `Run` returns normally. The conclusion,
`grovefile_safety`, mentions no ghost state and no bounds: in every execution of
the program, its result is `#()` if it returns, no thread is stuck and none has an
unrecovered panic, so `Run`'s checks (`panic`s) never fire: the read returns what
was written, and the TSC does not decrease.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Link
public import Perennial.GooseLang.Ext.Grove.Adequacy
public import Perennial.GooseLang.CrashLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

namespace github_com.mit_pdos.perennial.goose.testdata.examples.grovefile

attribute [local instance] groveExts groveExtsSemantics groveExtsInterp groveExts_hasGrove

/-- The program: initialize the package, then call `Run` (as goose calls a
function: resolve it, then apply it). -/
def main [GoGlobalContext] : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Run []))) (Val #())) (Val #()))

/-- Ghost state for a Grove program: one slot for each camera that `GooseGpreS`
needs for `[groveExt]` (the network, the listened-on endpoints and the files share
the meta data slot, and the first two the slot of their ghost names; the TSC and the
global time share the `MonoNat` slot). -/
def groveGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨constOF (HeapView byte_string (Agree (DiscreteO (List w8))) (GMap byte_string)),
      inferInstance⟩
  | 8 => ⟨constOF (HeapView byte_string (Agree (DiscreteO GName)) (GMap byte_string)),
      inferInstance⟩
  | 9 => ⟨constOF MetaUR, inferInstance⟩
  | 10 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨constOF (HeapView Endpoint (Agree (DiscreteO (GSet message))) (GMap Endpoint)),
      inferInstance⟩
  | 12 => ⟨constOF (HeapView Endpoint (Agree (DiscreteO GName)) (GMap Endpoint)), inferInstance⟩
  | 13 => ⟨MonoNatRF, inferInstance⟩
  | 14 => ⟨constOF (HeapView Endpoint (Agree (DiscreteO Bool)) (GMap Endpoint)), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

instance groveGpreS : GooseGpreS groveGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨⟨⟨⟨11, rfl⟩⟩, ⟨⟨12, rfl⟩⟩, ⟨9, rfl⟩⟩, ⟨⟨⟨14, rfl⟩⟩, ⟨⟨12, rfl⟩⟩, ⟨9, rfl⟩⟩,
    ⟨⟨⟨7, rfl⟩⟩, ⟨⟨8, rfl⟩⟩, ⟨9, rfl⟩⟩, ⟨⟨13, rfl⟩, 0⟩⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨10, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The `get_is_pkg_init` of the program: the package and `grove_ffi`. -/
def getIsPkgInit [HeapGS .hasLC GF] (p : GoString) : IProp GF :=
  if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile
  else if p = pkg_id.github_com.mit_pdos.gokv.grove_ffi then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.gokv.grove_ffi
  else iprop(True)

/-- `grovefile_safety` for executions of fewer than `N` steps along which fewer
than `T` threads are live, under any ghost state `GF` with `GooseGpreS GF`:
`grove_single_node_adequacy` for the program. -/
theorem grovefile_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : Assumptions]
    [hPre : GooseGpreS GF] (N T : Nat) (σ : state) (g : GlobalState) (old : List w8)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hfile : (extLocal groveExt σ.world).groveNodeFiles !! go!"f" = some old)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([main], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([main], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine grove_single_node_adequacy (GF := GF) N T main σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) ?_ n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  intro hG _ _ Hlctx'
  -- the node's Go context is `lctx`, for which the Go semantics holds
  rw [Hlctx] at Hlctx'
  obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
  subst Hlctx'
  letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
  have Hne : pkg_id.github_com.mit_pdos.gokv.grove_ffi ≠
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile := by
    unfold pkg_id.github_com.mit_pdos.gokv.grove_ffi
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile
    decide
  have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile
      (getIsPkgInit (GF := GF)) := by
    refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne], trivial⟩, trivial⟩
  have wp_Run' := fun old =>
    (FuncUnfold.func_unfold (f := Run) (type_args := [])) ▸ wp_Run (GF := GF) old
  rw [Hpkgs]
  iintro - Hfiles Hgs _
  icases (BigSepM.bigSepM_lookup (Φ := fun f c => (f f↦ c : IProp GF)) Hfile) $$ Hfiles with Hf
  imodintro
  unfold main
  wp_apply wp_initialize' getIsPkgInit Hinit $$ [Hgs] as ⟨_, #Hpkg⟩
  · -- no package is initialized
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  try wp_func_call
  wp_apply wp_Run' old $$ [Hf]
  · iexact Hf
  iintro _
  ipureintro; rfl

/-- Safety of the program on a single Grove node: in every execution of `main`
(`RealNsteps`, the real semantics, fail-stop), from a state whose Go context
satisfies the Go semantics and the package's assumptions, with no package
initialized, the main thread only, and a file `"f"` (any contents; other files
may exist, and the network and the TSC may be anything), the program's result is
`#()` if it returns, no thread is stuck and no thread has an unrecovered panic:
the checks of `Run` hold. (`grovefile_safety_bounded` with the ghost state
`groveGF`, the step bound `n + 1` and the thread bound `n + 2`, which an
execution of `n` steps from one thread respects, `real_nsteps_threads`.) -/
theorem grovefile_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (σ : state) (g : GlobalState) (old : List w8)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hfile : (extLocal groveExt σ.world).groveNodeFiles !! go!"f" = some old)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([main], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  grovefile_safety_bounded (GF := groveGF) (n + 1) (n + 2) σ g old Hlctx Hpkgs Hfile n κs t2 σ2
    Hsteps (by omega) Hthreads (fun k κs' ρ' hk h => by
      have := real_nsteps_threads h
      simp only [Hthreads] at this
      omega)

end adequacy

end github_com.mit_pdos.perennial.goose.testdata.examples.grovefile

end Perennial

#print axioms Perennial.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.grovefile_safety
