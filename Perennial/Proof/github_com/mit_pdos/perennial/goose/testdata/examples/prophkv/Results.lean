/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/prophkv`: every
execution of the program (initialization, then `Test()`) returns `"a"` or `"b"`, has no stuck
thread and no unrecovered panic.

The proof of `Test` uses a prophecy of the program's result, which the Go code does not contain:
it is the WP of the instrumented program `withProph prog` (`wp_withProph_prog`), and
`goose_adequacy_withProph` turns it into a theorem about the executions of `prog` itself. The
statement below mentions no prophecy and no ghost state.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv.Main
public import Perennial.GooseLang.CrashLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

/-- The program runs with no extensions. -/
@[reducible] def noExts : GooseExts := ⟨[]⟩

attribute [local instance] noExts

@[reducible] def noExtsSemantics : GooseSemantics := ⟨PUnit.unit⟩
@[reducible] def noExtsInterp : GooseInterp := ⟨PUnit.unit⟩

attribute [local instance] noExtsSemantics noExtsInterp

/-- Ghost state for a program with no extensions: one slot for each camera `GooseGpreS` needs. -/
noncomputable def prophkvGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance prophkvGpreS : GooseGpreS prophkvGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := PUnit.unit
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The `get_is_pkg_init` of the program: the package and `primitive`. -/
def getIsPkgInit [HeapGS .hasLC GF] (p : GoString) : IProp GF :=
  if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv
  else if p = pkg_id.github_com.goose_lang.primitive then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive
  else iprop(True)

/-- An execution of at most `n` steps from a single thread has fewer than `n + 2` live threads. -/
theorem RealThreadsBelow.of_single' {n : Nat} {ρ : List Expr × CfgState}
    (h1 : ρ.2.1.threads = 1) : RealThreadsBelow (n + 2) n ρ := by
  intro k κs ρ' hk h
  have := real_nsteps_threads h
  omega

/-- The program's safety for executions of fewer than `N` steps along which fewer than `T`
threads are live: `goose_adequacy_withProph`, from the WP of the instrumented program. -/
theorem prog_safe_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (N T : Nat) (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([prog], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → resultOk v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy_withProph (GF := prophkvGF) N T prog σ g resultOk ?_ trivial trivial ?_
    n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  · intro p h
    rcases h with h | h <;> exact intoVal_ne_PanicV _ p h.symm
  · intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC prophkvGF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    have Hne : pkg_id.github_com.goose_lang.primitive ≠
        pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv := by
      unfold pkg_id.github_com.goose_lang.primitive
        pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv
      decide
    have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv
        (getIsPkgInit (GF := prophkvGF)) := by
      refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne], trivial⟩, trivial⟩
    rw [Hpkgs]
    iintro _ _ Hgs _
    imodintro
    iapply wp_withProph_prog getIsPkgInit Hinit
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro

/-- **The program's safety**: in every real execution of `prog` (the Go program as translated,
with no prophecy), from a state whose Go context satisfies the Go semantics and the package's
assumptions, with no package initialized and the main thread only, the program's result is `"a"`
or `"b"`, no thread is stuck and none has an unrecovered panic. -/
theorem prog_safe [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → resultOk v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  prog_safe_bounded (n + 1) (n + 2) σ g Hlctx Hpkgs n κs t2 σ2 Hsteps (by omega) Hthreads
    (RealThreadsBelow.of_single' Hthreads)

end adequacy

end github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

end Perennial
