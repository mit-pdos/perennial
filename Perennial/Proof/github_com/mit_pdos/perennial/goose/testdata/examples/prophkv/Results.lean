/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/prophkv`: every
execution of the program (initialization, then `Test()`) returns `"a"` or `"b"`, has no stuck
thread and no unrecovered panic.

The proof of `GetAny`'s logically atomic spec uses a prophecy of its result, which the Go code
does not contain: the WP of the program (`wp_prog`) is in a Go model where `GetAny` resolves to
its body under a prophecy (`GetAnyP`, `patchSem` and `assumptionsP` build that model from the
real one), and `goose_adequacy_funcProph` turns it into a theorem about the executions of the
program itself in the real model. Its side condition, that the calls of `GetAny` stay in
position, is checked on the program (`prog_ok`) and assumed of what the model returns
(`ModelOk`) and of the initial heap. The statement mentions no prophecy and no ghost state.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv.Main
public import Perennial.GooseLang.CrashLang
public import Perennial.Golang.Theory.FuncProph

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

/-! ## The instrumented model -/

section model
variable [GooseExts] [GoGlobalContext]

/-- `GetAny`'s instrumented body as a Go function: `GetAnyP`. -/
def GetAnyPFn : GoFunc :=
  ⟨BAnon, "$a1", Rec BAnon "$a2" (withProph (App (App (Val GetAny.impl) (Var "$a1")) (Var "$a2")))⟩

theorem GetAny_not_reserved : GetAny ∉ reservedFuncs := by
  simp (config := { decide := true }) [reservedFuncs, GetAny, go.panic, go.min, go.max,
    github_com.mit_pdos.perennial.goose.model.channel.runtimePanic,
    github_com.goose_lang.primitive.RandomUint64, github_com.goose_lang.primitive.Assume,
    github_com.goose_lang.primitive.NewProph,
    github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice,
    github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString,
    github_com.mit_pdos.perennial.goose.model.strings.DecodeRune,
    github_com.mit_pdos.perennial.goose.model.strings.decoderune]

/-- The package's assumptions in the instrumented model, from those in the real one. -/
theorem assumptionsP (F : GoInstruction → val → Expr → Prop) (sem : @go.Semantics _ ⟨F⟩ _)
    (hA : @Assumptions _ _ ⟨F⟩ sem.sem_fn) :
    @AssumptionsP _ _ (patchLctx ⟨F⟩ GetAny (RecV GetAnyPFn.f GetAnyPFn.x GetAnyPFn.e))
      (patchFns sem.sem_fn GetAny GetAnyPFn) := by
  refine @AssumptionsP.mk _ _ (patchLctx ⟨F⟩ GetAny (RecV GetAnyPFn.f GetAnyPFn.x GetAnyPFn.e))
    (patchFns sem.sem_fn GetAny GetAnyPFn) ?_ ?_ ?_ ?_ ?_
  · transfer hA.1
  · refine @FuncUnfold.mk _ (patchFns sem.sem_fn GetAny GetAnyPFn) _ _ _ _ ?_
    rw [patchFns_functions_ne F sem GetAny GetAnyPFn _ _
      (by simp (config := { decide := true }) [NewKV, GetAny])]
    exact hA.2.1
  · refine @FuncUnfold.mk _ (patchFns sem.sem_fn GetAny GetAnyPFn) _ _ _ _ ?_
    rw [patchFns_functions_nil, if_pos rfl]
    exact congrFun (@go.PreSemantics.core_sem _ ⟨F⟩ _ sem.sem_fn
      (@go.Semantics.core_sem _ ⟨F⟩ _ sem)).intoVal_unfold_func.intoVal_unfold GetAnyPFn
  · refine @FuncUnfold.mk _ (patchFns sem.sem_fn GetAny GetAnyPFn) _ _ _ _ ?_
    rw [patchFns_functions_ne F sem GetAny GetAnyPFn _ _
      (by simp (config := { decide := true }) [Test, GetAny])]
    exact hA.4.1
  · transfer hA.5

end model


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

/-- No extension: no extension step. -/
theorem noExts_good : GoodExts (giOf GetAny) := by
  intro ext op v σg e' σg' hst
  obtain ⟨E, hE, _⟩ := hst
  change extNamed [] ext = some E at hE
  simp [extNamed] at hE

/-- What the Go model may return keeps `GetAny`'s calls in position: its instructions' results
(`GoodModel`: for the program's functions, their bodies, which are) and its prophecy ids'
values. A model of Go satisfies it: Go has no instruction producing a reference to `GetAny` but
the program's own `FuncResolve GetAny`, and no prophecies. -/
structure ModelOk (L : GoLocalContext) : Prop where
  results : GoodModel (giOf GetAny) L
  proph : ∀ p : proph_id, okV (giOf GetAny) #p

theorem prog_ok [GoLocalContext] [go.Semantics] : Perennial.ok (giOf GetAny) 0 prog := by
  simp [prog, Perennial.ok, Perennial.okV, initialize',
    github_com.goose_lang.primitive.initialize', package.init_unseal, package.initDef,
    exceptionDo_unseal, exceptionDoDef, doExecute_unseal, doExecuteDef,
    go.intoVal_unfold Unit, go.intoVal_unfold GoString]
  simp (config := { decide := true }) [Test, GetAny]

/-- The program's safety for executions of fewer than `N` steps along which fewer than `T`
threads are live: `goose_adequacy_funcProph`, from the WP of the program in the model where
`GetAny` runs instrumented (`wp_prog`). -/
theorem prog_safe_bounded [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (N T : Nat) (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hmodel : ModelOk lctx) (Hheap : heapOk (giOf GetAny) σ.heap)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([prog], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → resultOk v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hunit : (#() : val) = unitV := congrFun (go.intoVal_unfold Unit) ()
  refine goose_adequacy_funcProph (GF := prophkvGF) N T prog σ g resultOk ?_ GetAny GetAny.impl
    ?_ (Hlctx ▸ Hmodel.results) noExts_good ?_ prog_ok Hheap trivial trivial ?_
    n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  · intro p h
    rcases h with h | h <;> exact intoVal_ne_PanicV _ p h.symm
  · intro e
    rw [Hlctx, ← hunit]
    have h := (go.CoreSemantics.go_func_resolve_step (n := GetAny) (ts := [])).isGoStep_pure_det
    rw [h, func_unfold]
    exact ⟨Eq.symm, Eq.symm⟩
  · exact { loc := fun x => by simp [go.intoVal_unfold Loc, Perennial.okV]
            bool := fun x => by simp [go.intoVal_unfold Bool, Perennial.okV]
            unit := by simp [go.intoVal_unfold Unit, Perennial.okV]
            w64 := fun x => by simp [go.intoVal_unfold w64, Perennial.okV]
            w32 := fun x => by simp [go.intoVal_unfold w32, Perennial.okV]
            w16 := fun x => by simp [go.intoVal_unfold w16, Perennial.okV]
            w8 := fun x => by simp [go.intoVal_unfold w8, Perennial.okV]
            proph := Hmodel.proph }
  · intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC prophkvGF :=
      ⟨G, ⟨Lexts, patchLctx lctx GetAny (prophFnV GetAny.impl), Lheap, Lgs, Lthr, Lcr⟩⟩
    letI lctxP : GoLocalContext := patchLctx lctx GetAny (prophFnV GetAny.impl)
    letI semP : @go.Semantics _ lctxP _ :=
      patchSem lctx.is_go_step_pure sem GetAny GetAnyPFn GetAny_not_reserved
    haveI : @AssumptionsP _ _ lctxP semP.sem_fn := assumptionsP lctx.is_go_step_pure sem package_sem
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
    iapply wp_prog getIsPkgInit Hinit
    rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro

/-- **The program's safety**: in every real execution of `prog` (the Go program as translated,
with no prophecy), from a state whose Go context satisfies the Go semantics and the package's
assumptions and returns no reference to `GetAny` out of a call (`ModelOk`), whose heap holds none
either, with no package initialized and the main thread only, the program's result is `"a"` or
`"b"`, no thread is stuck and none has an unrecovered panic. -/
theorem prog_safe [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hmodel : ModelOk lctx) (Hheap : heapOk (giOf GetAny) σ.heap) (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([prog], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → resultOk v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  prog_safe_bounded (n + 1) (n + 2) σ g Hlctx Hpkgs Hmodel Hheap n κs t2 σ2 Hsteps (by omega)
    Hthreads (RealThreadsBelow.of_single' Hthreads)

end adequacy


end github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

end Perennial
