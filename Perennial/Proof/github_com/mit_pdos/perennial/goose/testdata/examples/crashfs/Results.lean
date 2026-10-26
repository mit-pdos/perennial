/-
The end-to-end result of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs`:
the crash adequacy of its boot program, which initializes the package and runs
`Main`, at the start and after every crash, against the filesystem alone.

The boot program's precondition, over a generation's local ghost state `L`, is the
invariant of the file `"f"` (`fileInv`, under `L`'s file ghost state) and the package
state of a fresh program. The first generation establishes it from the initial
file `"f"` (empty); after a crash, the files' ghost state is the crashed
generation's (`fs_crash_adequacy`), so the same invariant holds of the next
generation. The conclusion: in every execution with crashes, no thread is stuck
and none has an unrecovered panic, so `Main`'s assertions (`panic`s) never fire.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Link
public import Perennial.GooseLang.Ext.Fs.Adequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext

namespace github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExtsCrashInterp fsExts_hasFs

/-- The boot program: initialize the package, then call `Main` (as goose calls a
function: resolve it, then apply it). -/
def boot [GoGlobalContext] : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Main []))) (Val #())) (Val #()))

/-- The namespace of the invariant of the file. -/
def fileN : Namespace := nroot.@"crashfs"

section adequacy
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of the boot program in the generation with local ghost
state `L`: the invariant of the file, under `L`'s files' ghost state, and the
package state of a fresh program. -/
def bootPre [G : GooseGlobalGS .hasLC GF] (L : GooseLocalGS GF) : IProp GF :=
  iprop((∃ γ, inv fileN (fileInv (hG := ⟨G, L⟩) (extLocalGS fsExt (L := L)) γ)) ∗
    ownGoState (hG := L.goose_go_stateGS) ∅)

/-- The `get_is_pkg_init` of the boot program: the package and `fsffi`. -/
def getIsPkgInit [HeapGS .hasLC GF] (p : GoString) : IProp GF :=
  if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs then
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs
  else if p = pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi then
    isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi
  else iprop(True)

/-- Crash safety of the boot program: for any receipt and thread bounds `N` and
`T`, in every real execution with crashes of `boot` of fewer than `N` steps,
from a state whose Go context satisfies the Go semantics and the package's
assumptions, with no package initialized, the main thread only, and the file
`"f"` empty (other files may exist), along which fewer than `T` threads are live, the boot program's
result is `#()`, no thread is stuck and no thread has an unrecovered panic: the
assertions of `Main` hold, however many times the node crashes. -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [hPre : GooseGpreS GF] (N T : Nat) (σ : state) (g : GlobalState)
    (Hlctx : σ.goState.goLctx = lctx) (Hpkgs : σ.goState.packageState = ∅)
    (Hfile : extLocal fsExt σ.world !! go!"f" = some go!"")
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps boot n ([boot], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow boot T n ([boot], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine fs_crash_adequacy (GF := GF) N T boot σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) (fun L => bootPre L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: the file is empty; allocate the invariant
    intro hG _ _ _
    rw [Hpkgs]
    iintro Hf Hgs
    icases (BigSepM.bigSepM_lookup (Φ := fun f c => (f fs↦ c : IProp GF)) Hfile) $$ Hf with Hf
    imod dghostVar_alloc (GF := GF) () with ⟨%γ, Hown⟩
    imod inv_alloc fileN ⊤ (fileInv gooseFsGS γ) $$ [Hf Hown] with #Hinv
    · inext; iexists go!""; iframe Hf; ileft; iframe Hown; ipureintro; rfl
    imodintro
    unfold bootPre
    iframe Hgs
    iexists γ
    iexact Hinv
  · -- every generation: the boot program, and the invariant for the next one
    intro hG _ _ Hlctx'
    -- the generation's Go context is `lctx`, for which the Go semantics holds
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    have Hne : pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi ≠
        pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs := by
      unfold pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi
        pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs
      decide
    have Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs (getIsPkgInit (GF := GF)) := by
      refine ⟨by simp [getIsPkgInit], ⟨by simp [getIsPkgInit, Hne], trivial⟩, trivial⟩
    have wp_Main' := fun N γ =>
      (FuncUnfold.func_unfold (f := Main) (type_args := [])) ▸ wp_Main (GF := GF) N γ
    unfold bootPre
    iintro ⟨⟨%γ, #Hinv⟩, Hgs⟩ _
    imodintro
    isplitl [Hgs]
    · -- the boot program
      unfold boot
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
      wp_apply wp_Main' fileN γ $$ [Hinv]
      · iexact Hinv
      ipureintro; rfl
    · -- after a crash, the files' ghost state is the generation's, and so is the invariant
      iintro %L' _ %Hfs Hgs'
      imodintro
      iframe Hgs'
      iexists γ
      rw [Hfs]
      iexact Hinv

end adequacy

end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

end Perennial
