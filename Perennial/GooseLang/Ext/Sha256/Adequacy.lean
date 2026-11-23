/-
Adequacy for a program that hashes with SHA-256.

* The program runs against the closed list of extensions `[sha256Ext ok]` (`sha256Exts ok`),
  for the run's filter `ok`: the theorem instantiates `goose_adequacy` with it. A program
  proved under `[HasSha256 ok]` for an arbitrary list instantiates its proof with these
  instances; a program with other extensions closes off its own list the same way.
* The run starts with nothing hashed (`extGlobal (sha256Ext ok) g.globalWorld = ∅`).
* The theorem holds for every `ok`. A proof that uses collision resistance (`is_hash_inj`)
  needs `Sha256NoCollision ok`, which then is a hypothesis of the program's top-level theorem:

  ```
  theorem main_safe (ok : Sha256Filter) (Hok : Sha256NoCollision ok) ... :=
    sha256_single_node_adequacy ok ... (fun ... => main_wp ok Hok ...) ...
  ```

  read: every run of the program under the semantics `sha256Ext ok` is safe, for any filter
  that allows no collision; with `sha256NoFilter` the semantics removes no run, and the theorem
  then needs no hypothesis.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.Ext.Sha256.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a program that hashes: SHA-256 alone, with the filter `ok`. -/
@[reducible] def sha256Exts (ok : Sha256Filter) : GooseExts := ⟨[sha256Ext ok]⟩

section adequacy
variable (ok : Sha256Filter)

/-- The semantics of `sha256Exts ok`. -/
@[reducible] def sha256ExtsSemantics : @GooseSemantics (sha256Exts ok) :=
  letI := sha256Exts ok
  ⟨(sha256_semantics ok, ⟨⟩)⟩

/-- The ghost state of `sha256Exts ok`. -/
@[reducible] def sha256ExtsInterp : @GooseInterp (sha256Exts ok) :=
  letI := sha256Exts ok
  ⟨(sha256_interp ok, ⟨⟩)⟩

/-- The program's extension is SHA-256's, with the filter `ok`. -/
theorem sha256Exts_hasSha256 :
    letI := sha256Exts ok; letI := sha256ExtsSemantics ok; letI := sha256ExtsInterp ok
    HasSha256 ok :=
  letI := sha256Exts ok; letI := sha256ExtsSemantics ok; letI := sha256ExtsInterp ok
  ⟨{ registered := rfl, sem_eq := rfl, interp_eq := rfl }⟩

/-- Adequacy for a single node that hashes (fail-stop), for the filter `ok`: the program runs
against `sha256Exts ok`, and starts with nothing hashed. As for `goose_adequacy`, the WP is
proved for arbitrary time-receipt and thread bounds `N` and `T` with a postcondition `φ` that
excludes panics, and the conclusion is about real executions of fewer than `N` steps along
which fewer than `T` threads are live: a final value of the main thread satisfies `φ`, no
thread is stuck, and no thread has an unrecovered panic. -/
theorem sha256_single_node_adequacy {GF : BundledGFunctors} :
    letI := sha256Exts ok; letI := sha256ExtsSemantics ok; letI := sha256ExtsInterp ok
    letI := sha256Exts_hasSha256 ok
    ∀ [GoGlobalContext] [GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state) (g : GlobalState)
      (φ : val → Prop) (_hφ : ∀ p, ¬ φ (PanicV p))
      (_Hg0 : extGlobal (sha256Ext ok) g.globalWorld = (∅ : Sha256State))
      (_Hwp : ∀ [hG : HeapGS .hasLC GF],
        receiptBound GF = N →
        threadBound GF = T →
        hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
        ⊢ ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
          WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
      (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
      (_Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
      (_Hbound : n < N) (_Hthreads : σ.threads = 1)
      (_Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))),
      (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
        (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  letI := sha256Exts ok; letI := sha256ExtsSemantics ok; letI := sha256ExtsInterp ok
  letI := sha256Exts_hasSha256 ok
  intro _ hPre N T e σ g φ hφ Hg0 Hwp n κs t2 σ2 Hsteps Hbound Hthreads Hlive
  refine goose_adequacy (GF := GF) N T e σ g φ hφ ⟨Hg0, trivial⟩ ⟨trivial, trivial⟩ ?_ n κs t2 σ2
    Hsteps Hbound Hthreads Hlive
  intro hG HN HT Hlctx
  iintro - - Hgs Htok
  iapply Hwp HN HT Hlctx $$ Hgs Htok

end adequacy

end Perennial
