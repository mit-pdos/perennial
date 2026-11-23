/-
A ghost step linearized with a channel send, on state shared with the generations after a crash
(regression test of the crash-token update `ncfupd`, `GooseLang/NotCrashed.lean`, in the channel
specifications' atomic updates, `Golang/Theory/Chan/AuSpec/ChanAuBase.lean`).

The node runs `boot` at the start and after every crash: it makes a channel `ch` of capacity 1
and a channel `done`, closes `done`, and forks a goroutine that runs

  select { case ch <- 1: ; case <-done: }

Either clause may fire. A ghost counter `γ` counts the messages ever sent on the generations'
channels `ch`, over all generations: each generation starts from the count `k` its predecessor
left, and keeps the count `k + m`, `m` the length of its `ch`'s buffer, in its crash invariant
`inv crashN ((∃ m, ghostVar γ 1 (k + m) ∗ ghostVar γm ½ m) ∨ crashed ∗ token γt)` (`crashInv`),
whose other half of `γm` the channel's invariant ties to the buffer (`chInv`). So the counter
must be incremented exactly when the send fires: in the client's update of the send's atomic
update, which the channel code runs at its linearization point. That update must open the crash
invariant, which only a thread of a generation that has not crashed can do: it takes the
generation's `notCrashed`, which `sendAu` (a crash-token update) now passes to it.

* `wp_sendOrDone`: the goroutine's WP.
* `wp_boot`: a generation: its WP, and its crash obligation (from `crashed`, the counter for the
  next generation: `token γt` excludes the crash side of the invariant, and takes it over).
* `crash_safety`: `goose_crash_adequacy` for `boot`, for every execution with crashes.

The extensions are left abstract: the program uses none.
-/
module

public import Perennial.Golang.Theory.Chan
public import Perennial.GooseLang.CrashAdequacy
public import Perennial.Ghost.Token
public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace NotCrashedChanTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The program -/

section program
variable [GooseExts] [GoGlobalContext]

/-- The type of a bidirectional channel of `t`. -/
abbrev chanTy (t : go.GoType) : go.GoType := go.GoType.ChannelType go.ChanDir.sendrecv t

/-- `select { case ch <- 1: ; case <-done: }`, over the channel expressions `ch` and `done`. -/
abbrev selectE (ch done : Expr) : Expr :=
  App (Val (GoInstruction SelectStmt)) (SelectStmtClauses none
    [CommClause (SendCase go.uint64 ch (Val #(W64 1))) (Val #()),
     CommClause (RecvCase (go.StructType []) done) (Lam BAnon (Val #()))])

/-- The goroutine, on the channels `ch` and `done`. -/
abbrev sendOrDone (ch done : Loc) : Expr := selectE (Val #ch) (Val #done)

/-- The boot program: make `ch` (capacity 1) and `done`, close `done`, fork the goroutine. -/
def boot : Expr :=
  Let "ch" (App (App (Val (GoInstruction (FuncResolve go.make2 [chanTy go.uint64]))) (Val #()))
    (Val #(W64 1)))
  (Let "done" (App (App (Val (GoInstruction (FuncResolve go.make1 [chanTy (go.StructType [])])))
    (Val #())) (Val #()))
  (Seq (App (App (Val (GoInstruction (FuncResolve go.close [chanTy (go.StructType [])])))
    (Val #())) (Var "done"))
  (Fork (selectE (Var "ch") (Var "done")))))

end program

/-! ## The invariants -/

abbrev chN : Namespace := nroot.@"ch"
abbrev doneN : Namespace := nroot.@"done"
abbrev crashN : Namespace := nroot.@"crash"

section invariants
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The channel `ch` (of this generation): its buffer has as many messages as `γm` counts. -/
abbrev chInv (γch : ChanNames) (γm : GName) : IProp GF :=
  iprop(∃ b : List w64, ownChan γch w64 (.Buffered b) ∗ ghostVar γm (1 : Qp).half b.length)

/-- The crash invariant of this generation: the counter `γ` is `k` (its value when the generation
started) plus `γm`, while the generation runs; once it has crashed, `token γt` (which the
generation's crash obligation holds) may stand for it instead. -/
abbrev crashInv (γ γm γt : GName) (k : Nat) : IProp GF :=
  iprop((∃ m : Nat, ghostVar γ 1 (k + m) ∗ ghostVar γm (1 : Qp).half m) ∨ crashed ∗ token γt)

end invariants

/-! ## The goroutine -/

section goroutine
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
/-- **The goroutine**: whichever clause fires, it does not panic, and the counter stays in step
with `ch`'s buffer. The send clause's atomic update increments the counter when the send fires,
in the crash invariant, which it opens with the crash token that `sendAu` passes it
(`inv_nc_acc`). -/
theorem wp_sendOrDone (ch done : Loc) (γch γd : ChanNames) (γ γm γt : GName) (k : Nat) :
    ⊢ isChan (GF := GF) ch γch w64 -∗ isChan done γd Unit -∗
      inv doneN (ownChan γd Unit (.Closed [])) -∗ inv chN (chInv γch γm) -∗
      inv crashN (crashInv γ γm γt k) -∗
      WP (sendOrDone ch done) {{ v, ⌜v.isPanic = false⌝ }} := by
  iintro #Hch #Hdone #Hdinv #Hcinv #Hkinv
  unfold sendOrDone selectE
  wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `ch <- 1`: the counter is incremented exactly when the send fires
    simp only [chan.blockingClausePre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch, (W64 1)
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iframe Hch
    unfold sendAu
    iintro Hnc
    -- the crash token rules out the crash side of the crash invariant
    ihave Hacc := inv_nc_acc (E := ⊤) (N := crashN) (fun _ _ => CoPset.mem_full) $$ Hkinv
    imod Hacc $$ Hnc with ⟨Hnc, >Hk, Hkclose⟩
    icases Hk with ⟨%m, Hγ, Hm⟩
    iinv Hcinv with Hc Hcclose
    icases Hc with > ⟨%b, Hoc, Hm2⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iframe Hnc
    inext
    iexists .Buffered b
    iframe Hoc
    dsimp only
    iintro Hoc
    imod Hmask with -
    ihave %Heq := ghostVar_agree _ _ _ _ _ $$ Hm Hm2
    subst Heq
    imod ghostVar_update_halves (b ++ [W64 1]).length _ _ _ $$ Hm Hm2 with ⟨Hm, Hm2⟩
    imod ghostVar_update (k + (b ++ [W64 1]).length) _ _ $$ Hγ with Hγ
    imod Hcclose $$ [Hoc Hm2] with -
    · inext
      unfold chInv
      iexists b ++ [W64 1]
      iframe
    imod Hkclose $$ [Hγ Hm] with -
    · inext
      iexists (b ++ [W64 1]).length
      iframe
    imodintro
    wp_auto
    ipureintro; trivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `<-done`: `done` is closed
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γd
    isplitr
    · ipureintro; rfl
    iframe Hdone
    unfold recvAu
    iapply ncfupd_of_fupd
    iinv Hdinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Closed []
    iframe Hi
    dsimp only
    iintro Hd
    imod Hmask with -
    imod Hclose $$ Hd with -
    imodintro
    wp_auto
    ipureintro; trivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end goroutine

/-! ## A generation -/

section generation
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
/-- **A generation**, from the counter's value `k`: the boot program, and the crash obligation,
which gives the counter back once the generation has crashed. The crash invariant is allocated
before the program runs (with `γm` at `0`); the channel's invariant ties `γm`'s other half to the
buffer once `ch` is made. -/
theorem wp_boot (γ : GName) (k : Nat) :
    ⊢ ghostVar (GF := GF) γ 1 k ={⊤}=∗
      WP boot {{ v, ⌜v = #()⌝ }} ∗ (crashed -∗ |={⊤}=> ∃ n : Nat, ghostVar γ 1 n) := by
  iintro Hγ
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γm, Hm⟩
  icases (ghostVar_split_half γm 1 (0 : Nat)).1 $$ Hm with ⟨Hm1, Hm2⟩
  imod inv_alloc crashN ⊤ (crashInv γ γm γt k) $$ [Hγ Hm1] with #Hkinv
  · inext
    ileft
    iexists 0
    rw [Nat.add_zero]
    iframe
  imodintro
  isplitl [Hm2]
  · unfold boot
    wp_auto
    wp_apply chan.wp_make2 (V := w64) (W64 1) $$ [] as %ch %γch ⟨#Hch, %Hcap, Hoc⟩
    · ipureintro; decide
    wp_apply chan.wp_make1 (V := Unit) as %done %γd ⟨#Hdone, -, Hdoc⟩
    wp_apply chan.wp_close (V := Unit) done γd $$ Hdone
    iintro _
    unfold closeAu
    iapply ncfupd_of_fupd
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Idle
    iframe Hdoc
    dsimp only
    iintro Hdoc
    imod Hmask with -
    imod inv_alloc doneN ⊤ (ownChan γd Unit (.Closed [])) $$ [Hdoc] with #Hdinv
    · inext
      iexact Hdoc
    imod inv_alloc chN ⊤ (chInv γch γm) $$ [Hoc Hm2] with #Hcinv
    · inext
      iexists []
      iframe
    imodintro
    wp_auto
    iapply wp_fork
    · inext
      iapply wp_sendOrDone ch done γch γd γ γm γt k $$ Hch Hdone Hdinv Hcinv Hkinv
    · inext
      ipureintro
      rfl
  · -- the crash obligation: `token γt` rules out the crash side, and takes it over
    iintro #Hcr
    iinv Hkinv with H Hclose
    icases H with (> ⟨%m, Hγ, Hm⟩ | > ⟨_, Ht2⟩)
    · imod Hclose $$ [Ht] with -
      · inext
        iright
        iframe Ht
        iexact Hcr
      imodintro
      iexists k + m
      iexact Hγ
    · iexfalso
      iapply token_exclusive $$ Ht Ht2

end generation

/-! ## Crash safety -/

section adequacy
variable [GooseExts] [GooseSemantics] [GooseInterp] [GooseCrashInterp] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- The boot program's precondition: the counter (whose ghost name each generation hands to the
next). -/
def bootPre [G : GooseGlobalGS .hasLC GF] (_L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ (γ : GName) (n : Nat), ghostVar γ 1 n)

/-- `crash_safety` for executions of fewer than `N` steps along which fewer than `T` threads are
live: `goose_crash_adequacy` for `boot`, with `bootPre`. -/
theorem crash_safety_bounded [lctx : GoLocalContext] [sem : go.Semantics] [hPre : GooseGpreS GF]
    (N T : Nat) (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps boot n ([boot], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow boot T n ([boot], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T boot σ g (fun v => v = #())
    (fun p h => intoVal_ne_PanicV () p h.symm) Hinitg Hinit (fun L => bootPre L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: a new counter
    intro hG _ _ _
    iintro _ _ _
    imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γ, Hγ⟩
    imodintro
    unfold bootPre
    iexists γ, 0
    iexact Hγ
  · -- every generation: `wp_boot`
    intro hG _ _ Hlctx'
    rw [Hlctx] at Hlctx'
    obtain ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    subst Hlctx'
    letI hG : HeapGS .hasLC GF := ⟨G, ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    unfold bootPre
    iintro ⟨%γ, %k, Hγ⟩ _
    imod wp_boot γ k $$ Hγ with ⟨Hwp, Hcr⟩
    imodintro
    iframe Hwp
    iintro %L' #Hc _ _ _
    imod Hcr $$ Hc with ⟨%m, Hγ⟩
    imodintro
    iexists γ, m
    iexact Hγ

/-- **Crash safety** of the boot program: in every execution with crashes of `boot`, from a
state whose Go context satisfies the Go semantics, with the main thread only, the boot program
returns `#()`, no thread is stuck and none has an unrecovered panic, however many times the node
crashes. (`crash_safety_bounded` with the ghost state `GF`, the step bound `n + 1` and the thread
bound `n + 2`.) -/
theorem crash_safety [lctx : GoLocalContext] [sem : go.Semantics] [hPre : GooseGpreS GF]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps boot n ([boot], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  crash_safety_bounded (GF := GF) (n + 1) (n + 2) σ g Hlctx Hinitg Hinit n κs t2 σ2 b Hsteps
    (by omega) Hthreads (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

end NotCrashedChanTest

end Perennial
