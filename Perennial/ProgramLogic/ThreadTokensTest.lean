/-
Thread tokens: laws and examples (regression test).

The example is a counter of live goroutines in miniature: a 32-bit counter,
incremented with `atomic.AddUint32` by a thread that deposits its thread token
in the counter's invariant, so that the counter is matched by as many thread
tokens. Since `threadBound GF = T` tokens are contradictory, the counter stays
below `T`; under the premise `T ≤ 2^31` on the (otherwise unspecified) bound,
the 32-bit addition never wraps around, without any precondition on the
callers. This is the shape of the argument that a `sync.WaitGroup`'s counter,
backed by one token per goroutine that has been `Add`ed and not yet `Done`,
stays below `2^31` because that many goroutines cannot be live at once. A client
discharges the premise when it instantiates `T` in `goose_adequacy`.
-/
module

public import Perennial.Proof.sync.atomic
public import Perennial.GooseLang.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace ThreadTokensTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The laws -/

section laws
variable {GF : BundledGFunctors} [ThreadGS GF]

example (m n : Nat) : threadToks (m + n) ⊣⊢@{IProp GF} threadToks m ∗ threadToks n :=
  threadToks_add m n
example : ⊢@{IProp GF} threadToks 0 := threadToks_zero
example (n : Nat) : threadToks n ⊢@{IProp GF} ⌜n < threadBound GF⌝ := threadToks_lt n
example : threadToks (threadBound GF) ⊢@{IProp GF} False := threadBound_elim
example (n : Nat) : Timeless (threadToks n : IProp GF) := inferInstance
example : 1 < threadBound GF := threadBound_gt

end laws

/-! ## A counter of live threads that cannot overflow -/

section counter
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : sync.atomic.Assumptions]

def counterN : Namespace := nroot.@"threads"

/-- The counter invariant: the 32-bit counter `l` holds `n`, and `n` thread
tokens back it (one per registered thread). -/
def counterInv (l : Loc) : IProp GF :=
  iprop(∃ n : Nat, l ↦ (W32 n : w32) ∗ threadToks n)

theorem counter_alloc (l : Loc) :
    l ↦ (W32 0 : w32) ⊢@{IProp GF} |={⊤}=> inv counterN (counterInv l) := by
  iintro Hl
  iapply inv_alloc counterN ⊤ (counterInv l)
  inext
  unfold counterInv
  iexists 0
  iframe
  exact threadToks_zero

/-- Registering a thread (`atomic.AddUint32(l, 1)`) deposits the thread's token
and returns `n + 1` for some `n + 1 < 2^31`: the counter never reaches `2^31`,
provided the thread bound is at most `2^31`. -/
theorem wp_counter_register (Hbound : threadBound GF ≤ 2 ^ 31) (l : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ inv counterN (counterInv l) ∗ threadTok }}
      (App (App (Val (@! sync.atomic.AddUint32)) (Val #l)) (Val #(W32 1)))
    {{ (n : Nat), RET #(W32 (n + 1)); ⌜n + 1 < 2 ^ 31⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hinv, Htok⟩ HΦ
  iapply sync.atomic.wp_AddUint32 l (W32 1) $$ %_ Hpkg
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold counterInv
  icases Hi with ⟨%n, Hl, Hn⟩
  -- the thread's token and the `n` tokens of the invariant bound `n + 1`
  icases threadToks_add_one_lt n $$ [Htok Hn] with ⟨%Hlt, Hn⟩
  · iframe
  iexists (W32 n)
  iframe Hl
  iintro Hl
  imod Hmask with -
  imod Hclose $$ [Hl Hn] with -
  · inext
    iexists n + 1
    rw [show W32 n + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
    iframe
  imodintro
  rw [show W32 n + W32 1 = W32 ((n : Int) + 1) by word]
  iapply HΦ $$ %n
  ipureintro; omega

/-- A thread holding its token forks: it receives the new thread's token too
(here it keeps both), and the forked thread must end with a token (here it is
given one by its own proof, e.g. out of an invariant). Two tokens are then at
hand, so `2 < threadBound GF`. -/
example (e : Expr) (s : Stuckness) (E : CoPset) :
    threadTok ∗ ▷ WP e @ s; ⊤ {{ v, ⌜v.isPanic = false⌝ ∗ (threadTok : IProp GF) }} ⊢
      WP (Fork e) @ s; E {{ _v, threadToks 2 ∗ ⌜2 < threadBound GF⌝ }} := by
  iintro ⟨Htok, He⟩
  iapply wp_fork_tok
  inext
  iintro Hnew
  iframe He
  icases threadToks_add_one_lt 1 $$ [Hnew Htok] with ⟨%Hlt, Htoks⟩
  · iframe
  iframe Htoks
  ipureintro; exact Hlt

end counter

/-! ## Picking the bound at adequacy time

A client whose WP proof assumes `threadBound GF ≤ 2 ^ 31` (e.g. through
`wp_counter_register`) instantiates `goose_adequacy` with `T = 2 ^ 31` and gets
safety for executions along which fewer than `2 ^ 31` threads are live (and of
fewer than `N` steps, for the time-receipt bound `N` of its choice). -/

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext] {GF : BundledGFunctors}

example [GooseGpreS ffi GF] (N : Nat) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      threadBound GF ≤ 2 ^ 31 →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2)) (Hn : n < N)
    (Hthreads : g.threads = 1)
    (Hlive : RealThreadsBelow (2 ^ 31) n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) :=
  goose_adequacy N (2 ^ 31) e σ g φ Hinitg Hinit
    (@fun hG _ HT Hlctx => Hwp (hG := hG) (Nat.le_of_eq HT) Hlctx) n κs t2 σ2 Hsteps Hn
    Hthreads Hlive

end adequacy

end ThreadTokensTest

end Perennial
