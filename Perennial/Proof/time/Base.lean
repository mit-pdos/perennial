/-
Shared definitions of the proofs of the Go `time` package: its `isPkgInit` (`isInit`, the global
`startNano`), the `Countable` instance of `time.Time` (for the channel ghost state), the
predicates of the timer and ticker specs (`isRuntimeTimer`, `isTimer`, `isFuncTimer`, `isTicker`),
and the spec of the trusted model's `arbitraryTime` (not a Go function).

Notes on the package's specs:
* The `Time` arithmetic is translated and proved (`Time.wp_Add`, `Time.wp_Sub`,
  `Time.wp_Before`, `Time.wp_Equal`, `wp_Since`, `wp_Until`, ...); the specs only say that
  these return some value (no panics; `Sub` saturates, the others wrap or fall back to the wall
  clock). `Since` and `Until` read the global `startNano`, so they take `isPkgInit`
  (`isInit`); they call `Now`, whose spec `wp_Now` is an axiom (`Now` reads the clock through
  the `go:linkname` `runtimeNow`). The model of `runtimeIsBubbled` (true only inside a
  `testing/synctest` bubble) is an arbitrary boolean (`TrustedCode/time.lean`).
* The runtime's timers are modeled in `TrustedCode/time.lean`: its `newTimer` (used by the
  translated `AfterFunc`), `stopTimer` and `resetTimer` (used by the translated `Timer.Stop`
  and `Timer.Reset`), and `NewTimer`, `NewTicker`, `Ticker.Stop` and `Ticker.Reset`. All the
  timer and ticker specs are proved over these models. `Time.After` is translated and proved.
* `wp_After`, the timer specs, `wp_when` and `wp_AfterFunc` are stated with the channel
  theory's instances, which fix `hlc := HasLC.hasLC` (sections `chan_*`).
  `Pos.Countable time.Time.t` (for the channel ghost state) is defined here.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Code.time
public import Perennial.GeneratedProof.time
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace time

instance Time.countable [GooseExts] : Pos.Countable time.Time :=
  .ofInjective (fun t => Pos.Countable.encode (t.wall', t.ext', t.loc'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- The package invariant: the global `startNano` (`runtimeNano() - 1`, set by the package's
initialization; Go never writes it afterwards) holds a fixed value. `Since` and `Until` read
it. -/
abbrev isInit : IProp GF :=
  iprop(∃ v : w64, globalAddr time.startNano ↦□ v)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.time :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.time :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.time ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.time

set_option goose.wp.extras true in
/-- `arbitraryTime` (a helper of the trusted model of the runtime's timers,
`TrustedCode/time.lean`, not a Go function): some time. -/
theorem wp_arbitraryTime :
    {{ (True : IProp GF) }}
      (App (Val time.arbitraryTime) (Val #()))
    {{ (t : time.Time), RET #t; True }} := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_auto
  wp_end

end wps


section chan_defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-! ### The runtime's timers

The runtime allocates each of its timers as a `runtime.timeTimer`: the `Timer`'s fields (or the
`Ticker`'s, which are their prefix) followed by the runtime's state, which `stopTimer` and
`resetTimer` use. A copy of a `Timer` or `Ticker` (`*u = *t`) copies only the fields, and Go's
`stopTimer`/`resetTimer` on it treat the memory after `u` as timer state (go1.27.3:
`u.Reset(time.Second)` on a copied `Ticker` dies with "fatal error: unlock of unlocked lock").
The models in `TrustedCode/time.lean` keep the runtime's state as one cell at
`structFieldRef time.Timer "timer" t` (`runtimeTimerRef`), allocated only by the models of the
runtime's `newTimer`, `NewTimer` and `NewTicker`: the models of `stopTimer` and `resetTimer`
load it, so they are stuck on a `Timer` or `Ticker` the program allocated, or a copy. Its
points-to, `isRuntimeTimer t`, is what makes `isTimer`, `isFuncTimer` and `isTicker`
unforgeable: no allocation of the program has a cell at that address (`timer` is no field of a
Go type the program can name).

The specs say nothing about *when* (or whether) a value arrives on a timer's or ticker's
channel (a bag of times, `isChanBag`, with no logical content): `Stop` and `Reset` return some
`bool` and change nothing the proof can observe. This over-approximates Go's timers (a stopped
timer's channel delivers nothing; the model allows it), which is sound for safety. -/

/-- `t` heads one of the runtime's timers (persistent): the cell of its runtime state. -/
def isRuntimeTimer (t : Loc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"timer" t ↦□ true)

instance isRuntimeTimer_persistent (t : Loc) : Persistent (isRuntimeTimer (GF := GF) t) := by
  unfold isRuntimeTimer; infer_instance

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    structFieldRef time.Timer go!"initTimer" t ↦□ true ∗
    isRuntimeTimer t ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTimer_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTimer (GF := GF) t ch γ) := by
  unfold isTimer; infer_instance

/-- `t` is a `*Timer` made by `AfterFunc` (persistent): `initTimer` is set, and `t` heads one
of the runtime's timers. (`wp_AfterFunc` withholds `C`, which no caller needs.) -/
def isFuncTimer (t : Loc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"initTimer" t ↦□ true ∗ isRuntimeTimer t)

instance isFuncTimer_persistent (t : Loc) : Persistent (isFuncTimer (GF := GF) t) := by
  unfold isFuncTimer; infer_instance

/-- `t` is a `*Ticker` made by `NewTicker`, whose channel `C` is `ch` (persistent). -/
def isTicker (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Ticker go!"C" t ↦□ ch ∗
    structFieldRef time.Ticker go!"initTicker" t ↦□ true ∗
    isRuntimeTimer t ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTicker_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTicker (GF := GF) t ch γ) := by
  unfold isTicker; infer_instance

/-- `runtimeTimerAlloc` (a helper of the trusted model): the runtime's state of the timer at
`t`. -/
theorem wp_runtimeTimerAlloc (t : Loc) :
    {{ (True : IProp GF) }}
      (App (Val time.runtimeTimerAlloc) (Val #t))
    {{ RET #(); isRuntimeTimer (GF := GF) t }} := by
  wp_start
  unfold runtimeTimerRef
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_if_angelic
  iintro %Heq
  subst Heq
  ipersist r
  wp_auto
  iapply HΦ
  unfold isRuntimeTimer
  iexact r

/-- The trusted model of the runtime's `stopTimer`: some `bool`, for one of its timers. -/
theorem wp_stopTimer (t : Loc) :
    {{ isRuntimeTimer (GF := GF) t }}
      (App (Val time.stopTimer.impl) (Val #t))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as Hr
  unfold isRuntimeTimer runtimeTimerRef
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  wp_end

/-- The trusted model of the runtime's `resetTimer`: some `bool`, for one of its timers. -/
theorem wp_resetTimer (t : Loc) (w p : w64) :
    {{ isRuntimeTimer (GF := GF) t }}
      (App (App (App (Val time.resetTimer.impl) (Val #t)) (Val #w)) (Val #p))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as Hr
  unfold isRuntimeTimer runtimeTimerRef
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end chan_defs

end time

end Perennial
