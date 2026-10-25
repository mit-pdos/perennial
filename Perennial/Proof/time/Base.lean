/-
Shared definitions of the proofs of the Go `time` package: its `isPkgInit` (`isInit`, the global
`startNano`), the `Countable` instance of `time.Time` (for the channel ghost state), the
predicates of the timer specs (`newTimerMade`, `isTimer`, `isFuncTimer`), and the spec of the
trusted model's `arbitraryTime` (not a Go function).

Notes on the package's specs:
* The `Time` arithmetic is translated and proved (`Time.wp_Add`, `Time.wp_Sub`,
  `Time.wp_Before`, `Time.wp_Equal`, `wp_Since`, `wp_Until`, ...); the specs only say that
  these return some value (no panics; `Sub` saturates, the others wrap or fall back to the wall
  clock). `Since` and `Until` read the global `startNano`, so they take `isPkgInit`
  (`isInit`); they call `Now`, whose spec `wp_Now` is an axiom (`Now` reads the clock through
  the `go:linkname` `runtimeNow`). The model of `runtimeIsBubbled` (true only inside a
  `testing/synctest` bubble) is an arbitrary boolean (`TrustedCode/time.lean`).
* `AfterFunc` is translated; the runtime's `newTimer` (a fresh `*Timer` and a goroutine that
  calls the callback) is modeled in `TrustedCode/time.lean`. `Stop` of its timers is (a case
  of) the axiom `Timer.Stop.wp_proof`.
* `NewTicker`, `Ticker.Stop` and `Ticker.Reset` are modeled in `TrustedCode/time.lean` (Go
  reinterprets the runtime's `*Timer` as a `*Ticker` through `unsafe.Pointer`); their specs are
  proved over the model (`isTicker`). `Time.After` is translated and proved.
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

instance Time.countable [FfiSyntax] : Pos.Countable time.Time :=
  .ofInjective (fun t => Pos.Countable.encode (t.wall', t.ext', t.loc'))
    (by rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; have h := Pos.encode_inj h; simp_all)

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- `t` was returned by `NewTimer` (opaque): the runtime allocated it as the head of one of its
timers (`runtime.timeTimer`: the `Timer`'s fields followed by the runtime's state) and set its
`initTimer`, so that `Stop` and `Reset` may call the runtime's `stopTimer` and `resetTimer` on
it. Only the axiom `wp_NewTimer` provides it; no points-to gives it, so a `Timer` the program
allocates, or a copy of one, is not one. Its meaning is fixed by the axioms that mention it
(`wp_NewTimer`, `Timer.wp_Stop`, `Timer.wp_Reset`); nothing else is proved about it (the value
`False` only shows that the type is inhabited: Lean does not unfold an `opaque`). -/
opaque newTimerMade {GF : BundledGFunctors} (t : Loc) : IProp GF := iprop(False)

section chan_defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-! ### Timers (the trust boundary: `NewTimer`, `Timer.Stop` and `Timer.Reset` are not
translated; the runtime's timers are not modelled)

A `*Timer` from `NewTimer` is `isTimer t ch γ`: its `C` field holds, for good, a channel `ch` on
which a receive may yield some time (a bag of times, `isChanBag`, with no logical content), and
`t` is one of the runtime's timers (`newTimerMade t`). The specs say nothing about *when* (or
whether) a value arrives: `Stop` and `Reset` return some `bool` and change nothing the proof can
observe. This over-approximates Go's timers (a stopped timer's channel delivers nothing; the
model allows it), which is sound for safety.

`newTimerMade t` is what makes `isTimer` unforgeable. The points-to of `C` alone is not: a
program can allocate its own `Timer` and copy `C` into it (`u := new(time.Timer); u.C = t.C`),
and Go's `Stop` and `Reset` on that `u` panic ("uninitialized Timer"); with the points-to of
`initTimer` as well, it could copy the whole struct (`*u = *t`), and the runtime's `stopTimer`
and `resetTimer` would treat the memory after `u` as their timer state. -/

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) ∗
    □ newTimerMade (GF := GF) t)

instance isTimer_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTimer (GF := GF) t ch γ) := by
  unfold isTimer; infer_instance

/-! ### `AfterFunc` timers

`AfterFunc(d, f)` is translated: it calls the runtime's `newTimer` (modeled in
`TrustedCode/time.lean` as a fresh `*Timer` with `initTimer` set and a goroutine that calls the
callback) with `goFunc`, which runs `f` in a new goroutine. `Stop` is not translated (it calls
the runtime's `stopTimer`); `Timer.Stop.spec` covers its timers (`Timer.wp_Stop_func`). -/

/-- `t` is a `*Timer` made by `AfterFunc` (persistent): `initTimer` is set. Only `wp_AfterFunc`
gives it out (with no access to `C`, see `Timer.wp_Stop_func`). -/
def isFuncTimer (t : Loc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"initTimer" t ↦□ true)

instance isFuncTimer_persistent (t : Loc) : Persistent (isFuncTimer (GF := GF) t) := by
  unfold isFuncTimer; infer_instance

/-! ### Tickers

`NewTicker`, `Ticker.Stop` and `Ticker.Reset` are modeled in `TrustedCode/time.lean` (Go
reinterprets the runtime's `*Timer` as a `*Ticker` through `unsafe.Pointer`): a fresh `*Ticker`
with `initTicker` set, and a goroutine that sends arbitrary times on its channel. Like a timer's,
a ticker's channel may yield some time at a receive (a bag of times with no logical content), or
nothing; `Stop` and `Reset` change nothing the proof can observe. -/

/-- `t` is a `*Ticker` made by `NewTicker`, whose channel `C` is `ch` (persistent). -/
def isTicker (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Ticker go!"C" t ↦□ ch ∗
    structFieldRef time.Ticker go!"initTicker" t ↦□ true ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTicker_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTicker (GF := GF) t ch γ) := by
  unfold isTicker; infer_instance

end chan_defs

end time

end Perennial
