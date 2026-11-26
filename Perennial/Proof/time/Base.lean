/-
Shared definitions of the proofs of the Go `time` package: its `isPkgInit` (`isInit`, the global
`startNano`), the `Countable` instance of `time.Time` (for the channel ghost state), the runtime
clock (`clockLb`), and the predicates of the timer and ticker specs (`runtimeTimerCell`,
`isRuntimeTimer`, `isTimer`, `isFuncTimer`, `isTicker`, and the firings `timerCallback`,
`timerFiring`).

Notes on the package's specs:
* The `Time` arithmetic is translated and proved (`Time.wp_Add`, `Time.wp_Sub`,
  `Time.wp_Before`, `Time.wp_Equal`, `wp_Since`, `wp_Until`, ...). The comparisons
  (`Before`, `After`, `Equal`) and the helpers `sec`, `nsec` and `stripMono` return Go's
  functions of the fields (`Time.before`, `Time.after`, `Time.equal`, `Time.secOf`,
  `Time.nsecOf`, `Time.stripMonoOf`, below); the specs of the others (`Add`, `Sub`, `Unix`,
  `UnixNano`, ...) only say that they return some value (no panics; `Sub` saturates, the others
  wrap or fall back to the wall clock). `Since` and `Until` read the global `startNano`, so they take `isPkgInit`
  (`isInit`); they call `Now`, which reads `startNano` and `Local`, so it takes `isPkgInit` too.
* The runtime's clock readings and timers are a Go model (`goose/model/overlay/time`), translated:
  `runtimeNow` and `runtimeNano` read the primitive stub `now` (arbitrary readings,
  `TrustedCode/time.lean`; `runtimeNano`'s are positive), `runtimeIsBubbled` is
  `gomodel.Choose`. A timer (`newTimer`, used by the translated `AfterFunc`; `NewTimer`,
  `NewTicker`) is a goroutine that waits until `runtimeNano` reaches its `when` and fires
  (`startTimer`); `stopTimer` and `resetTimer` (used by the translated `Timer.Stop` and
  `Timer.Reset`) and the `Ticker` methods read the runtime's state of the timer, which the
  primitive stubs `newRuntimeTimer`, `newRuntimeTicker` and `runtimeTimerFire` keep.
* `Duration.Seconds` (over the semantics' IEEE 754 operations) and
  `Duration.String` (`format`, `fmtFrac`, `fmtInt`: a 32-byte buffer, every index in bounds) are
  translated and proved; their specs say only that they return some value.
* The model's runtime clock is the Go global `runtimeClock`, which only `runtimeClockNow` reads and
  advances (to readings of `runtimeNano`): `clockLb n`, the clock has reached `n` (below). Only
  `After` reads it: its channel delivers only once the clock is `d` past the reading at the call
  (`time.After.spec`). `runtimeNano`, `runtimeNow` (so `Now`) and the other timers read `now`
  directly, which gives nothing about the clock.
* `wp_After`, the timer specs, `wp_when` and `wp_AfterFunc` are stated with the channel
  theory's instances, which fix `hlc := HasLC.hasLC` (sections `chan_*`).
  `Pos.Countable time.Time.t` (for the channel ghost state) is defined here.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.internal.gomodel.Base
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

/-! ### A `Time`'s instant, and comparisons

Go's `Time` (`time.go`) keeps an instant in `wall` and `ext`. `wall` holds, from its top bit down,
the flag `hasMonotonic` (bit 63), a 33-bit seconds field (bits 30-62: the seconds since 1885, set
only with the flag) and the nanoseconds (bits 0-29, `nsecMask`). With the flag, `ext` is the
monotonic clock reading; without it, the seconds since January 1, year 1. The functions below are
Go's (`sec`, `nsec`, `stripMono`, `Before`, `After`, `Equal`), on the values of the fields, with
Go's constants spelled out (`hasMonotonic = 1 << 63`, `nsecMask = 1<<30 - 1`, `wallToInternal`,
the seconds from year 1 to 1885); the specs of those methods return them. -/

/-- `t.wall&hasMonotonic != 0`: `t` carries a monotonic clock reading (in `ext`). -/
def Time.hasMono [GooseExts] (t : time.Time) : Bool :=
  decide (t.wall' &&& W64 9223372036854775808 ≠ W64 0)

/-- `t.sec()`: the seconds since January 1, year 1, of `t`'s wall clock: with a monotonic
reading, `wallToInternal` plus `wall`'s seconds field (`wall<<1>>(nsecShift+1)`); otherwise
`ext`. -/
def Time.secOf [GooseExts] (t : time.Time) : w64 :=
  if t.hasMono then W64 59453308800 + (t.wall' <<< W64 1) >>> W64 31 else t.ext'

/-- `t.nsec()`: the nanoseconds of `t`, `int32(wall & nsecMask)` (non-negative, below `2^30`). -/
def Time.nsecOf [GooseExts] (t : time.Time) : w32 :=
  W32 (uint.Z (t.wall' &&& W64 1073741823))

/-- `t.Before(u)`: when both carry a monotonic reading, `t.ext < u.ext`; otherwise `t`'s
`(sec, nsec)` is lexicographically below `u`'s (as signed integers). -/
def Time.before [GooseExts] (t u : time.Time) : Bool :=
  if t.hasMono && u.hasMono then decide (sint.Z t.ext' < sint.Z u.ext')
  else decide (sint.Z t.secOf < sint.Z u.secOf ∨
    (t.secOf = u.secOf ∧ sint.Z t.nsecOf < sint.Z u.nsecOf))

/-- `t.After(u)`: `u.Before(t)` (Go's `After` is `Before` with the operands swapped). -/
def Time.after [GooseExts] (t u : time.Time) : Bool := Time.before u t

/-- `t.Equal(u)`: when both carry a monotonic reading, `t.ext == u.ext`; otherwise the same
`(sec, nsec)`. -/
def Time.equal [GooseExts] (t u : time.Time) : Bool :=
  if t.hasMono && u.hasMono then decide (t.ext' = u.ext')
  else decide (t.secOf = u.secOf ∧ t.nsecOf = u.nsecOf)

/-- `t.stripMono()`'s result: with a monotonic reading, `ext` becomes `t.sec()` and `wall`
keeps only the nanoseconds (the flag and the seconds field cleared); otherwise `t` unchanged.
The result has no monotonic reading (`Time.hasMono_stripMonoOf`). -/
def Time.stripMonoOf [GooseExts] (t : time.Time) : time.Time :=
  if t.hasMono then { t with wall' := t.wall' &&& W64 1073741823, ext' := t.secOf } else t

/-- The flag `hasMonotonic` of a `wall` is its bit 63. -/
theorem wall_hasMono_iff (x : w64) :
    decide (x &&& W64 9223372036854775808 ≠ W64 0) = x.getLsbD 63 := by
  have h : (W64 9223372036854775808 : w64) = BitVec.twoPow 64 63 := by decide
  have h0 : (BitVec.twoPow 64 63 : w64) ≠ 0#64 := by decide
  have hz : (W64 0 : w64) = 0#64 := rfl
  rw [h, hz, BitVec.and_twoPow]
  cases hb : x.getLsbD 63 <;> simp [h0]

theorem Time.hasMono_eq_getLsbD [GooseExts] (t : time.Time) :
    t.hasMono = t.wall'.getLsbD 63 :=
  wall_hasMono_iff t.wall'

/-- Go's test of both flags at once, `t.wall&u.wall&hasMonotonic != 0`. -/
theorem Time.hasMono_and [GooseExts] (t u : time.Time) :
    decide (t.wall' &&& u.wall' &&& W64 9223372036854775808 ≠ W64 0) =
      (t.hasMono && u.hasMono) := by
  rw [wall_hasMono_iff, Time.hasMono_eq_getLsbD, Time.hasMono_eq_getLsbD, BitVec.getLsbD_and]

theorem Time.hasMono_stripMonoOf [GooseExts] (t : time.Time) :
    t.stripMonoOf.hasMono = false := by
  unfold Time.stripMonoOf
  split
  · simp only [Time.hasMono_eq_getLsbD, BitVec.getLsbD_and]
    simp
  · simp_all

/-! The cases of Go's tests of the flags, as the proofs of the methods meet them. -/

section cases
variable [GooseExts] {t u : time.Time}

theorem Time.hasMono_and_true (h : ¬t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    (t.hasMono && u.hasMono) = true := by
  rw [← Time.hasMono_and]; exact decide_eq_true h

theorem Time.hasMono_and_false (h : t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    (t.hasMono && u.hasMono) = false := by
  rw [← Time.hasMono_and, h]; decide

theorem Time.secOf_of_mono (h : ¬t.wall' &&& W64 9223372036854775808 = W64 0) :
    t.secOf = W64 59453308800 + t.wall' <<< W64 1 >>> W64 31 := by
  simp only [Time.secOf, Time.hasMono, ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte]

theorem Time.secOf_of_not_mono (h : t.wall' &&& W64 9223372036854775808 = W64 0) :
    t.secOf = t.ext' := by
  simp only [Time.secOf, Time.hasMono, ne_eq, h, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]

theorem Time.stripMonoOf_of_mono (h : ¬t.wall' &&& W64 9223372036854775808 = W64 0) :
    t.stripMonoOf = ⟨t.wall' &&& W64 1073741823, t.secOf, t.loc'⟩ := by
  simp only [Time.stripMonoOf, Time.hasMono, ne_eq, h, not_false_eq_true, decide_true,
    ↓reduceIte]

theorem Time.stripMonoOf_of_not_mono (h : t.wall' &&& W64 9223372036854775808 = W64 0) :
    t.stripMonoOf = t := by
  simp only [Time.stripMonoOf, Time.hasMono, ne_eq, h, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]

theorem Time.before_of_mono (h : ¬t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.before u = decide (sint.Z t.ext' < sint.Z u.ext') := by
  simp only [Time.before, Time.hasMono_and_true h, ↓reduceIte]

theorem Time.before_of_not_mono (h : t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.before u = decide (sint.Z t.secOf < sint.Z u.secOf ∨
      (t.secOf = u.secOf ∧ sint.Z t.nsecOf < sint.Z u.nsecOf)) := by
  simp only [Time.before, Time.hasMono_and_false h, Bool.false_eq_true, ↓reduceIte]

theorem Time.after_of_mono (h : ¬t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.after u = decide (sint.Z u.ext' < sint.Z t.ext') := by
  simp only [Time.after, Time.before, Bool.and_comm u.hasMono, Time.hasMono_and_true h,
    ↓reduceIte]

theorem Time.after_of_not_mono (h : t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.after u = decide (sint.Z u.secOf < sint.Z t.secOf ∨
      (t.secOf = u.secOf ∧ sint.Z u.nsecOf < sint.Z t.nsecOf)) := by
  simp only [Time.after, Time.before, Bool.and_comm u.hasMono, Time.hasMono_and_false h,
    Bool.false_eq_true, ↓reduceIte, @eq_comm _ u.secOf t.secOf]

theorem Time.equal_of_mono (h : ¬t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.equal u = decide (t.ext' = u.ext') := by
  simp only [Time.equal, Time.hasMono_and_true h, ↓reduceIte]

theorem Time.equal_of_not_mono (h : t.wall' &&& u.wall' &&& W64 9223372036854775808 = W64 0) :
    t.equal u = decide (t.secOf = u.secOf ∧ t.nsecOf = u.nsecOf) := by
  simp only [Time.equal, Time.hasMono_and_false h, Bool.false_eq_true, ↓reduceIte]

end cases

section clock
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ### The runtime clock

The model's runtime clock is the Go global `time.runtimeClock`, an `int64` (`sleep.go`): its
latest reading, which only `runtimeClockNow` reads (an atomic load) and advances (a
compare-and-swap to a reading of `runtimeNano`, never a smaller one). The ghost state is a
monotone counter `γ` that follows its value `c` (`clockInv`), and `clockLb n` is a lower bound of
it: **the clock has reached `n`** (persistent). Values above `clockMax = 2^63 - 1`, which the
clock never exceeds, count as `clockMax` (`clockEnc`): so `clockLb n` for such an `n` says that
the clock has reached `clockMax`, which keeps sums `clockLb (T + d)` meaningful where Go's timers
saturate (`when`). The counter's name is existential in `clockLb`: the global has one invariant
(its full points-to is in it), so every `clockLb` speaks of the one clock. -/

/-- `int64`'s maximum, the runtime clock's largest value. -/
abbrev clockMax : Int := 2 ^ 63 - 1

/-- The ghost counter's value for the clock value `z`: `z + 2^63`, with values above `clockMax`
counted as `clockMax`. -/
def clockEnc (z : Int) : Nat := (min z clockMax + 2 ^ 63).toNat

theorem clockEnc_mono {a b : Int} (h : a ≤ b) : clockEnc a ≤ clockEnc b := by
  unfold clockEnc; omega

/-- The namespace of the runtime clock's invariant. -/
def clockN : Namespace := nroot .@ "time_runtimeClock"

/-- The invariant of the runtime clock: the global `time.runtimeClock` holds `c`, which the
counter `γ` follows; `c` is non-negative (it starts at 0, and every later value is a reading of
`runtimeNano`, which is positive). -/
abbrev clockInv (γ : GName) : IProp GF :=
  iprop(∃ c : w64, globalAddr time.runtimeClock ↦ c ∗ ⌜0 ≤ sint.Z c⌝ ∗
    monoNatAuthOwn γ 1 (clockEnc (sint.Z c)))

/-- `γ` is the counter of the runtime clock (persistent): the global's invariant, which `γ`
follows, and `sync/atomic`'s `isPkgInit` (`runtimeClockNow` uses its `LoadInt64` and
`CompareAndSwapInt64`). -/
def isRuntimeClock (γ : GName) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ inv clockN (clockInv γ))

instance isRuntimeClock_persistent (γ : GName) : Persistent (isRuntimeClock (GF := GF) γ) := by
  unfold isRuntimeClock; infer_instance

/-- **The runtime clock has reached `n`** (persistent; for `n > clockMax`: it has reached
`clockMax`). -/
def clockLb (n : Int) : IProp GF :=
  iprop(∃ γ : GName, isRuntimeClock γ ∗ monoNatLbOwn γ (clockEnc n))

instance clockLb_persistent (n : Int) : Persistent (clockLb (GF := GF) n) := by
  unfold clockLb; infer_instance

/-- A lower bound of the clock is one of every smaller value. -/
theorem clockLb_le {n m : Int} (h : m ≤ n) : clockLb (GF := GF) n ⊢ clockLb m := by
  unfold clockLb
  iintro ⟨%γ, #Hc, #Hlb⟩
  iexists γ
  iframe Hc
  iapply monoNatLbOwn_le _ (clockEnc_mono h) $$ Hlb

/-- The clock at `x` has reached every `n` it is at least. -/
theorem clockLb_enc {n x : Int} (h : clockEnc n ≤ clockEnc x) :
    clockLb (GF := GF) x ⊢ clockLb n := by
  unfold clockLb
  iintro ⟨%γ, #Hc, #Hlb⟩
  iexists γ
  iframe Hc
  iapply monoNatLbOwn_le _ h $$ Hlb

end clock

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- The package invariant: the global `startNano` (`runtimeNano() - 1`, set by the package's
initialization; Go never writes it afterwards) holds a fixed value, which `Now`, `Since` and
`Until` read; and so does the global `Local` (`&localLoc`, set by the initialization), which `Now`
reads. Go programs may assign `time.Local`; this invariant hands out only a persistent
read-only points-to of it, so a program that writes it cannot be verified (its proof would need
the full points-to), while every read gets the value the initialization stored. The same holds of
the global `UTC` (`&utcLoc`), which `Time.Location` reads. And the runtime clock (the global
`runtimeClock`, allocated by the initialization as a zero `int64`) has its invariant: a first
bound `clockLb (-2^63)` (every `int64` is at least that), which carries it. -/
abbrev isInit : IProp GF :=
  iprop((∃ v : w64, globalAddr time.startNano ↦□ v) ∗
    (∃ l : Loc, globalAddr time.Local ↦□ l) ∗
    (∃ l : Loc, globalAddr time.UTC ↦□ l) ∗
    clockLb (-2 ^ 63))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.time :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.time :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.time ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.time

/-- The runtime clock has some reading (a first bound, for a caller's chain of bounds). -/
theorem isPkgInit_clockLb :
    isPkgInit (PROP := IProp GF) pkg_id.time ⊢ clockLb (GF := GF) (-2 ^ 63) := by
  iintro #H
  ihave ⟨-, -, -, #Hlb⟩ := isInit_access $$ H
  iexact Hlb

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
The model's primitive stubs (`TrustedCode/time.lean`) keep the runtime's state, the timer's
firing (a `func()`), as one cell at `structFieldRef time.Timer "timer" t` (`runtimeTimerRef`),
allocated only by `newRuntimeTimer` and `newRuntimeTicker` (so only by the model's `newTimer`
and `NewTicker`): `runtimeTimerFire`, which the models of `stopTimer` and `resetTimer` call,
loads it, so they are stuck on a `Timer` or `Ticker` the program allocated, or a copy. Its
points-to (`runtimeTimerCell`, `isRuntimeTimer t`) is what makes `isTimer`, `isFuncTimer` and
`isTicker` unforgeable: no allocation of the program has a cell at that address (`timer` is no
field of a Go type the program can name).

A timer's firing runs `f(arg, seq, delay)` for the callback `f` of `newTimer` and some `seq`
and `delay` (`timerFunc`), from what the caller provides (`timerCallback`, `timerFiring`); the
firing goroutine (`startTimer`) fires once, or again and again for a ticker, so a ticker's
firing, and that of a timer that may be reset, must be safe to run from nothing.

The specs say nothing about *when* (or whether) a value arrives on a timer's or ticker's
channel (a bag of times, `isChanBag`, with no logical content): `Stop` and `Reset` return some
`bool` and change nothing the proof can observe. This over-approximates Go's timers (a stopped
timer's channel delivers nothing; the model allows it), which is sound for safety. -/

/-- The runtime's state of the timer at `t` (persistent): the cell that `newRuntimeTimer` and
`newRuntimeTicker` allocate, holding the timer's firing (`resetTimer` starts it again). -/
def runtimeTimerCell (t : Loc) (fire : GoFunc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"timer" t ↦□ fire)

instance runtimeTimerCell_persistent (t : Loc) (fire : GoFunc) :
    Persistent (runtimeTimerCell (GF := GF) t fire) := by
  unfold runtimeTimerCell; infer_instance

/-- One call of a timer's callback (persistent): `f(arg, seq, delay)` returns, from `P`. -/
def timerCall (f : GoFunc) (arg : GoInterface) (seq delay : w64) (P : IProp GF) : IProp GF :=
  iprop({{ P }} (App (App (App (Val #f) (Val #arg)) (Val #seq)) (Val #delay)) {{ RET #(); True }})

/-- One call of a timer's callback (persistent): `f(arg, seq, delay)` returns, from `P`. -/
def timerCallback (f : GoFunc) (arg : GoInterface) (P : IProp GF) : IProp GF :=
  iprop(∀ seq : w64, ∀ delay : w64, timerCall f arg seq delay P)

instance timerCallback_persistent (f : GoFunc) (arg : GoInterface) (P : IProp GF) :
    Persistent (timerCallback f arg P) := by
  unfold timerCallback timerCall; infer_instance

/-- A timer's firing (persistent): `fire()` returns, from `P`. -/
def timerFiring (fire : GoFunc) (P : IProp GF) : IProp GF :=
  iprop({{ P }} (App (Val #fire) (Val #())) {{ RET #(); True }})

instance timerFiring_persistent (fire : GoFunc) (P : IProp GF) :
    Persistent (timerFiring fire P) := by
  unfold timerFiring; infer_instance

/-- `t` heads one of the runtime's timers (persistent). -/
def isRuntimeTimer (t : Loc) : IProp GF :=
  iprop(∃ fire : GoFunc, runtimeTimerCell t fire)

instance isRuntimeTimer_persistent (t : Loc) : Persistent (isRuntimeTimer (GF := GF) t) := by
  unfold isRuntimeTimer; infer_instance

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent): one of the
runtime's timers, whose firing is safe to run from nothing (it sends on `ch`; `Reset` starts it
again). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    structFieldRef time.Timer go!"initTimer" t ↦□ true ∗
    (∃ fire : GoFunc, runtimeTimerCell t fire ∗ timerFiring fire iprop(True)) ∗
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

/-- `t` is a `*Ticker` made by `NewTicker`, whose channel `C` is `ch` (persistent): as
`isTimer`. -/
def isTicker (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Ticker go!"C" t ↦□ ch ∗
    structFieldRef time.Ticker go!"initTicker" t ↦□ true ∗
    (∃ fire : GoFunc, runtimeTimerCell t fire ∗ timerFiring fire iprop(True)) ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTicker_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTicker (GF := GF) t ch γ) := by
  unfold isTicker; infer_instance

/-- `runtimeTimerAlloc` (a helper of the primitive stubs `newRuntimeTimer` and
`newRuntimeTicker`, not a Go function): the runtime's state of the timer at `t`, holding the
firing `fire`. -/
theorem wp_runtimeTimerAlloc (t : Loc) (fire : GoFunc) :
    {{ (True : IProp GF) }}
      (App (App (Val time.runtimeTimerAlloc) (Val #t)) (Val #fire))
    {{ RET #(); runtimeTimerCell (GF := GF) t fire }} := by
  wp_start
  unfold runtimeTimerRef runtimeTimerType
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_if_angelic
  iintro %Heq
  subst Heq
  ipersist r
  wp_auto
  iapply HΦ
  unfold runtimeTimerCell
  iexact r

end chan_defs

end time

end Perennial
