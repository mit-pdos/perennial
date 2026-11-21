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
  (`isInit`); they call `Now`, translated and proved over the trusted model of the `go:linkname`
  `runtimeNow` (arbitrary clock readings, `TrustedCode/time.lean`); `Now` reads `startNano`
  and `Local`, so it takes `isPkgInit` too. The model of `runtimeIsBubbled` (true only inside a
  `testing/synctest` bubble) is an arbitrary boolean (`TrustedCode/time.lean`).
* The runtime's timers are modeled in `TrustedCode/time.lean`: its `newTimer` (used by the
  translated `AfterFunc`), `stopTimer` and `resetTimer` (used by the translated `Timer.Stop`
  and `Timer.Reset`), and `NewTimer`, `NewTicker`, `Ticker.Stop` and `Ticker.Reset`. All the
  timer and ticker specs are proved over these models. `Time.After` is translated and proved.
* The runtime's monotonic clock is modeled as runtime state (`TrustedCode/time.lean`, "The
  runtime's monotonic clock"), allocated by the package's initialization: `clockLb n`, the clock
  has reached `n` (below). Only `After` reads it so far: its channel delivers only once the clock
  is `d` past the reading at the call (`time.After.spec`). `runtimeNano`, `runtimeNow` (so `Now`)
  and the other timers keep arbitrary readings, which give nothing about the clock.
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

section clock
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ### The runtime clock

The model of the runtime's monotonic clock (`TrustedCode/time.lean`, "The runtime's monotonic
clock"): a cell holding the clock's value `c`, an `int64`, which only readings change, never
decreasing it. The ghost state is a monotone counter `γ` that follows `c` (`clockInv`), and
`clockLb n` is a lower bound of it: **the clock has reached `n`** (persistent). Values above
`clockMax = 2^63 - 1`, which the clock never exceeds, count as `clockMax` (`clockEnc`): so `clockLb n`
for such an `n` says that the clock has reached `clockMax`, which keeps sums `clockLb (T + d)`
meaningful where Go's timers saturate (`when`). The counter's name is existential in `clockLb`: the
cell has one invariant (its full points-to is in it), so every `clockLb` speaks of the one clock. -/

/-- `int64`'s maximum, the runtime clock's largest value. -/
abbrev clockMax : Int := 2 ^ 63 - 1

/-- The ghost counter's value for the clock value `z`: `z + 2^63`, with values above `clockMax`
counted as `clockMax`. -/
def clockEnc (z : Int) : Nat := (min z clockMax + 2 ^ 63).toNat

theorem clockEnc_mono {a b : Int} (h : a ≤ b) : clockEnc a ≤ clockEnc b := by
  unfold clockEnc; omega

/-- The namespace of the runtime clock's invariant. -/
def clockN : Namespace := nroot .@ "time_runtimeClock"

/-- The invariant of the runtime clock's cell `l`: it holds `c`, which the counter `γ` follows. -/
abbrev clockInv (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ c : w64, heapPointsto l (DFrac.own 1) #c ∗ monoNatAuthOwn γ 1 (clockEnc (sint.Z c)))

/-- `γ` is the counter of the runtime clock (persistent): the global `time.runtimeClock` holds the
address of the cell, whose invariant `γ` follows. -/
def isRuntimeClock (γ : GName) : IProp GF :=
  iprop(∃ l : Loc, globalAddr runtimeClock ↦□ l ∗ inv clockN (clockInv γ l))

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

set_option maxHeartbeats 1000000 in
/-- A reading of the runtime clock at the cell `l` (`runtimeClockRead`, a helper of the trusted
model): some `x`, at least any bound the caller holds (`clockLb n`, `n` capped at `clockMax`). -/
theorem wp_runtimeClockRead (γ : GName) (l : Loc) (n : Int) :
    {{ inv clockN (clockInv (GF := GF) γ l) ∗ monoNatLbOwn γ (clockEnc n) }}
      (App (Val time.runtimeClockRead) (Val #l))
    {{ (x : w64), RET #x; ⌜clockEnc n ≤ clockEnc (sint.Z x)⌝ ∗ monoNatLbOwn γ (clockEnc (sint.Z x)) }} := by
  wp_start as ⟨#Hinv, #Hlb⟩
  unfold runtimeClockRead
  iloeb as IH generalizing HΦ
  -- `c`: the clock now (an atomic add of 0)
  wp_bind (AtomicAdd _ _)
  iinv Hinv with ⟨%c, >Hl, >Hauth⟩
  have Hev : atomicAddEval #c #(W64 0) = some #c := by
    have h := congrFun (go.intoVal_unfold w64) c
    have h0 := congrFun (go.intoVal_unfold w64) (W64 0)
    rw [h, h0]; simp only [atomicAddEval]
    rw [show c + W64 0 = c from by simp, h]
  wp_apply_core wp_atomic_add l #c #(W64 0) #c Hev $$ Hl
  iintro Hl
  ihave %Hnc := monoNatLbOwn_valid γ 1 _ _ $$ Hauth Hlb
  imodintro
  isplitl [Hl Hauth]
  · inext; iexists c; iframe
  wp_pures
  wp_apply wp_ArbitraryInt as %x -
  wp_pures
  wp_if_destruct
  · -- `c ≤ x`: advance the clock to `x`, if it is still `c`
    wp_bind (CmpXchg _ _ _)
    iinv Hinv with ⟨%c', >Hl, >Hauth⟩
    by_cases hc : c' = c
    · subst hc
      wp_apply_core wp_cmpxchg_suc l #c' #x #c' rfl $$ Hl
      iintro Hl
      imod mono_nat_own_update (clockEnc (sint.Z x)) (clockEnc_mono (by word)) $$ Hauth
        with ⟨Hauth, #Hlbx⟩
      imodintro
      isplitl [Hl Hauth]
      · inext; iexists x; iframe
      wp_pures
      iapply HΦ
      iframe Hlbx
      ipureintro
      have := clockEnc_mono (a := sint.Z c') (b := sint.Z x) (by word)
      omega
    · wp_apply_core _root_.Perennial.wp_cmpxchg_fail l (DFrac.own 1) #c' #c #x (fun h => hc (go.intoVal_inj h)) $$ Hl
      iintro Hl
      imodintro
      isplitl [Hl Hauth]
      · inext; iexists c'; iframe
      wp_pures
      iapply IH $$ HΦ
  · iapply IH $$ HΦ

/-- A reading of the runtime clock (`runtimeClockNow`, a helper of the trusted model): some `x`, at
least any bound the caller holds. -/
theorem wp_runtimeClockNow (n : Int) :
    {{ clockLb (GF := GF) n }}
      (App (Val time.runtimeClockNow) (Val #()))
    {{ (x : w64), RET #x; ⌜clockEnc n ≤ clockEnc (sint.Z x)⌝ ∗ clockLb (sint.Z x) }} := by
  wp_start as Hlb
  unfold clockLb
  icases Hlb with ⟨%γ, #Hc, #Hlb⟩
  unfold isRuntimeClock
  icases Hc with ⟨%l, #Hg, #Hinv⟩
  unfold runtimeClockType
  wp_auto
  wp_apply wp_runtimeClockRead γ l n $$ [] as %x ⟨%Hx, #Hlbx⟩
  · iframe #
  iapply HΦ
  isplitr
  · ipureintro; exact Hx
  iexists γ
  iframe #

/-- Waiting for the runtime clock to reach `w` (`runtimeClockWaitUntil`, a helper of the trusted
model): a reading `x ≥ w`. -/
theorem wp_runtimeClockWaitUntil (n : Int) (w : w64) :
    {{ clockLb (GF := GF) n }}
      (App (Val time.runtimeClockWaitUntil) (Val #w))
    {{ (x : w64), RET #x; ⌜sint.Z w ≤ sint.Z x⌝ ∗ clockLb (sint.Z x) }} := by
  wp_start as #Hlb
  unfold runtimeClockWaitUntil
  iloeb as IH generalizing HΦ
  wp_apply wp_runtimeClockNow n $$ Hlb as %x ⟨%-, #Hx⟩
  wp_pures
  wp_if_destruct
  · wp_pures
    iapply HΦ
    iframe Hx
    ipureintro; word
  · iapply IH $$ HΦ

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
the full points-to), while every read gets the value the initialization stored. And the runtime
clock, allocated by the initialization (`asynctimerchan`'s trusted initializer), is in place: a first
bound `clockLb (-2^63)` (every `int64` is at least that), which carries the clock's invariant. -/
abbrev isInit : IProp GF :=
  iprop((∃ v : w64, globalAddr time.startNano ↦□ v) ∗
    (∃ l : Loc, globalAddr time.Local ↦□ l) ∗
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
  ihave ⟨-, -, #Hlb⟩ := isInit_access $$ H
  iexact Hlb

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
points-to (`runtimeTimerCell`, `isRuntimeTimer t`) is what makes `isTimer`, `isFuncTimer` and `isTicker`
unforgeable: no allocation of the program has a cell at that address (`timer` is no field of a
Go type the program can name).

The specs say nothing about *when* (or whether) a value arrives on a timer's or ticker's
channel (a bag of times, `isChanBag`, with no logical content): `Stop` and `Reset` return some
`bool` and change nothing the proof can observe. This over-approximates Go's timers (a stopped
timer's channel delivers nothing; the model allows it), which is sound for safety. -/

/-- The runtime's state of the timer at `t` (persistent): the cell `runtimeTimerAlloc`
allocates, holding what the timer does when it fires (`resetTimer` forks it again). -/
def runtimeTimerCell (t : Loc) (fire : GoFunc) : IProp GF :=
  iprop(structFieldRef time.Timer go!"timer" t ↦□ fire)

instance runtimeTimerCell_persistent (t : Loc) (fire : GoFunc) :
    Persistent (runtimeTimerCell (GF := GF) t fire) := by
  unfold runtimeTimerCell; infer_instance

/-- The firing of the runtime's state of `NewTimer`'s and `NewTicker`'s timers: nothing (their
goroutines send on `C` regardless). -/
def noFire : GoFunc := func.mk BAnon BAnon (Val #())

/-- `t` heads one of the runtime's timers (persistent). -/
def isRuntimeTimer (t : Loc) : IProp GF :=
  iprop(∃ fire : GoFunc, runtimeTimerCell t fire)

instance isRuntimeTimer_persistent (t : Loc) : Persistent (isRuntimeTimer (GF := GF) t) := by
  unfold isRuntimeTimer; infer_instance

/-- `t` is a `*Timer` made by `NewTimer`, whose channel `C` is `ch` (persistent). -/
def isTimer (t : Loc) (ch : Loc) (γ : ChanNames) : IProp GF :=
  iprop(structFieldRef time.Timer go!"C" t ↦□ ch ∗
    structFieldRef time.Timer go!"initTimer" t ↦□ true ∗
    runtimeTimerCell t noFire ∗
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
    runtimeTimerCell t noFire ∗
    isChanBag γ ch (V := time.Time) (fun _ => iprop(True)))

instance isTicker_persistent (t ch : Loc) (γ : ChanNames) :
    Persistent (isTicker (GF := GF) t ch γ) := by
  unfold isTicker; infer_instance

/-- `runtimeTimerAlloc` (a helper of the trusted model): the runtime's state of the timer at
`t`, firing by the closure `fire`. -/
theorem wp_runtimeTimerAlloc (t : Loc) (f x : Binder) (e : Expr) :
    {{ (True : IProp GF) }}
      (App (App (Val time.runtimeTimerAlloc) (Val #t)) (Val (RecV f x e)))
    {{ RET #(); runtimeTimerCell (GF := GF) t (func.mk f x e) }} := by
  wp_start
  unfold runtimeTimerRef runtimeTimerType
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl,
    show RecV f x e = #(func.mk f x e) by rw [go.intoVal_unfold GoFunc]]
  wp_auto
  wp_if_angelic
  iintro %Heq
  subst Heq
  ipersist r
  wp_auto
  iapply HΦ
  unfold runtimeTimerCell
  iexact r

/-- The trusted model of the runtime's `stopTimer`: some `bool`, for one of its timers. -/
theorem wp_stopTimer (t : Loc) :
    {{ isRuntimeTimer (GF := GF) t }}
      (App (Val time.stopTimer.impl) (Val #t))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as Hr
  unfold isRuntimeTimer
  icases Hr with ⟨%fire, #Hr⟩
  unfold runtimeTimerCell runtimeTimerRef runtimeTimerType
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  wp_end

/-- The trusted model of the runtime's `resetTimer`: some `bool`, for one of its timers whose
firing does nothing of its own (`NewTimer`'s, `NewTicker`'s). -/
theorem wp_resetTimer (t : Loc) (w p : w64) :
    {{ runtimeTimerCell (GF := GF) t noFire }}
      (App (App (App (Val time.resetTimer.impl) (Val #t)) (Val #w)) (Val #p))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as Hr
  unfold runtimeTimerCell runtimeTimerRef runtimeTimerType
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_bind (Fork _)
  iapply wp_fork $$ []
  · inext
    unfold noFire
    wp_auto
    itrivial
  inext
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end chan_defs

end time

end Perennial
