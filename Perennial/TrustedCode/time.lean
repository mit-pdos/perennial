/-
Trusted model of `time` (namespace `time`, as the generated package): the primitive stubs of its Go
model (`goose/model/overlay/time`, `Perennial/Code/time.toml`). The timers, the clock readings,
`NewTimer`, `NewTicker`, `After` and the `Ticker` methods are that model's Go, translated; what is
left here is the runtime's clock and sleep (`now`, `Sleep`: bodyless functions of `time` that the
runtime defines) and the runtime's state of a timer (`newRuntimeTimer`, `newRuntimeTicker`,
`runtimeTimerFire`: additions of the model, whose Go bodies serve gc builds).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial
noncomputable section

namespace time
section code
variable [GooseExts] [GoGlobalContext]

/-- `now()` (`time.go`, defined by the runtime: `time_now`) reads the wall clock, as seconds and
nanoseconds since the Unix epoch, and the monotonic clock; modeled as arbitrary values of its
result types `(int64, int32, int64)`, which include every result of the runtime (there `nsec` is
below 1e9 and `mono` is `nanotime()`). -/
def now.impl : val :=
  λ: <>, Pair (Pair ArbitraryInt (Convert go.int64 go.int32 ArbitraryInt)) ArbitraryInt

/-- `Sleep(d)` (defined by the runtime: `timeSleep`) parks the goroutine until the monotonic clock
has advanced by `d`; modeled as returning at once. No reading of the model's clocks is tied to the
real one (`now` is arbitrary), so every schedule of Go's sleeping goroutine, which resumes at some
later point, is one of the model's. -/
def Sleep.impl : val :=
  λ: "d", #()

/-- The type of the runtime's state of a timer in the model: its firing, a `func()`. -/
def runtimeTimerType : go.GoType := go.GoType.FunctionType (go.signature.Signature [] false [])

/-- The address of the runtime's state of the timer whose `Timer` (or `Ticker`) is at `t`. The
runtime allocates a timer as a `runtime.timeTimer`, the `Timer`'s fields followed by the
embedded `timer`; this is that `timer`, as one cell, which holds the timer's firing.

Soundness rests on the choice of this address, not only on `timer` being no field of `Timer` (no
Go type the program can name has it): `structFieldRef … "timer" t` must be an address that no
allocation of the program has, so that `runtimeTimerAlloc` can always place the cell there (its
`AngelicExit` is then only on the model's own choice of address, the `alloc_struct` scheme) and
`runtimeTimerFire` is stuck at every `Timer` or `Ticker` the runtime did not make (a zero value or a
copy, where Go's `stopTimer`/`resetTimer` read memory that is not a timer). -/
def runtimeTimerRef : val :=
  λ: "t", StructFieldRef (go.Named go!"time.Timer" []) go!"timer" "t"

/-- Allocates the runtime's state of the timer at `t`, holding `fire`: a fresh cell, kept only if
the allocation lands at `runtimeTimerRef t` (`AngelicExit` otherwise). This is sound because
`runtimeTimerRef t` is chosen to be an address that no allocation of the program has (see
`runtimeTimerRef`; that no Go type has a field `timer` is not enough by itself): some choice of
the model's allocator always lands there, so the exit discards no behaviour of Go's. -/
def runtimeTimerAlloc : val :=
  λ: "t" "fire",
    let: "r" := GoAlloc runtimeTimerType "fire" in
    if: "r" =⟨go.PointerType runtimeTimerType⟩ runtimeTimerRef "t" then #() else AngelicExit #()

/-- `newRuntimeTimer(fire)` (a primitive stub of the model): a new `*Timer` with `initTimer` set
(and no channel), as the runtime's `newTimer` allocates it, followed by the runtime's state of the
timer, holding `fire` (`runtimeTimerAlloc`). -/
def newRuntimeTimer.impl : val :=
  λ: "fire",
    let: "t" := GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ])) in
    runtimeTimerAlloc "t" "fire" ;;
    "t"

/-- `newRuntimeTicker(fire)` (a primitive stub of the model): `newRuntimeTimer` for a `*Ticker`
with `initTicker` set (`Ticker`'s fields are `Timer`'s, and the runtime allocates a ticker as a
timer). -/
def newRuntimeTicker.impl : val :=
  λ: "fire",
    let: "t" := GoAlloc (go.Named go!"time.Ticker" [])
      (CompositeLiteral (go.Named go!"time.Ticker" []) (LiteralValue [
        KeyedElement (some (KeyField go!"initTicker")) (ElementExpression go.bool #true)
      ])) in
    runtimeTimerAlloc "t" "fire" ;;
    "t"

/-- `runtimeTimerFire(p)` (a primitive stub of the model): the firing held by the runtime's state
of the timer at `p`; stuck unless `newRuntimeTimer` or `newRuntimeTicker` made it (at a `Timer`
the program allocated, or a copy, where Go's `stopTimer`/`resetTimer` read memory that is not a
timer). -/
def runtimeTimerFire.impl : val :=
  λ: "p", ![runtimeTimerType] (runtimeTimerRef "p")

end code
end time

end

end Perennial
