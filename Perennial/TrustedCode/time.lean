/-
Trusted model of `time` (namespace `time`, as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace time
section code
variable [FfiSyntax] [GoGlobalContext]

def runtimeNano.impl : val :=
  λ: <>, ArbitraryInt

/-- Model of the runtime's `stopTimer` (`go:linkname`), called by the translated `(*Timer).Stop`:
some `bool`. The runtime also stops the timer; the model does not (the model of `NewTimer` may
deliver times on `C` at any point regardless), which only adds executions. -/
def stopTimer.impl : val :=
  λ: "t", ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- Model of the runtime's `resetTimer` (`go:linkname`), called by the translated
`(*Timer).Reset`: some `bool`. The runtime also reschedules the timer, which then fires (again)
on the channel given to `newTimer`; the model of `NewTimer` already sends on that channel
unboundedly often, so `resetTimer` needs no effect of its own. -/
def resetTimer.impl : val :=
  λ: "t" "when" "period", ArbitraryInt =⟨go.int64⟩ #(W64 0)

def arbitraryTime : val :=
  λ: <>,
     -- generate a simple non-monotonic time without any nanoseconds and
     -- location of UTC
     let: "wall_seconds" := ArbitraryInt in
     CompositeLiteral (go.Named go!"time.Time" []) (LiteralValue [
        KeyedElement (some (KeyField go!"wall")) (ElementExpression go.uint64 #(W64 0)),
        KeyedElement (some (KeyField go!"ext")) (ElementExpression go.int64 "wall_seconds"),
        KeyedElement (some (KeyField go!"loc")) (ElementExpression «unsafe».Pointer #null)
     ])

/-- Model of `NewTimer`. Go's body is

```go
c := make(chan Time, 1)
t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
t.C = c
return t
```

where the runtime's `newTimer` allocates the `*Timer` (with `initTimer` set) and, when
`syncTimer(c) != nil` (GODEBUG `asynctimerchan=0`, the default since Go 1.23), makes `c`
synchronous: `cap(c)` and `len(c)` are 0 and no stale value is delivered. Each time the timer
fires (once, and again after each `Reset`), the runtime calls `sendTime`, a non-blocking send
of the current time on `c`.

`NewTimer` itself is trusted (not only `newTimer`) because of that change to `c`. Goose
translates the body above (with `newTimer` and `syncTimer` trusted), but in goose's channel
semantics the translated `make(chan Time, 1)` always has `cap(t.C) = 1`, where Go with
`asynctimerchan=0` reports 0. Such a model has fewer executions than Go. No model of the
linkname stub `newTimer` can make an existing channel synchronous. The model:

* makes `c` with capacity 0 or 1, chosen arbitrarily (the synchronous and the asynchronous
  timer channel);
* forks a goroutine that sends arbitrary times (`arbitraryTime`) on `c` forever, ignoring `d`:
  every firing, whenever it happens and however often `Reset` re-arms the timer, is one of
  these sends; a send that never completes is a firing whose non-blocking send dropped the
  value or a firing that never happened. It allows more (values after `Stop`, stale values);
* returns a fresh `*Timer` holding `c` in `C` and `true` in `initTimer`. -/
def NewTimer.impl : val :=
  λ: "d",
    let: "ch" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() (if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then #(W64 0) else #(W64 1)) in
    Fork (exceptionDo (for: (λ: <>, #true) ; (λ: <>, #()) := λ: <>,
      do: chan.send (go.Named go!"time.Time" []) "ch" (arbitraryTime #()))) ;;
    GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"C"))
          (ElementExpression (go.ChannelType go.sendrecv (go.Named go!"time.Time" [])) "ch"),
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ]))

/-- Model of `Since(t)`: some duration. Go's body is

```go
if t.wall&hasMonotonic != 0 && !runtimeIsBubbled() {
	return subMono(runtimeNano()-startNano, t.ext)
}
return Now().Sub(t)
```

and neither branch panics. Goose translates it and its callees (`subMono`, `Now`, `Time.Sub`,
`Time.Add`, ...) once the linkname stubs `runtimeIsBubbled` and `runtimeNow` are trusted.
Even so, the translation cannot be verified here:
* it reads the package variables `startNano` and `Local`, owned only through `time`'s package
  initialization, whose proof `wp_initialize'` is blocked by opaque initializers (`Local'init`,
  ...);
* the slow path `Now().Sub(t)` calls `Time.Add`, whose body uses `&^` (`GoBitClear`, with no
  semantics) and the untranslated `addSec` and `stripMono` (see `Time.wp_Add`). -/
def Since.impl : val :=
  λ: "t", ArbitraryInt

def Sleep.impl : val :=
  λ: "d", #()

end code
end time

end Perennial
