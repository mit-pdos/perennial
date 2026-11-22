/-
Scratch, NOT part of the build (it is outside every lake glob, and imports
nothing): the properties Perennial must be able to prove about the examples in
`labels/` and `recovers/` once the semantics for labeled break/continue and for
`recover()` in a deferred named function or method exist. Every `sorry` here is
a target, not a proof.

Conventions are those of the semantics test proofs
(`Perennial/{Spec,Proof}/github_com/mit_pdos/perennial/goose/testdata/examples/semantics/`):
the examples are expected to move into package `semantics`, so `@! f` is that
package's `f`, `TestFunOk name` is "`name()` returns `true`" from
`semantics/Base.lean`, and the context is that section's variables
(`[GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hG : HeapGS hlc GF}
[go.Semantics] [semantics.Assumptions]`). A method `catcher.catch` is written
`@! catcher.catch` loosely; the real name is whatever goose's method naming gives.
-/

namespace Perennial.PendingLabelsRecover

/-! ## (A) Labeled break / continue

Every `test*` function: `TestFunOk test*` (returns `true`). The value-level
statements below are what each `test*` reduces to, and are the specs a proof
would prove first. -/

-- `continue L` to an outer for with a post statement (the post runs).
theorem labeledContinue_spec :
    {{ (True : IProp GF) }} App (Val (@! labeledContinue)) (Val #())
    {{ RET #(W64 10); True }} := by sorry

-- `break L` from an inner for.
theorem labeledBreak_spec :
    {{ (True : IProp GF) }} App (Val (@! labeledBreak)) (Val #())
    {{ RET #(W64 23); True }} := by sorry

-- `break L` from a switch in a labeled for; the unlabeled `break` ends only the switch.
theorem breakLoopFromSwitch_spec :
    {{ (True : IProp GF) }} App (Val (@! breakLoopFromSwitch)) (Val #())
    {{ RET #(W64 2); True }} := by sorry

-- doPrintf shape: `continue L` through switch/switch/inner for (whose post must NOT run).
theorem continueFromNestedSwitch_spec :
    {{ (True : IProp GF) }} App (Val (@! continueFromNestedSwitch)) (Val #())
    {{ RET #(W64 3); True }} := by sorry

-- labeled switch: `break L` from a for inside a case skips the rest of the case.
theorem labeledSwitch_spec (x : w64) :
    {{ (True : IProp GF) }} App (Val (@! labeledSwitch)) (Val #x)
    {{ RET #(if x = W64 1 then W64 2 else W64 50); True }} := by sorry

-- labeled select (buffered channel holding 1).
theorem labeledSelect_spec :
    {{ (True : IProp GF) }} App (Val (@! labeledSelect)) (Val #())
    {{ RET #(W64 2); True }} := by sorry

-- labeled range over a slice / a map (order-independent result) / an int / a func.
theorem rangeSliceLabeled_spec :
    {{ (True : IProp GF) }} App (Val (@! rangeSliceLabeled)) (Val #()) {{ RET #(W64 6); True }} := by sorry
theorem rangeMapLabeled_spec :
    {{ (True : IProp GF) }} App (Val (@! rangeMapLabeled)) (Val #()) {{ RET #(W64 4); True }} := by sorry
theorem rangeMapBreakLabeled_spec :
    {{ (True : IProp GF) }} App (Val (@! rangeMapBreakLabeled)) (Val #()) {{ RET #(W64 1); True }} := by sorry
theorem rangeIntLabeled_spec :
    {{ (True : IProp GF) }} App (Val (@! rangeIntLabeled)) (Val #()) {{ RET #(W64 6); True }} := by sorry
-- 6*100 + 7: the sum, and the number of yield calls (break L makes yield return false once,
-- and `seq` stops calling it; `seq`'s own label L does not interfere).
theorem rangeFuncLabeled_spec :
    {{ (True : IProp GF) }} App (Val (@! rangeFuncLabeled)) (Val #()) {{ RET #(W64 607); True }} := by sorry
-- `break L` aimed at an outer for, from inside a range-over-func: the labeled
-- outcome must leave `func.forRange` (through its `exit` cell) unchanged.
theorem breakThroughRangeFunc_spec :
    {{ (True : IProp GF) }} App (Val (@! breakThroughRangeFunc)) (Val #()) {{ RET #(W64 4); True }} := by sorry

-- `return` from inside a labeled loop.
theorem returnInLabeledLoop_spec :
    {{ (True : IProp GF) }} App (Val (@! returnInLabeledLoop)) (Val #()) {{ RET #(W64 23); True }} := by sorry

-- closures capture their own iteration's `i` across `continue L` (the post
-- statement updates the next iteration's copy).
theorem closureAcrossContinue_spec :
    {{ (True : IProp GF) }} App (Val (@! closureAcrossContinue)) (Val #()) {{ RET #(W64 4); True }} := by sorry

-- the same label in a function and a function literal inside it.
theorem sameLabelNested_spec :
    {{ (True : IProp GF) }} App (Val (@! sameLabelNested)) (Val #()) {{ RET #(W64 209); True }} := by sorry

-- The general one: needs a loop invariant across `continue L`, i.e. a `wp_for`
-- rule whose body may end in the labeled outcome for its own label.
theorem countPairs_spec (n : w64) (hn : uint.Z n < 2 ^ 32) :
    {{ (True : IProp GF) }} App (Val (@! countPairs)) (Val #n)
    {{ RET #(W64 (uint.Z n * (uint.Z n - 1) / 2)); True }} := by sorry

-- doPrintf shape (`continue formatLoop`, `break simpleFormat`).
theorem miniPrintf_spec :
    {{ (True : IProp GF) }} App (Val (@! miniPrintf)) (Val #go!"x%-vy%3z%")
    {{ RET (#go!"xVy!3z!", #(W64 1)); True }} := by sorry

/-! ## (B) recover() in a function or method called by defer -/

-- A deferred method recovers 7 and stores it in the named result.
theorem methodRecover_spec :
    {{ (True : IProp GF) }} App (Val (@! methodRecover)) (Val #()) {{ RET #(W64 7); True }} := by sorry

-- A deferred top-level function recovers.
theorem topRecover_spec :
    {{ (True : IProp GF) }} App (Val (@! topRecover)) (Val #()) {{ RET #true; True }} := by sorry

-- Recover and re-panic: the inner function panics with 6 (5 + 1) ...
theorem repanicInner_spec (c : Loc) (s : w64) :
    ∀ Φ : val → IProp GF,
      (c.[catcher.t, "seen"] ↦ s) -∗
      ((c.[catcher.t, "seen"] ↦ (s + W64 1)) -∗ Φ (PanicV #(interface.mkOk go.uint64 #(W64 6)))) -∗
      WP (App (Val (@! repanicInner)) (Val #c)) {{ Φ }} := by sorry
-- ... which the caller's deferred literal recovers: 6*10 + 1.
theorem repanic_spec :
    {{ (True : IProp GF) }} App (Val (@! repanic)) (Val #()) {{ RET #(W64 61); True }} := by sorry

-- recover() is nil when not panicking; the function returns normally.
theorem recoverNotPanicking_spec :
    {{ (True : IProp GF) }} App (Val (@! recoverNotPanicking)) (Val #()) {{ RET #true; True }} := by sorry

-- `f := c.catch; defer f(&x)`: Go returns 9. Under the plan's proposal A this is
-- NOT expected to be provable (goose cannot see that `f` recovers, the ordinary
-- `catch` is stuck), which is sound. What must never be provable is the
-- "recover gave nil" behaviour, i.e. the panic escaping:
theorem methodValueRecover_go :   -- Go's behaviour; provable only with runtime panic state (plan's B)
    {{ (True : IProp GF) }} App (Val (@! methodValueRecover)) (Val #()) {{ RET #(W64 9); True }} := by sorry
/- MUST NOT be provable (it is false in Go):
   ∀ Φ, Φ (PanicV #(interface.mkOk go.uint64 #(W64 9))) ⊢
          WP (App (Val (@! methodValueRecover)) (Val #())) {{ Φ }}  -/

-- A direct, non-deferred call: Go's recover() returns nil and the call is a no-op.
-- Under proposal A (`recover()` in the ordinary `catch` is stuck) this is NOT
-- provable; that is the incompleteness decision point 6 accepts.
theorem directCall_go :
    {{ (True : IProp GF) }} App (Val (@! directCall)) (Val #()) {{ RET #true; True }} := by sorry

-- A deferred literal calling the recovering method: its recover() is nil in Go,
-- the panic continues and the outer literal recovers it (101). Also NOT
-- provable under proposal A (the direct `c.catch` call is stuck); it would be
-- with "nil in non-deferred F", which is unsound for `methodValueRecover`.
theorem helperInDeferredLiteral_go :
    {{ (True : IProp GF) }} App (Val (@! helperInDeferredLiteral)) (Val #()) {{ RET #(W64 101); True }} := by sorry

-- fmt shape: handleMethods with a String() that panics "oops" recovers via
-- `defer p.catchPanic(verb, "String")` and writes the PANIC message.
theorem printArg_bad_spec :
    {{ (True : IProp GF) }} App (Val (@! printArg)) (Val (#(interface.mkOk bad.t #()), #false))
    {{ RET (#true, #go!"%!v(PANIC=String method: oops)"); True }} := by sorry
theorem printArg_good_spec :
    {{ (True : IProp GF) }} App (Val (@! printArg)) (Val (#(interface.mkOk good.t #()), #false))
    {{ RET (#true, #go!"ok"); True }} := by sorry
-- With p.panicking, catchPanic re-panics with the same value, recovered by the caller.
theorem nestedPanic_spec :
    {{ (True : IProp GF) }} App (Val (@! nestedPanic)) (Val #()) {{ RET #go!"oops"; True }} := by sorry

/- The spec the deferred variant (`catcher.catch'deferred`, plan's proposal A)
   needs, in words: given the `$recover` cell holding a panic value
   `interface.mkOk go.uint64 #w`, the call stores `w` through `res`, increments
   `seen`, clears the cell (the panic is recovered), and returns `#()`; given the
   cell empty (not panicking), it changes nothing. The deferring function's
   `wrapDeferRecover` then returns its named result normally. -/

end Perennial.PendingLabelsRecover
