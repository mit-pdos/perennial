# Labels: `catchLabel` (plan A) vs "the loop takes the label"

`doFor cond body post` (argument order of `Defn/Loop.lean`); `B` is a body thunk. A: `doFor c (λ: <>, catchLabel #"L" (B #())) p`. Owner: `doForLabeled #"L" c B p`, either (O1) defined as exactly A's term, or (O2) a new primitive loop that compares the label itself.

| example (`labels/`) | A | O1 / O2 |
|---|---|---|
| labeledContinue, labeledBreak, countPairs, returnInLabeledLoop, closureAcrossContinue | body wrapped; `doFor` sees plain `continue` and runs the post (and the loop-variable copy) | same term (O1); O2 needs its own step/`wp_for` rule |
| continueFromNestedSwitch, miniPrintf (`continue formatLoop` crosses an inner loop *with* a post) | inner `doFor` returns `continueTo` unchanged, so the post is skipped, as Go does | same; O2 must also pass other labels' outcomes outward |
| breakLoopFromSwitch | unlabeled switch's `catchBreak` passes `breakTo` on | same |
| labeledSwitch, labeledSelect | `catchBreak (catchLabel #"L" s)` | no loop to take the label: O needs `catchLabel` (or a `catchLabelBreak`) anyway |
| rangeInt | goose desugars to `doFor`: wrap the body | `doForLabeled` applies directly |
| rangeSlice/Map/Func, breakThroughRangeFunc | wrap the body closure `λ: "k" "v", catchLabel #"L" (…)`; no range helper changes | needs a labeled variant of each helper (slice, array x3, chan, string, map, func n), or a wrapped body, which is A |
| sameLabelNested | the literal's body is separate code, so labels cannot meet | same |

Where they differ:
- Only O2 really differs from A. O1 is A with a name, covering 3-clause `for` and int-range only.
- Labeled `switch`/`select` and the 7+ range helpers have no `cond`/`post` for the loop to take, so O still needs `catchLabel` for them. A uses one wrapper everywhere.
- `continue L` with a post statement: the wrapper must sit *inside* the body thunk. `catchLabel L (doFor …)` would turn `continue L` into leaving the loop and skip the post. A and O1 both put it inside. O2 must handle it in its own rule.
- Crossing loops: in both, every loop that a jump to an *outer* label crosses must pass `breakTo`/`continueTo` outward without running its post. That is today's behaviour of `doFor`, `func.forRange` (through `exit`) and `map.forRange`, so the `forPostcondition` "labeled outcome" disjunct is needed under either shape.
- Proofs: O2 gives a `wp_forLabeled` rule that treats its own label as `continue`/`break`. A gets the same from `wp_for` + `wp_catchLabel`, at no trusted cost.

Recommendation: A, with `doForLabeled` at most as an abbreviation (O1) for readable gold files and a derived `wp_forLabeled` lemma. A adds 3 one-line definitions, no step rules and no change to any existing loop or range helper. It handles switch/select and all ranges the same way. O2 adds a trusted primitive and still needs `catchLabel` for switch/select and ranges.

# Recover (`recovers/`), plan A (`F'deferred` taking `$recover`)
- methodRecover, topRecover, recoverNotPanicking, printArg (handleMethods/catchPanic): `defer c.catch(&x)` → `defer (catcher.catch'deferred $panic c &x)`. Provable.
- repanic, nestedPanic: `F'deferred` re-panics after `recoverPanic $recover`. Provable.
- methodValueRecover (`f := c.catch; defer f(&x)`): goose cannot see the callee, so it runs the ordinary `catch`, whose `recover()` is stuck. Unprovable, and sound. Returning nil there would let the false "panics with 9" spec be proved.
- directCall, helperInDeferredLiteral: Go's recover gives nil. Under "stuck" they are unprovable. That is the incompleteness decision point 6 accepts, and these two show its price.
