# Design: `Context.Value` at keys other than `&cancelCtxKey`

- **Date:** 2026-11-08. **Status:** proposal, for review. Nothing here is implemented.
- **Branch:** `ctx-value`, off `lean` at `84d538063`.
- **Requested by:** etcd-grove, for two needs that are one family:
  - **B2-F1** (sweep repairs 1). `ctx.Value(StartTimeKey{})` and `ctx.Value(keepAliveCtxKey{})` for
    `s.ctx = WithCancel(Background())` and for contexts derived from it by `WithValue`. These replace
    two axioms that claim the result for every `isContext`. That claim is false: an `isContext` may
    hold any value under the key, and a user `Context` may panic in `Value`.
  - **P-RL1** (k8s stage 7f). For `child = WithCancel(parent)` and a key `k ≠ &cancelCtxKey`, the
    child's `Value(k)` is the parent's. That stage's parent is a `*valueCtx` chain (grpc metadata).
- **Kind:** proofs over the translated `context` package. There is no new axiom, no new trusted
  code, and no change to an existing statement except stronger posts.

## 1. What is missing

At `lean`, `context`'s specs give `Value` only at `&cancelCtxKey`:
- `isContext`'s `"#HValue"` (`Proof/context/Base.lean:583`, and `:609`: "the `Values` field of
  `ContextDesc` is unused");
- `context.cancelCtx.Value.spec`.

Nothing says what `Value(k)` returns at any other key, for any context. There is also no spec of
`backgroundCtx`'s `Value`. `withCancel`'s post already makes the new context's parent field
read-only (`ctxField c ↦□ parent`, `Spec/context/withCancel_.lean:38`). `wp_WithCancel_gen` then
folds it into `isContext`, and `WithCancel`'s public posts drop it. So a client cannot follow
`cancelCtx.Value`'s `value(c.Context, key)`.

## 2. Go (go1.27.3, `src/context/context.go`)

```go
func (c *cancelCtx) Value(key any) any {
	if key == &cancelCtxKey { return c }
	return value(c.Context, key)
}
func (c *valueCtx) Value(key any) any {
	if c.key == key { return c.val }
	return value(c.Context, key)
}
func (emptyCtx) Value(key any) any { return nil }   // backgroundCtx, todoCtx embed it
func value(c Context, key any) any {
	for {
		switch ctx := c.(type) {
		case *valueCtx:   if key == ctx.key { return ctx.val }; c = ctx.Context
		case *cancelCtx:  if key == &cancelCtxKey { return c }; c = ctx.Context
		case withoutCancelCtx: if key == &cancelCtxKey { return nil }; c = ctx.c
		case *timerCtx:   if key == &cancelCtxKey { return &ctx.cancelCtx }; c = ctx.Context
		case backgroundCtx, todoCtx: return nil
		default:          return c.Value(key)
		}
	}
}
```

`value(c, k)` is `c.Value(k)` with the loop unrolled. It reads the fields of the standard types
directly instead of calling their `Value` methods. So a law stated only with `parent.Value(k)` is
not enough for the child: P-RL1's first wording was false for exactly this reason (the 7f review).
The laws below carry both `x.Value(k)` and `value(x, k)` for every context `x` they describe.

## 3. The proposal

### 3.1 One predicate

```lean
/-- `ctxValue x k R` (persistent, sealed): `x.Value(k)` returns, with a result satisfying `R`, and
so does `context.value(x, k)` (from any loop state at `x`). -/
@[no_expose] def ctxValue (x : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) : IProp GF
instance ctxValue_persistent ...
theorem ctxValue_Value : ctxValue x k R ⊢
  {{ True }} (App (Val #(methods x.ty go!"Value" x.v)) (Val #k)) {{ (v : GoInterface), RET #v; ⌜R v⌝ }}
theorem ctxValue_mono : (∀ v, R v → R' v) → ctxValue x k R ⊢ ctxValue x k R'
```

Internally it is `□ (WP x.Value(k) {R} ∧ ∀ lc lk lres, the loop of value from c ↦ x … {R})`. The
loop form is internal: it lets the `*cancelCtx` and `*valueCtx` cases continue the caller's loop
instead of calling `value` again.

### 3.2 The laws (all proved over `Code/context.lean`)

- **L1, the roots.** `⊢ ctxValue backgroundCtxVal k (· = interface.nil)`, and the same for
  `todoCtxVal`, for every `k`. This is the `case backgroundCtx, todoCtx` branch and `emptyCtx.Value`.
  See §5 on how the translation handles `todoCtx` here.
- **L2, `*cancelCtx` (B2-F1, and P-RL1 for every parent this file describes).**
  `ctxField c ↦□ parent ∗ ⌜k ≠ cancelCtxKeyAny⌝ ∗ ctxValue parent k R ⊢
  ctxValue (interface.mk (ptr cancelCtx.ty) #c) k R`. There is no premise on the parent's type: the
  parent enters through its own `ctxValue`, not through `parent.Value`. This is what makes P-RL1
  true.
- **L3, `*timerCtx`.** The same, through the embedded `cancelCtx`'s `Context` field (`tcc c`, which
  `timerCtx.cancel.spec` already reads read-only). The `Value` method is the promoted
  `(*cancelCtx).Value`.
- **L4, `*valueCtx`** (for `WithValue`, which `lean` does not translate: `context.toml`'s
  `!WithValue`). The law is stated over its fields, so that whatever produces a `valueCtx` (a
  client's trust-boundary spec of `WithValue` today, a translation later) only states the fields:
  `valueCtxFields p parent key val ∗ ⌜safe to compare k with key⌝ ∗ ⌜k = key → R val⌝ ∗
  (⌜k ≠ key⌝ -∗ ctxValue parent k R) ⊢ ctxValue (interface.mk (ptr valueCtx.ty) #p) k R`.
  - `valueCtxFields` is the three fields read-only, plus `key`'s comparability (`WithValue` panics
    on a non-comparable key).
  - "Safe to compare" means `k`'s dynamic type is not `key`'s, or is comparable. `key == ctx.key`
    on two `any`s panics only if both dynamic types are the same non-comparable type. The
    comparisons with `&cancelCtxKey` (a `*int`) never panic.
- **L5, other contexts.** `⌜x.ty` is none of `ptr valueCtx`, `ptr cancelCtx`, `withoutCancelCtx`,
  `ptr timerCtx`, `backgroundCtx`, `todoCtx⌝ ∗ □ {{ True }} x.Value(k) {{ v, ⌜R v⌝ }} ⊢
  ctxValue x k R`. This is the `default` branch: an application's own context type, whose `Value`
  spec its owner gives.

### 3.3 The constructors' posts (stronger, nothing else changes)

- `WithCancel.spec` and `wp_WithCancel_any`: the post also gives
  `□ ∀ k R, ⌜k ≠ cancelCtxKeyAny⌝ -∗ ctxValue parent k R -∗ ctxValue ctx' k R`. This is L2 with
  `withCancel`'s `ctxField c ↦□ parent`, which the proof already has (`Hf`).
- `wp_WithCancel_Background`: `□ ∀ k, ⌜k ≠ cancelCtxKeyAny⌝ -∗ ctxValue ctx' k (· = nil)`, by L1
  and L2.
- `WithDeadline`/`WithTimeout`/`WithDeadlineCause`, and their `Background` forms: the same, by L3.
- `isContext` and `ContextDesc` are unchanged. Folding `ctxValue` into `isContext` (for the
  `Values` field) would change every client of `isContext`. It is left as a later option, recorded
  here.

### 3.4 What it serves

- **B2-F1.** `s.ctx = WithCancel(Background())` gets `ctxValue s.ctx k nil` at every key that is
  not `&cancelCtxKey`. Through `ctxValue_Value`, that is the `{{True}} s.ctx.Value(k)` that
  etcd-grove's `WithValue` wand takes. `startTimeOk`/`keepAliveOk` follow, and the two axioms
  `context.ValueStartTime`/`ValueKeepAlive` are deleted. The client's local `WithCancelBackground`
  spec is a corollary.
- **P-RL1.** `child = WithCancel(parent)` with `ctxValue parent k R` gives `ctxValue child k R`,
  for any parent type. For 7f's parent (a `*valueCtx` from `WithValue`, through
  `metadata.AppendToOutgoingContext`), the client's `WithValue` spec states `valueCtxFields` and
  L4 gives `ctxValue`. That is a change in etcd-grove's trust-boundary spec, not in Perennial.
- **Not covered: P-RL2** (derivations over a parent whose `Err` is any error after `Done`). It is
  another family: `isContext` generalized over its errors' predicate. It stays a separate proposal.

## 4. Cost and risk

- About 300-500 lines in `Perennial/Proof/context/` (a new `Value.lean`; posts in
  `WithCancelGen.lean`, `Results.lean`, `TimerCtx.lean`, `WithDeadline*.lean`).
- The loop proof is the bulk: a `for` with five type assertions per iteration, proved once with
  an invariant over the current `c`.
- Trusted base: unchanged. No assumption, no axiom, no trusted code. `etc/trusted-delta.py` should
  print nothing.

## 5. A translator bug found on the way (separate fix, `fix-semantics`)

goose translates a type-switch case that lists several types incorrectly: it tests the first type
twice and never tests the last one.

- In `goose.go` (`typeSwitchStmt`), `for i := range c.List[1:] { cond = ... getCond(i) ... }`
  iterates `i = 0 .. n-2`, so it should be `getCond(i+1)`.
- Gold evidence:
  - `testdata/examples/unittest/type_switch.go`'s `multiTypeSwitch` (`case int, string:`)
    translates to `If (Snd (TypeAssert2 go.int $y)) true (Snd (TypeAssert2 go.int $y))`
    (`Code/.../unittest.lean:5701`): a `string` takes the other branch.
  - `context.value`'s `case backgroundCtx, todoCtx:` translates to `backgroundCtx` twice
    (`Code/context.lean:1777`).

The model then differs from Go: the case's body is skipped for the last type. That is unsound when
the body is the one that panics. For example, `case int, string: panic(..)` with a string runs the
next case or the default in the model and panics in Go.

In `context.value` it is harmless: a `todoCtx` reaches `default`, whose `c.Value(key)` is
`emptyCtx.Value`, `nil`, as the skipped case returns. L1 is proved over the translation as it is.

The only multi-type cases in the translations etcd-grove and Perennial check in are these two
(a grep for the pattern). The fix goes through `.agents/skills/fix-semantics/SKILL.md` as its own
bug, with the user's sign-off. It is not part of this proposal.
