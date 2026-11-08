# Plan: goose tests every type of a multi-type type-switch case

- **Date:** 2026-11-08. **Status:** plan for the user's sign-off (`.agents/skills/fix-semantics/SKILL.md`,
  step 3). No trusted file is changed until it is signed off.
- **Branch:** `goose-typeswitch-multi`, off `lean` at `84d538063`.
- **Found by:** etcd-grove (sweep repairs 1), while writing the `ctx-value` design
  (`docs/design/context-value.md` on branch `ctx-value`, a separate and later landing).

## 1. The symptom

**Translation wrong (unsound).** A type-switch case that lists several types, `case T1, ..., Tn:`,
is taken in the model only if the value has one of `T1 ... T(n-1)`. `Tn` is never tested, and `T1`
is tested twice. A value of type `Tn` skips the case's body and goes on to the later cases or the
`default`.

**Cause.** `goose/goose.go`, `typeSwitchStmt`, lines 2412-2418:

```go
cond := getCond(0)
for i := range c.List[1:] {          // i = 0 .. n-2
	cond = glang.BinaryExpr{Op: glang.BinOp{OpId: glang.OpLOr, Type: glang.VerbatimExpr("go.bool")},
		X: getCond(i), Y: cond}          // c.List[0 .. n-2]: c.List[n-1] never tested
}
```

**Witness** (run with go1.27.3; scratch at `/shared/tmp/sweep-repairs-1/scratch/tswitch/main.go`):

```go
func last(x any) bool {
	switch x.(type) {
	case int, string:
		return true
	}
	return false
}
func lastPanics(x any) int {
	switch x.(type) {
	case int, string:
		panic("int or string")
	default:
		return 0
	}
}
```

| Call | Go | Model |
|---|---|---|
| `last("s")` | `true` | `false` |
| `lastPanics("s")` | panics `int or string` | returns `0` |

The second row is the unsound direction: the model has a behaviour Go does not, so a no-panic proof
of `lastPanics("s")` would go through.

**Gold evidence at `lean`:**
- `goose/testdata/examples/unittest/type_switch.go`'s `multiTypeSwitch` (`case int, string:`)
  translates to `If (Snd (TypeAssert2 go.int $y)) #true (Snd (TypeAssert2 go.int $y))`
  (`Perennial/Code/.../goose/testdata/examples/unittest.lean:5701`).
- `context.value`'s `case backgroundCtx, todoCtx:` translates to `backgroundCtx` twice
  (`Perennial/Code/context.lean:1777`).

## 2. The change

One line in `goose/goose.go`:

```diff
 			cond := getCond(0)
 			for i := range c.List[1:] {
 				cond = glang.BinaryExpr{Op: glang.BinOp{
 					OpId: glang.OpLOr,
 					Type: glang.VerbatimExpr("go.bool"),
 				},
-					X: getCond(i), Y: cond}
+					X: getCond(i + 1), Y: cond}
 			}
```

**Cost:**

| Item | Count |
|---|---|
| goose lines changed | 1 |
| new goose branches | 0 |
| semantics rules | 0 |
| trusted models | 0 |
| new semantics tests | 1 |
| new unittest gold functions | 1 |

The disjunction's evaluation order is unchanged in kind: it tests later types first, as it does
now. That is unobservable: each disjunct is a pure `TypeAssert2` (or a comparison with
`interface.nil` for a `nil` case), with no effect and no panic.

## 3. Regression tests

- **Semantics test** (`goose/testdata/examples/semantics/control_flow.go`, beside
  `testBreakTypeSwitch`; then `go generate ./goose/cmd/test_gen`):

  ```go
  // A type-switch case listing several types is taken for each of them, the last included.
  func testTypeSwitchLastType() bool {
  	var x any = "s"
  	switch x.(type) {
  	case int, string:
  		return true
  	}
  	return false
  }
  ```

  It is `true` in Go and `false` in the model at `lean`. Its Lean proof is
  `Perennial/Proof/.../semantics/testTypeSwitchLastType.lean`, `semantics_auto`, as
  `testMethodSetTypeSwitch`'s. It is linked in the semantics `Link.lean`.

- **Unittest gold** (`goose/testdata/examples/unittest/type_switch.go`): a function whose last
  listed type takes a different branch than without the fix:

  ```go
  func multiTypeSwitchLast(x any) int {
  	switch x.(type) {
  	case int, string:
  		return 1
  	case bool:
  		return 2
  	}
  	return 0
  }
  ```

  Its gold shows `TypeAssert2 go.string` in the first case's condition. The gold of the existing
  `multiTypeSwitch` changes the same way.

## 4. Fallout (re-translation)

A grep of every checked-in translation, for the shape every multi-type case translates to
(`Let "$ok" (If ...`), finds only:
- **Perennial:**
  - `Perennial/Code/context.lean:1777` (`context.value`'s `case backgroundCtx, todoCtx:`);
  - `Perennial/Code/.../goose/testdata/examples/unittest.lean:5701` (`multiTypeSwitch`).
- **etcd-grove** (`Code/`, `RaftWitness/Code/`, `PorcupineDag/Code/`): none. Nothing there needs
  re-translating; the pin bump brings only Perennial's changes.

The proofs this touches:
- **`unittest.multiTypeSwitch.wp_proof`** (`Perennial/Proof/.../unittest/multiTypeSwitch.lean`)
  cases on `ty = go.int` only. With the fix the `string` case is a new branch, so the proof gains a
  `by_cases` on `go.string` (about 4 lines). This proof breaks because the model changed in the
  intended way. The spec (`returns some w64`) is unchanged.
- **`context.value`:** no proof in Perennial steps through it. `cancelCtx.Value.spec` is proved
  only at `&cancelCtxKey`, which never reaches `value`. A `todoCtx` now takes the
  `case backgroundCtx, todoCtx` branch (`nil`) instead of the `default` (`todoCtx.Value`, the
  promoted `emptyCtx.Value`, `nil`): the same result.

Steps (per the skill's step 5):
1. `go test ./goose -update-gold`, then `go test ./goose/...` and `go vet`.
2. Rebuild goose/proofgen into a private `GOPATH`.
3. `etc/update-goose-new.py` (`context` comes from the toolchain sources, go1.27.3).
4. `etc/lean-ci.sh -q`.
5. `etc/trusted-delta.py HEAD`: the expected signals are the one goose line, the two re-translated
   bodies and the new test's translation.

## 5. Closest decided case and siblings

- **Closest case:** Case 2 (`x[low:]` evaluates `x` once, 84edc3ea5). It has the same shape: one
  wrong line in a translation scheme of `goose.go`, fixed in place, with a semantics test,
  regenerated gold and translations, and no new branch or rule. Here the scheme ("a multi-type case
  is taken if `y` asserts to any listed type") already exists; the loop just indexes the wrong
  element.
- **Siblings checked:**
  - `switchStmt` (expression switches, `case a, b:`) indexes `for i := 1; i < len(c.List); i++`,
    which is correct.
  - No other `range X[1:]` loop in `goose/*.go` uses its index into `X`.
  - The single-type case, the `default` and the `nil` case are unaffected.

  So this is one bug, with no siblings to bundle.

## 6. Left out

- The `ctx-value` proposal (`Context.Value` at other keys). It is independent of this fix (its L1
  holds over either translation) and lands separately, later.
- Any change to the order in which a case's types are tested (unobservable, §2).
