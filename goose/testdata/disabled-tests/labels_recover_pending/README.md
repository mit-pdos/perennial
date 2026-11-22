# Pending: labeled break/continue and recover() in deferred named functions

These programs are waiting on semantics and goose work, and goose rejects them today:
- labeled statements (`*ast.LabeledStmt`) and `break L`/`continue L` (`labels/`);
- `recover()` in a function or method called by `defer` (`recovers/`).

They drive that work (plan: stage 0 of the real `fmt`, `doPrintf` and
`handleMethods`/`catchPanic`). They are kept out of `testdata/examples` on
purpose, because `goose/examples_test.go` translates every package under it
(recursively), and these would fail.

- `labels/labels.go`, `recovers/recovers.go`: one function per feature, plus
  `fmt`-shaped ones (`miniPrintf`, `printArg`). Each `func test*() bool` returns
  true in Go, in the style of `testdata/examples/semantics`, and the comments give
  each function's result.
- `*_test.go`: run them with `go test ./goose/testdata/disabled-tests/labels_recover_pending/...`.
- `Properties.lean`: the Lean statements to prove once the semantics exists.
  Scratch only, outside every lake glob, with `sorry` placeholders.
- `DESIGN.md`: how each example translates under the plan's `catchLabel` and
  under "the loop takes the label".

Once the semantics lands, move the functions into `testdata/examples/semantics`
(or `unittest` for the gold-only shapes), regenerate `semantics/generated_test.go`
with `cmd/test_gen`, and turn `Properties.lean` into spec/proof files under
`Perennial/{Spec,Proof}/.../goose/testdata/examples/semantics/`.
