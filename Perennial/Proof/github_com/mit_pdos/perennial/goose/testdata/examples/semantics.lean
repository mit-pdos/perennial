/-
The proofs of the goose `semantics` test package: the shared definitions (`Base`) and
the linked results (`Link`), `github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_<F>`
for each proved function `F`. By Go source file:

* `arrays.go`: range loops over arrays.
* `builtin.go`: the builtins `min` and `max`.
* `control_flow.go`: `fallthrough`, and `break` in a `switch`.
* `conversions.go`, `int_conversions.go`: conversions (the `[]byte -> string`
  conversion is handled with `wp_bytes_to_string`) and integer conversions.
* `interfaces_complex.go`, `type_equality.go`, `structs.go`, `new.go`, `slices.go`.
* `loopvars.go`: each iteration of a loop has its own iteration variables.
* `nil.go`: comparisons with `nil`.
* `panic.go`: `panic`.
* `precedence.go`: operator precedence.
* `recover.go`: `panic` and `recover`: a panic recovered by a deferred function
  literal that sets a named result (`recoverNamed`), a panic raised two calls down
  inside a loop that reaches a recovering `defer` (`catchTwoDeep`), and a panic that
  runs the deferred functions and continues (`panicUnrecovered`).
* `allocator.go`: nothing stated yet (see `Base`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Link

@[expose] public section
