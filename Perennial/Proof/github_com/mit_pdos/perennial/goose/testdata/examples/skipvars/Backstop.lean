/-
The skipped variables of `github.com/mit-pdos/perennial/goose/testdata/examples/skipvars` have no Lean name: hand-written Lean (another package's
`TrustedCode`, a proof) that names one fails to elaborate, as goose refuses translated code that
does. The package's `skipped'` lists them with their reasons.
-/
module

public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars

@[expose] public section

noncomputable section

namespace Perennial

/-- error: Unknown identifier `github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.X` -/
#guard_msgs in
example [GooseExts] [GoGlobalContext] : GoString := github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.X

/-- error: Unknown identifier `github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Z` -/
#guard_msgs in
example [GooseExts] [GoGlobalContext] : GoString := github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Z

-- the translated variables keep their names
example [GooseExts] [GoGlobalContext] : GoString := github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.last

example : (github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.skipped'.map (·.name)) =
    ["github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.X", "github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.a", "github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.b", "github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.Z",
     "github.com/mit-pdos/perennial/goose/testdata/examples/skipvars._@skipvars.go:38: var _ I = (*T)(nil)",
     "github.com/mit-pdos/perennial/goose/testdata/examples/skipvars._@skipvars.go:39: var _ = T{}"] := by
  rfl

end Perennial

end
