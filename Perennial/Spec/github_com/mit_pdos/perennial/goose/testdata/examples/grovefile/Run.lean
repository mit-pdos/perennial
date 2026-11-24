/-
`github.com/mit-pdos/perennial/goose/testdata/examples/grovefile.Run`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std grove_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Assumptions]

/-- `Run()`: with the file `"f"` (any contents), it returns normally (its checks
hold: the read returns what was written, and the TSC does not decrease) and
leaves `"f"` holding `"hello"`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Run.spec : Prop :=
  ∀ (old : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile ∗
        go!"f" f↦ old }}
      (App (Val (@! Run)) (Val #()))
    {{ RET #(); go!"f" f↦ go!"hello" }}

end spec

end Perennial
