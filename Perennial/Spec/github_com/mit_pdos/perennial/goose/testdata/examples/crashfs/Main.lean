/-
`github.com/mit-pdos/perennial/goose/testdata/examples/crashfs.Main`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std fs_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Assumptions]

/-- `Main()`, the boot program: under the invariant of the file `"f"`, it does
not panic (its assertions hold). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Main.spec : Prop :=
  ∀ (N : Namespace) (γ : GName),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs ∗
        inv N (fileInv γ) }}
      (App (Val (@! Main)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
