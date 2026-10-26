/-
`github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext.Write`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std fs_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Assumptions]

/-- `Write(name, data)`: replace the contents of the file `name` by `data`, a
logically atomic spec. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Write.spec : Prop :=
  ∀ (name data : GoString),
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ old : GoString, name fs↦ old ∗ (name fs↦ data ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! Write)) (Val #name)) (Val #data)) {{ Φ }}

end spec

end Perennial
