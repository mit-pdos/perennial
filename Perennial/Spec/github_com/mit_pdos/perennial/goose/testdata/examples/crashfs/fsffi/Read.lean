/-
`github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi.Read`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std fs_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Assumptions]

/-- `Read(name)`: the contents of the file `name`, a logically atomic spec (the
file's points-to is needed only at the read, so it can come from an invariant). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Read.spec : Prop :=
  ∀ (name : GoString),
  ⊢ ∀ Φ : val → IProp GF, (|={⊤,∅}=> ∃ (q : DFrac) (c : GoString),
        name fs↦{q} c ∗ (name fs↦{q} c ={∅,⊤}=∗ Φ #c)) -∗
      WP (App (Val (@! Read)) (Val #name)) {{ Φ }}

end spec

end Perennial
