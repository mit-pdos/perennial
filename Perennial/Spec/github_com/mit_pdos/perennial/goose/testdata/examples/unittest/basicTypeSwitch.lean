/-
`github.com/mit-pdos/perennial/goose/testdata/examples/unittest.basicTypeSwitch`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.basicTypeSwitch.spec : Prop :=
  ∀ (x : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ⌜match x with
          | interface.ok ⟨ty, v⟩ =>
              (ty = go.int → ∃ v' : w64, v = #v') ∧
              (ty = go.string → ∃ v' : GoString, v = #v')
          | _ => True⌝ }}
      (App (Val (@! basicTypeSwitch)) (Val #x))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
