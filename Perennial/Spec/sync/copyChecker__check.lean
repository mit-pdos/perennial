/-
`sync.(*copyChecker).check`'s spec.
-/
module

public import Perennial.Proof.sync.CondDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- Not `{{{ isPkgInit sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`,
which is false for the zero checker: `check` CASes it to `c`. -/
abbrev sync.copyChecker.check.spec : Prop :=
  ∀ (c : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isCopyChecker (GF := GF) c }}
      (App (Val (c @!! go.GoType.PointerType copyChecker.ty @!! go!"check")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
