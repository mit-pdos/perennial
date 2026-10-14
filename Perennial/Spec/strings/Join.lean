/-
`strings.Join`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Join(elems, sep)`: the elements of `elems` separated by `sep`, when the result fits
(`JoinFits`; Go panics otherwise). -/
abbrev strings.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString),
  JoinFits xs sep →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
      (App (App (Val (@! Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }}

end spec

end Perennial
