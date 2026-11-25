/-
`internal.reflectlite.Value.IsNil`'s spec.
-/
module

public import Perennial.Proof.internal.reflectlite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

/-- `v.IsNil()` of a direct `Value` of kind `Pointer` (22) holding a pointer `l`: whether `l` is
nil. -/
abbrev internal.reflectlite.Value.IsNil.spec : Prop :=
  ∀ (v : Value) {t e : go.GoType} [t ↓u go.PointerType e] [go.NotLayoutModelled t] (l : Loc),
  v.flag' &&& W64 31 = W64 22 → v.flag' &&& W64 128 = W64 0 →
  v.ptr' = interface.mkOk t #l →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #()))
    {{ RET #(decide (l = null)); True }}

end spec

end Perennial
