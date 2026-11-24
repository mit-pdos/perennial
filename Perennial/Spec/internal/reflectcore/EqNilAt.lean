/-
`internal.reflectcore.EqNilAt`'s spec.
-/
module

public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

/-- `EqNilAt(x)`: `x == nil` at `x`'s dynamic type, a pointer, slice, map, channel or function
type. -/
abbrev internal.reflectcore.EqNilAt.spec : Prop :=
  (∀ {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! EqNilAt)) (Val #(interface.mkOk t #l)))
    {{ RET #(decide (l = null)); True }}) ∧
  (∀ {t e : go.GoType} [t ↓u go.SliceType e] (s : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! EqNilAt)) (Val #(interface.mkOk t #s)))
    {{ RET #(decide (s = slice.nil)); True }}) ∧
  (∀ {t k v : go.GoType} [t ↓u go.MapType k v] (m : GoMap),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! EqNilAt)) (Val #(interface.mkOk t #m)))
    {{ RET #(decide (m = map.nil)); True }}) ∧
  (∀ {t e : go.GoType} {d : go.ChanDir} [t ↓u go.ChannelType d e] (c : GoChan),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! EqNilAt)) (Val #(interface.mkOk t #c)))
    {{ RET #(decide (c = null)); True }}) ∧
  (∀ {t : go.GoType} {sig : go.signature} [t ↓u go.FunctionType sig] (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! EqNilAt)) (Val #(interface.mkOk t #f)))
    {{ RET #(decide (f = func.nil)); True }})

end spec

end Perennial
