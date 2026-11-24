/-
`errors.asAssign`'s spec (a function of the model of `As`, trusted: the semantics' `AsAssign`).
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `asAssign(err, target)` for a non-`nil` error `ii` and a target `*T`, `l`: whether `ii` is
assignable to `T` (`asAssignable`), storing it (`asStored`) into `*l` if it is, the target
unchanged otherwise. `AsTarget T` excludes Go's panics on the target; `AsDecided T ii` the case
the model does not follow (it is stuck there); `AsTypeTyped` gives the stored value its Lean type. -/
abbrev errors.asAssign.spec : Prop :=
  ∀ (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → AsDecided T ii → AsTypeTyped T' T ii →
    {{ (l ↦ v : IProp GF) }}
      (App (App (Val #(functions asAssign [])) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (v' : T'), RET #(asAssignable T ii);
        l ↦ v' ∗ ⌜(asAssignable T ii = true → asStored T ii = #v') ∧
          (asAssignable T ii = false → v' = v)⌝ }}

end spec

end Perennial
