/-
`sync.OnceValues`'s spec.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `OnceValues[T1, T2](f)` returns a function. It only allocates the state the function keeps:
what calling the function does is not specified here. -/
abbrev sync.OnceValues.spec : Prop :=
  ∀ {T1' : Type} [ZeroVal T1'] [TypedPointsto (GF := GF) T1'] {T1 : go.GoType}
    [IntoValTyped (GF := GF) T1' T1]
    {T2' : Type} [ZeroVal T2'] [TypedPointsto (GF := GF) T2'] {T2 : go.GoType}
    [IntoValTyped (GF := GF) T2' T2] (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val #(functions OnceValues [T1, T2])) (Val #f))
    {{ (g : GoFunc), RET #g; True }}

end spec

end Perennial
