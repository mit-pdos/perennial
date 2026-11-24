/-
`reflect.isDirectIface`'s spec.
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- `isDirectIface(t)` for the token (or any pointer-any) of a type `T` of a kind `k` other than
`Array` (17) and `Struct` (25): whether `k` is `Chan`, `Func`, `Map`, `Pointer` or
`UnsafePointer`. -/
abbrev reflect.isDirectIface.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] (k : Nat) (l : Loc),
  go.kindOf u = some k → k ≠ 17 → k ≠ 25 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! isDirectIface)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #(decide (k = 18 ∨ k = 19 ∨ k = 21 ∨ k = 22 ∨ k = 26)); True }}

end spec

end Perennial
