/-
`internal.reflectlite.isModelRType`'s spec.
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

/-- `isModelRType(t)` for the token (or any pointer-any) of a type `T` of kind `k` (a struct type
with fewer than `2^63` fields): whether `T` has the layout of the model's `rtype`, a struct of one
field of type `any` (`rtypeLayoutU`). -/
abbrev internal.reflectlite.isModelRType.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] (k : Nat) (l : Loc),
  go.kindOf u = some k → (∀ fs, u = go.StructType fs → fs.length < 2 ^ 63) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! isModelRType)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #(internal.reflectlite.rtypeLayoutU u); True }}

end spec

end Perennial
