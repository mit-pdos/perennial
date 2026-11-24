/-
`reflect.unpackEface`'s spec.
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

/-- `unpackEface(i)` for `i` holding a value of type `t` (not the model's `rtype`) of kind `k`, whose
`directIfaceN` is defined (for a kind other than `Array` and `Struct`, at any fuel `n > 0`:
`directIfaceN_of_kind`):
* for a type whose values an interface stores in its data word (`directIfaceN n t = some true`:
  `Chan`, `Func`, `Map`, `Pointer`, `UnsafePointer`, and an array or struct of one such
  element), the direct `Value` holding `i`, with flag `k`;
* for another type (a value `x : V` of a non-interface type), the indirect `Value` holding
  `any(q)` for a new variable `q` holding `x`, with flag `k | flagIndir`. -/
abbrev reflect.unpackEface.spec : Prop :=
  (∀ {t u : go.GoType} [t ↓u u] (k n : Nat) (v : val),
  go.kindOf u = some k → t ≠ rtype.ty → reflect.directIfaceN n t = some true →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! unpackEface)) (Val #(interface.mkOk t v)))
    {{ RET #(Value.mk (go.tok t) (interface.mkOk t v) (W64 k)); True }}) ∧
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t u : go.GoType} [t ↓u u]
    [IntoValTyped (GF := GF) V t] (k n : Nat) (x : V),
  go.kindOf u = some k → t ≠ rtype.ty → reflect.directIfaceN n t = some false →
  go.isInterfaceType u = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! unpackEface)) (Val #(interface.mkOk t #x)))
    {{ (q : Loc), RET #(Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q)
        (W64 k ||| W64 128)); q ↦ x }})

end spec

end Perennial
