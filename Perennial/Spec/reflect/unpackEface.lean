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

/-- `unpackEface(i)` for `i` holding a value of type `t` (not the model's `rtype`) of a kind `k`
other than `Array` (17) and `Struct` (25):
* for a kind whose values are stored in an interface's data word (`Chan`, `Func`, `Map`,
  `Pointer`, `UnsafePointer`), the direct `Value` holding `i`, with flag `k`;
* for another kind (a value `x : V` of a non-interface type), the indirect `Value` holding
  `any(q)` for a new variable `q` holding `x`, with flag `k | flagIndir`. -/
abbrev reflect.unpackEface.spec : Prop :=
  (∀ {t u : go.GoType} [t ↓u u] (k : Nat) (v : val),
  go.kindOf u = some k → t ≠ rtype.ty → (k = 18 ∨ k = 19 ∨ k = 21 ∨ k = 22 ∨ k = 26) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! unpackEface)) (Val #(interface.mkOk t v)))
    {{ RET #(Value.mk (go.tok t) (interface.mkOk t v) (W64 k)); True }}) ∧
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t u : go.GoType} [t ↓u u]
    [IntoValTyped (GF := GF) V t] (k : Nat) (x : V),
  go.kindOf u = some k → t ≠ rtype.ty → k ≠ 17 → k ≠ 25 →
  ¬(k = 18 ∨ k = 19 ∨ k = 21 ∨ k = 22 ∨ k = 26) → go.isInterfaceType u = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! unpackEface)) (Val #(interface.mkOk t #x)))
    {{ (q : Loc), RET #(Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q)
        (W64 k ||| W64 128)); q ↦ x }})

end spec

end Perennial
