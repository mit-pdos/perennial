/-
`errors.is`'s spec (the tree walk of `Is`).
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- `is(err, target, c)` (the tree walk of `Is`): it returns `true` only if an error of the tree
is `target` or has an `Is` method that returned `true` (`M`), and, when `c` (`target`'s type is
comparable), it returns `true` if `err` is `target`. For `c`, `target` is a pointer error and
the tree's errors of its type are pointers (`TreeTyped`), so that `err == target` does not
panic. -/
abbrev errors.is.spec : Prop :=
  ∀ (S : GoError → Prop) (M : GoInterfaceOk → Prop) (err target : GoError) (c : Bool),
    S err →
    (c = true → (∃ tii, target = interface.ok tii ∧ IsPointerError tii) ∧ TreeTyped S target) →
    {{ errorIsTree (GF := GF) S M target }}
      (App (App (App (Val (@! is')) (Val #err)) (Val #target)) (Val #c))
    {{ (b : Bool), RET #b;
        ⌜b = true → ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii)⌝ ∗
        ⌜b = false → c = true → err ≠ interface.nil → err ≠ target⌝ }}

end spec

end Perennial
