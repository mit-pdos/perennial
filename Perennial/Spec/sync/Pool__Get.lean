/-
`sync.(*Pool).Get`'s spec.
-/
module

public import Perennial.Proof.sync.PoolDefs

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

/-- `p.Get()`: returns a value `x` with `P x`, one that was `Put` (and is returned by no other
`Get`) or one `New` returned; or, only if `New` is `nil`, returns `nil`. -/
abbrev sync.Pool.Get.spec : Prop :=
  ∀ (p : Loc) (f : GoFunc) (P : GoAny → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPool p f P }}
      (App (Val (p @!! go.GoType.PointerType Pool.ty @!! go!"Get")) (Val #()))
    {{ (x : GoAny), RET #x; P x ∨ ⌜f = func.nil ∧ x = GoInterface.nil⌝ }}

end spec

end Perennial
