/-
`github.com/goose-lang/std.SumNoOverflow`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.Base

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
variable [package_sem : github_com.goose_lang.std.Assumptions]

/-- `SumNoOverflow(x, y)`: whether `x + y` does not overflow. -/
abbrev github_com.goose_lang.std.SumNoOverflow.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std }}
      (App (App (Val (@! SumNoOverflow)) (Val #x)) (Val #y))
    {{ RET #(decide (uint.Z (x + y) = uint.Z x + uint.Z y)); True }}

end spec

end Perennial
