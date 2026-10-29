/-
`Pool.Put`'s spec (`goose/model/pool/pool.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.pool.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.model.pool.Assumptions]

open github_com.mit_pdos.perennial.goose.model.pool in
/-- `s.Put(x)`: adds `x`, with `P x`, to the model pool, or drops it. -/
abbrev github_com.mit_pdos.perennial.goose.model.pool.Pool.Put.spec : Prop :=
  ∀ (s : Loc) (P : GoAny → IProp GF) (x : GoAny),
    {{ isPool s P ∗ P x }}
      (App (Val (s @!! go.GoType.PointerType Pool.ty @!! go!"Put")) (Val #x))
    {{ RET #(); True }}

end spec

end Perennial
