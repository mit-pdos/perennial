/-
`sync.(*Pool).Put`'s spec.
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

/-- `p.Put(x)`: gives `x`, with `P x`, to the pool (which may drop it). -/
abbrev sync.Pool.Put.spec : Prop :=
  ∀ (p : Loc) (f : GoFunc) (P : GoAny → IProp GF) (x : GoAny),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPool p f P ∗ P x }}
      (App (Val (p @!! go.GoType.PointerType Pool.ty @!! go!"Put")) (Val #x))
    {{ RET #(); True }}

end spec

end Perennial
