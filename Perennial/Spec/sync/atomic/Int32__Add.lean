/-
`sync.atomic.Int32.Add`'s spec.
-/
module

public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

abbrev sync.atomic.Int32.Add.spec : Prop :=
  ∀ (u : Loc) (delta : w32),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ old : w32, ownInt32 u (DFrac.own 1) old ∗
      (ownInt32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
    WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Add")) (Val #delta)) {{ Φ }}

end spec

end Perennial
