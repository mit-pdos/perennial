/-
`sync.atomic.CompareAndSwapUint64`'s spec.
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

abbrev sync.atomic.CompareAndSwapUint64.spec : Prop :=
  ∀ (addr : Loc) (old new : w64),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : w64) (dq : DFrac), addr ↦{dq} v ∗
      ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
      (addr ↦{dq} (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
    WP (App (App (App (Val (@! CompareAndSwapUint64)) (Val #addr)) (Val #old)) (Val #new)) {{ Φ }}

end spec

end Perennial
