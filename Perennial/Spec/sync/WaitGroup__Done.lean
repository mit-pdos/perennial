/-
`sync.(*WaitGroup).Done`'s spec.
-/
module

public import Perennial.Proof.sync.WaitGroupDefs

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

abbrev sync.WaitGroup.Done.spec : Prop :=
  ∀ (wg : Loc) (γ : WaitGroupNames) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isWaitGroup wg γ N) -∗
      (|={⊤,↑N}=> ▷ ∃ oldc : w32,
        "Hwg" ∷ ownWaitGroup γ oldc ∗
        "%Hbounds" ∷ ⌜0 ≤ sint.Z oldc - 1 ∧ sint.Z oldc - 1 < 2 ^ 31⌝ ∗
        "HΦ" ∷ (ownWaitGroup γ (oldc - W32 1) ={↑N,⊤}=∗ Φ #())) -∗
      WP (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #())) {{ Φ }}

end spec

end Perennial
