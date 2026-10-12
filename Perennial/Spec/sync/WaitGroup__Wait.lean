/-
`sync.(*WaitGroup).Wait`'s spec.
-/
module

public import Perennial.Proof.sync.WaitGroupDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev sync.WaitGroup.Wait.spec : Prop :=
  ∀ (wg : Loc) (γ : WaitGroupNames) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isWaitGroup wg γ N ∗
        ownWaitGroupWaitToken γ) -∗
      (|={⊤ \ ↑N,∅}=> ▷ ∃ oldc : w32, ownWaitGroup γ oldc ∗
        (⌜sint.Z oldc = 0⌝ → ownWaitGroup γ oldc ={∅,⊤ \ ↑N}=∗
          ownWaitGroupWaitToken γ -∗ Φ #())) -∗
      WP (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #())) {{ Φ }}

end spec

end Perennial
