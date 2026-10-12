/-
`sync.(*WaitGroup).Add`'s spec.
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

abbrev sync.WaitGroup.Add.spec : Prop :=
  ∀ (wg : Loc) (delta : w64) (γ : WaitGroupNames) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isWaitGroup wg γ N) -∗
      (|={⊤,↑N}=> ▷ ∃ oldc : w32,
        "Hwg" ∷ ownWaitGroup γ oldc ∗
        "%Hbounds" ∷ ⌜0 ≤ sint.Z oldc + sint.Z (W32 (sint.Z delta)) ∧
          sint.Z oldc + sint.Z (W32 (sint.Z delta)) < 2 ^ 31⌝ ∗
        "HΦ" ∷ ((⌜oldc ≠ W32 0⌝ ∗ (ownWaitGroup γ (oldc + W32 (sint.Z delta)) ={↑N,⊤}=∗ Φ #())) ∨
          (ownWaitGroupWaiters γ 0 ∗
            (ownWaitGroupWaiters γ 0 -∗ ownWaitGroup γ (oldc + W32 (sint.Z delta)) ={↑N,⊤}=∗
              Φ #())))) -∗
      WP (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #delta)) {{ Φ }}

end spec

end Perennial
