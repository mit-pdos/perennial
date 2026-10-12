/-
`sync.runtime_SemacquireRWMutex`'s spec.
-/
module

public import Perennial.Proof.sync.SemaDefs

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

abbrev sync.runtime_SemacquireRWMutex.spec : Prop :=
  ∀ (sema : Loc) (γ : GName) (N : Namespace) (lifo : Bool) (skipframes : w64),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isSema sema γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ v, ownSema γ v ∗
        (⌜uint.nat v > 0⌝ → ownSema γ (v - W32 1) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (App (App (Val (@! runtime_SemacquireRWMutex)) (Val #sema)) (Val #lifo)) (Val #skipframes)) {{ Φ }}

end spec

end Perennial
