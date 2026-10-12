/-
`sync.(*RWMutex).Unlock`'s spec: the low-level, logically atomic one, over the abstract
`rwmutex` state (`sync.rwmutex.*`, `RWMutexDefs`).
The guarded corollaries (`sync.RWMutex.wp_Unlock`, `wp_Unlock_guard`) are in `Perennial/Proof/sync/Results.lean`.
-/
module

public import Perennial.Proof.sync.RWMutexDefs

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

abbrev sync.rwmutex.RWMutex.Unlock.spec : Prop :=
  ∀ (γ : RWMutexNames) (rw : Loc) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ownRWMutex γ .Locked ∗
          (ownRWMutex γ (.RLocked 0) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #())) {{ Φ }}

end spec

end Perennial
