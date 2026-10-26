/-
`sync.(*RWMutex).TryLock`'s spec: the low-level, logically atomic one, over the abstract
`rwmutex` state (`sync.rwmutex.*`, `RWMutexDefs`).
-/
module

public import Perennial.Proof.sync.RWMutexDefs

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

abbrev sync.rwmutex.RWMutex.TryLock.spec : Prop :=
  ∀ (γ : RWMutexNames) (rw : Loc) (N : Namespace),
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ ((|={⊤ \ ↑N,∅}=> ∃ state, ownRWMutex γ state ∗
          (⌜state = .RLocked 0⌝ → ownRWMutex γ .Locked ={∅,⊤ \ ↑N}=∗ Φ #true)) ∧
         Φ #false) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"TryLock")) (Val #())) {{ Φ }}

end spec

end Perennial
