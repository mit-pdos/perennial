/-
What is derived from the linked results of `sync/atomic` and is not a Go function's triple.
-/
module

public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace sync.atomic

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- (Time receipts) `wp_AddUint64` for the call
`atomic.AddUint64(addr, v)` before the function is resolved, i.e. in the form
in which goose emits it. Resolving `AddUint64` is a Go instruction, which yields
a time receipt `⧗ 1`; the atomic update receives it (so it can, e.g., be stored
in an invariant opened by the update). -/
theorem wp_AddUint64_receipt (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (⧗ 1 -∗ |={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (App (Val (GoInstruction (FuncResolve AddUint64 []))) (Val #())) (Val #addr))
        (Val #v)) {{ Φ }} := by
  iintro %Φ #Hpkg HΦ
  wp_bind (App (Val (GoInstruction _)) (Val _))
  iapply wp_go_step_receipt'
  inext
  iintro Hr _
  iapply wp_value'
  iapply wp_AddUint64 addr v $$ %Φ Hpkg
  iapply HΦ $$ Hr

end results

end sync.atomic

end Perennial
