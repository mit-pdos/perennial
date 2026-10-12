/-
`context.WithDeadlineCause`'s spec.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- Fresh ghost names `γ'` for the Done channel (see `wp_WithCancel`), and the deadline is
`some d'` with `d' = d ∨ parent_desc.Deadline = some d'`: `Deadline := some d` would be false
when the parent's deadline `cur` is before `d`, as `WithDeadlineCause` then returns `WithCancel(parent)`, whose `Deadline()` is
the parent's `cur`. -/
abbrev context.WithDeadlineCause.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF)) (d : time.Time)
      (cause : GoError),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent parent_desc }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok parent))) (Val #d))
        (Val #cause))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d' : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜d' = d ∨ parent_desc.Deadline = some d'⌝ ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx'
          { parent_desc with Deadline := some d', PDone := iprop(True), Done_gn := γ' } }}

end spec

end Perennial
