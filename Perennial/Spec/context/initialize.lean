/-
`context.initialize'`'s spec.
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

/-- `context`'s package initialization (`wp_initialize'`).

The initializer allocates the package's variables, initializes `errors`, `sync`,
`sync/atomic` and `time`, sets `Canceled = errors.New("context canceled")`,
`DeadlineExceeded = deadlineExceededError{}` and `closedchan = make(chan struct{})`, and runs
`init()`, which closes `closedchan`. It establishes `isInit` (the `goroutines` counter in an
invariant, the fixed `closedchan` and `Canceled`, whose dynamic types `*errors.errorString` and
`deadlineExceededError` are in the type set of `error`: `isTypedErr`, from their method sets,
`errors.errorString_is_error` and `deadlineExceededError_is_error`). -/
abbrev context.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.context get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.context }}

end spec

end Perennial
