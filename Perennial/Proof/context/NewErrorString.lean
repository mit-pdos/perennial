/-
`errors.New(msg)` with the exact type of what it returns (`*errors.errorString`) and its `s` field,
proved from `errors.New`'s code (`errors.New.spec` keeps the type abstract, `IsPointerError`): what
the initializer needs for `Canceled`'s `isTypedErr` and `"#HCanceledCell"`.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `errors.New(msg)`, with the exact type of what it returns (`errors.wp_New_ptr` keeps the
pointer type abstract; `isTypedErr` needs `*errorString`): a pointer to an `errorString`
converted to `error` (a caller that compares a non-`nil` error against it needs its
dynamic type to be comparable, which a pointer type is), whose `s` field holds `msg` for good
(nothing writes it after `New`). -/
theorem wp_New_errorString (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        x.[errors.errorString, go!"s"] ↦□ msg ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
            (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  iframe s
  imodintro
  iintro %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- The `Error()` of a context's error (`isCtxErr`: `Canceled`'s or `DeadlineExceeded`'s value)
returns its message, `"context canceled"` or `"context deadline exceeded"` (`*errorString`'s
`Error` returns its `s` field; `deadlineExceededError`'s a constant), touching nothing else. -/
theorem wp_isCtxErr_Error (e : GoInterface) (ii : GoInterfaceOk) (he : e = GoInterface.ok ii) :
    {{ isCtxErr (GF := GF) e }}
      (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ #He HΦ
  unfold isCtxErr
  icases He with (⟨-, %x, %hx, #Hs⟩ | ⟨-, %hv⟩)
  · rw [hx] at he; cases he
    rw [method_unfold]
    wp_auto
    iapply HΦ; itrivial
  · rw [hv] at he; cases he
    wp_method_call
    unfold context.deadlineExceededError.Error.impl
    wp_auto
    iapply HΦ; itrivial

end wps

end context

end Perennial
