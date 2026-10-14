/-
`errors.New(msg)` with the exact type of what it returns (`*errors.errorString`), proved from
`errors.New`'s code (`errors.New.spec` keeps the type abstract, `IsPointerError`): what the
initializer needs for `Canceled`'s `isTypedErr`.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `errors.New(msg)`, with the exact type of what it returns (`errors.wp_New_ptr` keeps the
pointer type abstract; `isTypedErr` needs `*errorString`): a pointer to an `errorString`
converted to `error` (a caller that compares a non-`nil` error against it needs its
dynamic type to be comparable, which a pointer type is). -/
theorem wp_New_errorString (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
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
  imodintro
  iintro %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

end wps

end context

end Perennial
