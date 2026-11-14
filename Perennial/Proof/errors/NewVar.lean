/-
Package variables made by `errors.New`: `errors.wp_New_errorString` (`errors.New(msg)` with the
exact type of what it returns, `*errorString`, and its field, proved from `New`'s code), from which a
package's initializer proves `errors.newVar X msg` (`Base`: the global `X` holds such an error, for
good: `var X = errors.New(msg)`, which Go never writes after initialization), what its `isPkgInit`
keeps of such a variable (`io.isInit`, and `errors`' own for `ErrUnsupported`).

`errors.New.spec` keeps the error's type abstract (`IsPointerError`), which is enough to call
`Error()` and to compare it with `==`; a client that needs facts about the type (that it
implements `error`, `context.errorString_is_error`, and the methods it lacks, both from its
method set, by `go_type_set`) needs it to be `*errorString`.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace errors

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `newVar`'s error is a pointer error (`IsPointerError`). -/
theorem newVar_isPointerError (x : Loc) :
    IsPointerError ⟨go.GoType.PointerType errorString.ty, #x⟩ :=
  ⟨_, x, rfl, rfl⟩

variable [package_sem : errors.Assumptions]

/-- `errors.New(msg)`, with the exact type of what it returns (`errors.New.spec` keeps it
abstract, `IsPointerError`): a pointer to an `errorString` converted to `error`, whose field
`s` holds `msg` for good (nothing writes it after `New`) and whose `Error()` returns `msg`. -/
theorem wp_New_errorString (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errorString.ty) #x);
        x.[errors.errorString, go!"s"] ↦□ msg ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType errorString.ty) go!"Error" #x))
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

end wps

end errors

end Perennial
