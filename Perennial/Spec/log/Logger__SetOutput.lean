/-
`log.(*Logger).SetOutput`'s spec.
-/
module

public import Perennial.Proof.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

/-- `l.SetOutput(w)` stores `w` in `out` under the lock `outMu` (whose resource keeps only
that `out` holds some writer), and in the atomic `isDiscard` some Boolean (Go stores
whether `w == io.Discard`, a comparison that never panics: `Discard`'s dynamic type,
`io.discard`, is comparable, `io.isInit`; the spec does not say which). -/
abbrev log.Logger.SetOutput.spec : Prop :=
  ∀ (l : Loc) (b : Bool) (w : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗
        sync.isMutex (log.loggerOutMu (GF := GF) l)
          (∃ w : GoInterface, log.loggerOut (GF := GF) l ↦ w) ∗
        sync.atomic.ownBool (log.loggerIsDiscard (GF := GF) l) (DFrac.own 1) b }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"SetOutput")) (Val #w))
    {{ RET #(); ∃ b' : Bool, sync.atomic.ownBool (log.loggerIsDiscard (GF := GF) l) (DFrac.own 1) b' }}

end spec

end Perennial
