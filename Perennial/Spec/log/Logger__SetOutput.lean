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

/-- `l.SetOutput(w)` stores `w` in `out` under the lock `outMu`, and in the atomic
`isDiscard` whether `w == io.Discard` (a comparison that never panics: `Discard`'s dynamic
type, `io.discard`, is comparable, `io.isInit`). -/
abbrev log.Logger.SetOutput.spec : Prop :=
  ∀ (l : Loc) (b : Bool) (w : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ ⌜log.LoggerAligned l⌝ ∗
        sync.isMutex (log.outMuField (GF := GF) l)
          (∃ w : GoInterface, log.outField (GF := GF) l ↦ w) ∗
        sync.atomic.ownBool (log.isDiscardField (GF := GF) l) (DFrac.own 1) b }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"SetOutput")) (Val #w))
    {{ RET #(); ∃ b' : Bool, sync.atomic.ownBool (log.isDiscardField (GF := GF) l) (DFrac.own 1) b' }}

end spec

end Perennial
