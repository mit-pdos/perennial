/-
`log.(*Logger).SetPrefix`'s spec.
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

/-- `l.SetPrefix(prefix)` stores a pointer to a fresh cell holding `prefix` (the parameter's
variable, `&prefix`) in the atomic `prefix` field. -/
abbrev log.Logger.SetPrefix.spec : Prop :=
  ∀ (l : Loc) (p0 : Loc) (pfx : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ ⌜log.LoggerAligned (GF := GF) l⌝ ∗
        sync.atomic.ownPointer (T' := GoString) (log.prefixField (GF := GF) l) (DFrac.own 1) p0 }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"SetPrefix")) (Val #pfx))
    {{ RET #(); ∃ p : Loc,
        sync.atomic.ownPointer (T' := GoString) (log.prefixField (GF := GF) l) (DFrac.own 1) p ∗
        p ↦ pfx }}

end spec

end Perennial
