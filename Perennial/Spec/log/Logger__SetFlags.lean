/-
`log.(*Logger).SetFlags`'s spec.
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

/-- `l.SetFlags(flag)` stores `int32(flag)` in the atomic `flag` field. -/
abbrev log.Logger.SetFlags.spec : Prop :=
  ∀ (l : Loc) (f : w32) (flag : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗
        sync.atomic.ownInt32 (log.loggerFlag (GF := GF) l) (DFrac.own 1) f }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"SetFlags")) (Val #flag))
    {{ RET #(); sync.atomic.ownInt32 (log.loggerFlag (GF := GF) l) (DFrac.own 1) (W32 (sint.Z flag)) }}

end spec

end Perennial
