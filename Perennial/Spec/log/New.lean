/-
`log.New`'s spec.
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

/-- `log.New(out, prefix, flag)` returns a fresh, non-`nil` `*Logger` (`ownLogger`: prefix
`prefix` and flags `int32(flag)`, and its mutex guarding some writer: the spec does not say
it is `out`), for any arguments; it never panics. -/
abbrev log.New.spec : Prop :=
  ∀ (out : GoInterface) (pfx : GoString) (flag : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
      (App (App (App (Val (@! log.New)) (Val #out)) (Val #pfx)) (Val #flag))
    {{ (l : Loc), RET #l; ⌜l ≠ null⌝ ∗ log.ownLogger (GF := GF) l pfx (W32 (sint.Z flag)) }}

end spec

end Perennial
