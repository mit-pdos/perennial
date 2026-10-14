/-
`strings.Builder.WriteString`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `b.WriteString(t)` appends `t`, returning `len(t)` and a nil error. -/
abbrev strings.Builder.WriteString.spec : Prop :=
  ∀ (b : Loc) (s t : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ownBuilder b s }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"WriteString")) (Val #t))
    {{ RET (PairV #(W64 t.length) #interface.nil); ownBuilder b (s ++ t) }}

end spec

end Perennial
