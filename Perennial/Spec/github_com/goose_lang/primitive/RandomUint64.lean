/-
`github.com/goose-lang/primitive.RandomUint64`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- `RandomUint64()`: returns an arbitrary `uint64`. -/
abbrev github_com.goose_lang.primitive.RandomUint64.spec : Prop :=
    {{ (True : IProp GF) }} (App (Val (@! RandomUint64)) (Val #()))
    {{ (x : w64), RET #x; True }}

end spec

end Perennial
