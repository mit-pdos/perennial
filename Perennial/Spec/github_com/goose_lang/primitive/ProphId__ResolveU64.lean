/-
`github.com/goose-lang/primitive.ProphId.ResolveU64`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- `p.ResolveU64(x)`: resolves the prophecy `p` with `#x`, the head of the values it
was prophesied to be resolved with. -/
abbrev github_com.goose_lang.primitive.ProphId.ResolveU64.spec : Prop :=
  ∀ (p : ProphId) (pvs : List val) (x : w64),
    {{ (proph p pvs : IProp GF) }}
      (App (Val (p @!! ProphId.ty @!! go!"ResolveU64")) (Val #x))
    {{ (pvs' : List val), RET #(); ⌜pvs = #x :: pvs'⌝ ∗ proph p pvs' }}

end spec

end Perennial
