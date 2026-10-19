/-
`github.com/goose-lang/primitive.ProphId.ResolveBool`'s spec.
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

/-- `p.ResolveBool(b)`: resolves the prophecy `p` with `#b`, the head of the values it
was prophesied to be resolved with. -/
abbrev github_com.goose_lang.primitive.ProphId.ResolveBool.spec : Prop :=
  ∀ (p : ProphId) (pvs : List val) (b : Bool),
    {{ (proph p pvs : IProp GF) }}
      (App (Val (p @!! ProphId.ty @!! go!"ResolveBool")) (Val #b))
    {{ (pvs' : List val), RET #(); ⌜pvs = #b :: pvs'⌝ ∗ proph p pvs' }}

end spec

end Perennial
