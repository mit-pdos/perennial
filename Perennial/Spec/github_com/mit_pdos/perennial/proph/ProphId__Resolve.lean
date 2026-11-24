/-
`github.com/mit-pdos/perennial/proph.ProphId.Resolve`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.proph.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.proph.Assumptions]

/-- `p.Resolve(v)`: resolves the prophecy `p` with `#v`, the head of the values it
was prophesied to be resolved with. `v` is the `any` argument, the interface value Go's
implicit conversion builds: `interface.mkOk T #x` for an argument `x` of a non-interface
type `T`. So `#v` holds `x`'s value in the model, and two resolutions are equal values exactly
when their dynamic types and model values are equal (not Go's `==`, which `Resolve` does not
evaluate); a pointer, slice, map, channel or function in `x` contributes its address, not
what it points to. -/
abbrev github_com.mit_pdos.perennial.proph.ProphId.Resolve.spec : Prop :=
  ∀ (p : ProphId) (pvs : List val) (v : GoInterface),
    {{ (proph p pvs : IProp GF) }}
      (App (Val (p @!! ProphId.ty @!! go!"Resolve")) (Val #v))
    {{ (pvs' : List val), RET #(); ⌜pvs = #v :: pvs'⌝ ∗ proph p pvs' }}

end spec

end Perennial
