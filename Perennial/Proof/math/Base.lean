/-
Shared definitions of the proofs of the Go `math` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math
public import Perennial.GeneratedProof.math
public import Perennial.Proof.internal.gomodel.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math :=
  build_get_is_pkg_init_wf

end defs

open Lean Elab Tactic Meta in
/-- `wp_if_bool`: generalize the first Boolean value `#b` of the goal that is computed (neither a
literal, a variable nor a `decide`), such as a float comparison's `float64Leb x y`, to a variable,
so that `wp_if_destruct` (which splits on a `decide` or a Boolean variable) splits on it. -/
elab "wp_if_bool" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let computed (s : Lean.Expr) : Bool :=
    s.isAppOfArity ``GoGlobalContext.intoVal 4 && (s.getArg! 2).isConstOf ``Bool &&
      (let b := (s.getArg! 3).consumeMData
       !b.hasLooseBVars && !b.hasMVar && !b.isFVar && !b.isConstOf ``Bool.true &&
         !b.isConstOf ``Bool.false && !b.isAppOf ``Decidable.decide)
  let some v := t.find? computed | throwError "wp_if_bool: no computed Boolean value"
  let bStx ← Term.exprToSyntax ((v.getArg! 3).consumeMData)
  evalTactic (← `(tactic| generalize $bStx:term = b))

end math

end Perennial
