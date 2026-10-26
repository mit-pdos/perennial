/-
`strconv.syntaxError`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `syntaxError(fn, str)`: a fresh `*NumError{fn, str, ErrSyntax}`, a syntax error of the function `fn` on `str`. -/
abbrev strconv.syntaxError.spec : Prop :=
  ∀ (fn str : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (Val (@! syntaxError)) (Val #fn)) (Val #str))
    {{ (l : Loc), RET #l;
        strconv.numErrorOf (interface.mkOk (go.GoType.PointerType strconv.NumError.ty) #l) fn str ErrSyntax }}

end spec

end Perennial
