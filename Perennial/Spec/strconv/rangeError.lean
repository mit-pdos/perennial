/-
`strconv.rangeError`'s spec.
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

/-- `rangeError(fn, str)`: a fresh `*NumError{fn, str, ErrRange}`, a range error of the function `fn` on `str`. -/
abbrev strconv.rangeError.spec : Prop :=
  ∀ (fn str : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (Val (@! rangeError)) (Val #fn)) (Val #str))
    {{ (l : Loc), RET #l;
        strconv.numErrorOf (interface.mkOk (go.GoType.PointerType strconv.NumError.ty) #l) fn str ErrRange }}

end spec

end Perennial
