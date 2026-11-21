/-
`internal.strconv.Atoi`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `Atoi(s)` returns, with a nil error, `ErrSyntax` or `ErrRange` (the errors of `ParseInt(s, 10,
0)`, which its slow path calls; its fast path, for 1 to 18 bytes, returns `ErrSyntax` for a
non-digit). The number is not specified: what callers need is that `Atoi` does not panic and which
errors it returns. -/
abbrev internal.strconv.Atoi.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv }}
      (App (Val (@! Atoi)) (Val #s))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        ⌜err = interface.nil ∨ err = interface.mkOk internal.strconv.Error.ty #(W64 2) ∨
          err = interface.mkOk internal.strconv.Error.ty #(W64 1)⌝ }}

end spec

end Perennial
