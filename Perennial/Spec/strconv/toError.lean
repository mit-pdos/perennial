/-
`strconv.toError`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `toError(fn, s, base, bitSize, err)` on the two errors of `internal/strconv` a conversion in a
valid base and bit size returns: for its `ErrSyntax` (`syn = true`) a fresh
`*NumError{fn, s, ErrSyntax}`, for its `ErrRange` one with `ErrRange`. -/
abbrev strconv.toError.spec : Prop :=
  ∀ (fn s : GoString) (base bitSize : w64) (syn : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (App (App (App (Val (@! toError)) (Val #fn)) (Val #s)) (Val #base)) (Val #bitSize))
        (Val #(interface.mkOk internal.strconv.Error.ty #(W64 (if syn then 2 else 1)))))
    {{ (err : GoInterface), RET #err;
        strconv.numErrorOf err fn s (if syn then strconv.ErrSyntax else strconv.ErrRange) }}

end spec

end Perennial
