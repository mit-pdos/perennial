/-
`internal.reflectlite.Value.Elem`'s spec.
-/
module

public import Perennial.Proof.internal.reflectlite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

/-- `v.Elem()` of a direct `Value` of kind `Pointer` (22) holding a pointer `l : *T`: the zero
`Value` if `l` is nil, else the addressable `Value` of the `T` at `l` (`v`'s read-only bits,
`flagIndir`, `flagAddr` and `T`'s kind), which holds `any(l)`. -/
abbrev internal.reflectlite.Value.Elem.spec : Prop :=
  ∀ (v : Value) (T : go.GoType) [go.NotLayoutModelled T] (k : Nat) (l : Loc),
  go.kindOf (GoSemanticsFunctions.underlying T) = some k →
  v.typ_' = go.tok (go.PointerType T) → v.ptr' = interface.mkOk (go.PointerType T) #l →
  v.flag' &&& W64 31 = W64 22 → v.flag' &&& W64 128 = W64 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (v @!! Value.ty @!! go!"Elem")) (Val #()))
    {{ RET #(if l = null then (_root_.Perennial.zero_val internal.reflectlite.Value) else
        Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #l)
          (v.flag' &&& W64 96 ||| W64 128 ||| W64 256 ||| W64 k)); True }}

end spec

end Perennial
