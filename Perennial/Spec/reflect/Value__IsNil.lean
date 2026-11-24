/-
`reflect.Value.IsNil`'s spec.
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- `v.IsNil()`, in three cases:
* a direct `Value` of kind `Pointer` (22) holding a pointer `l` (not a method value): whether
  `l` is nil;
* a `Value` of kind `Slice` (23) holding `any(q)` for a variable `q` of slice type: whether the
  slice `*q` is nil;
* a `Value` of any other kind than `Chan`, `Func`, `Interface`, `Map`, `Pointer`, `Slice`,
  `UnsafePointer` (the zero `Value`, of kind 0, included): Go's panic
  `&ValueError{"reflect.Value.IsNil", k}` for the kind `k`. -/
abbrev reflect.Value.IsNil.spec : Prop :=
  (∀ (v : Value) {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc),
  v.flag' &&& W64 31 = W64 22 → v.flag' &&& W64 640 = W64 0 →
  v.ptr' = interface.mkOk t #l →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #()))
    {{ RET #(decide (l = null)); True }}) ∧
  (∀ (v : Value) {t e : go.GoType} [t ↓u go.SliceType e] (q : Loc) (dq : DFrac) (s : GoSlice),
  v.flag' &&& W64 31 = W64 23 → v.ptr' = interface.mkOk (go.PointerType t) #q →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ q ↦{dq} s }}
      (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #()))
    {{ RET #(decide (s = slice.nil)); q ↦{dq} s }}) ∧
  (∀ (v : Value) (Φ : val → IProp GF),
  v.flag' &&& W64 31 ∉ [W64 18, W64 19, W64 20, W64 21, W64 22, W64 23, W64 26] →
    isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      (∀ l : Loc, l ↦ ValueError.mk go!"reflect.Value.IsNil" (v.flag' &&& W64 31) -∗
        Φ (PanicV #(interface.mkOk (go.PointerType ValueError.ty) #l))) ⊢
      WP (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #())) {{ Φ }})

end spec

end Perennial
