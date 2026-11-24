/-
Results of `reflect` derived from the linked ones, in the vocabulary of `Values.lean`: the
methods of a `reflPtr`, a `reflElem` and the zero `Value`, and the `Type` methods called through
the interface `reflect.Type` on a `reflType`.
-/
module

public import Perennial.Proof.reflect.Link
public import Perennial.Proof.reflect.Values

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace reflect

/-- The flag bits of a `reflPtr`: kind `Pointer` (22), no other bit. -/
theorem ptrFlag_bits :
    W64 22 &&& W64 31 = W64 22 ∧ W64 22 ≠ W64 0 ∧ W64 22 &&& W64 256 = W64 0 ∧
    W64 22 &&& W64 352 ≠ W64 256 ∧ W64 22 &&& W64 96 = W64 0 ∧ W64 22 &&& W64 512 = W64 0 ∧
    W64 22 &&& W64 640 = W64 0 ∧ W64 22 &&& W64 736 = W64 0 ∧ W64 22 &&& W64 128 = W64 0 := by
  decide

/-- `Elem()`'s flag on a `reflPtr`: a `reflElem`'s. -/
theorem elemOfPtr_flag (k : Nat) (hk : k < 27) :
    W64 22 &&& W64 96 ||| W64 128 ||| W64 256 ||| W64 k = W64 k ||| W64 128 ||| W64 256 := by
  revert k; decide

/-- The kinds at which `IsNil` panics. -/
theorem isNil_panic_kinds :
    W64 0 ∉ [W64 18, W64 19, W64 20, W64 21, W64 22, W64 23, W64 26] ∧
    W64 25 ∉ [W64 18, W64 19, W64 20, W64 21, W64 22, W64 23, W64 26] ∧
    W64 0 &&& W64 31 = W64 0 := by
  decide

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-! ## `ValueOf` and `TypeOf` -/

omit [GooseSemantics] [GooseInterp] in
theorem pointerType_ne_rtype (T : go.GoType) : go.PointerType T ≠ rtype.ty := by
  unfold rtype.ty; simp

/-- `ValueOf(any(p))` for `p : *T`: a `reflPtr`. -/
theorem wp_ValueOf_reflPtr (T : go.GoType) (p : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! ValueOf)) (Val #(interface.mkOk (go.PointerType T) #p)))
    {{ (w : Value), RET #w; ⌜reflPtr w T p⌝ }} := by
  iintro %Φ #Hinit HΦ
  wp_apply (reflect.wp_ValueOf (GF := GF) (hG := hG)).1 (t := go.PointerType T)
    (u := go.PointerType T) 22 1 #p (by simp [go.kindOf]) (pointerType_ne_rtype T)
    (directIfaceN_of_kind (u := go.PointerType T) (k := 22) 0 (by simp [go.kindOf]) (by omega)
      (by omega))
  iapply HΦ
  ipureintro
  rfl

/-- `ValueOf(any(x))` for a value `x : V` of a struct type `t` that is not direct (for one
whose last field's type has a kind outside `directKind`, `Array` and `Struct`, such as `int64`:
`directIfaceN_struct_last`): the indirect `Value` of kind `Struct` holding a new variable `q`
holding `x`, on which `IsNil` panics (`Value.wp_IsNil_struct_value`). -/
theorem wp_ValueOf_struct_indirect {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} {fs : List go.field_decl} [t ↓u go.StructType fs]
    [IntoValTyped (GF := GF) V t] (x : V) (n : Nat) (ht : t ≠ rtype.ty)
    (hd : directIfaceN n t = some false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! ValueOf)) (Val #(interface.mkOk t #x)))
    {{ (q : Loc), RET #(Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q)
        (W64 25 ||| W64 128)); q ↦ x }} :=
  (reflect.wp_ValueOf (GF := GF) (hG := hG)).2.1 (u := go.StructType fs) 25 n x
    (by simp [go.kindOf]) ht hd (by simp [go.isInterfaceType])

/-- `ValueOf(nil)`: the zero `Value`. -/
theorem wp_ValueOf_nil :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! ValueOf)) (Val #(interface.nil : GoInterface)))
    {{ RET #(_root_.Perennial.zero_val reflect.Value); True }} :=
  (reflect.wp_ValueOf (GF := GF) (hG := hG)).2.2

/-- `TypeOf(i)` for `i` holding a value of type `t` (not the model's `rtype`): a `reflType`. -/
theorem wp_TypeOf_reflType (t : go.GoType) (v : val) (ht : t ≠ rtype.ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! TypeOf)) (Val #(interface.mkOk t v)))
    {{ (rt : Type'), RET #rt; ⌜reflType rt t⌝ }} := by
  iintro %Φ #Hinit HΦ
  wp_apply (reflect.wp_TypeOf (GF := GF) (hG := hG)).1 t v ht
  iapply HΦ
  ipureintro
  rfl

/-- `TypeOf(nil)`: the nil `Type`. -/
theorem wp_TypeOf_nil :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! TypeOf)) (Val #(interface.nil : GoInterface)))
    {{ RET #(interface.nil : GoInterface); True }} :=
  (reflect.wp_TypeOf (GF := GF) (hG := hG)).2

/-! ## `Value.Kind` -/

theorem Value.wp_Kind_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 22); True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_Kind : reflect.Value.Kind.spec (GF := GF) (hG := hG)) w
  rwa [hf, ptrFlag_bits.1] at h

theorem Value.wp_Kind_reflElem (v : Value) (T : go.GoType) (p : Loc) (k : Nat)
    (h : reflElem v T p) (hk : go.kindOf (GoSemanticsFunctions.underlying T) = some k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 k); True }} := by
  obtain ⟨k', hk', hv⟩ := h
  rw [hk] at hk'
  cases hk'
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have h := (reflect.Value.wp_Kind : reflect.Value.Kind.spec (GF := GF) (hG := hG)) v
  rwa [hf, (elemFlag_bits k (kindOf_lt hk)).1] at h

theorem Value.wp_Kind_zero :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((_root_.Perennial.zero_val reflect.Value) @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 0); True }} := by
  have hf : (_root_.Perennial.zero_val reflect.Value).flag' = W64 0 := rfl
  have h := (reflect.Value.wp_Kind : reflect.Value.Kind.spec (GF := GF) (hG := hG)) (_root_.Perennial.zero_val reflect.Value)
  rwa [hf, isNil_panic_kinds.2.2] at h

/-! ## `Value.IsValid`, `CanAddr`, `CanSet`, `CanInterface` -/

theorem Value.wp_IsValid_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"IsValid")) (Val #()))
    {{ RET #true; True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_IsValid : reflect.Value.IsValid.spec (GF := GF) (hG := hG)) w
  rwa [hf, decide_eq_true ptrFlag_bits.2.1] at h

theorem Value.wp_IsValid_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"IsValid")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have h := (reflect.Value.wp_IsValid : reflect.Value.IsValid.spec (GF := GF) (hG := hG)) v
  rwa [hf, decide_eq_true (elemFlag_bits k (kindOf_lt hk)).2.1] at h

theorem Value.wp_IsValid_zero :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((_root_.Perennial.zero_val reflect.Value) @!! Value.ty @!! go!"IsValid"))
        (Val #()))
    {{ RET #false; True }} := by
  have hf : (_root_.Perennial.zero_val reflect.Value).flag' = W64 0 := rfl
  have h := (reflect.Value.wp_IsValid : reflect.Value.IsValid.spec (GF := GF) (hG := hG)) (_root_.Perennial.zero_val reflect.Value)
  rwa [hf, decide_eq_false (fun h => h rfl)] at h

theorem Value.wp_CanAddr_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanAddr")) (Val #()))
    {{ RET #false; True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_CanAddr : reflect.Value.CanAddr.spec (GF := GF) (hG := hG)) w
  rwa [hf, decide_eq_false (fun h => h ptrFlag_bits.2.2.1)] at h

theorem Value.wp_CanAddr_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanAddr")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have h := (reflect.Value.wp_CanAddr : reflect.Value.CanAddr.spec (GF := GF) (hG := hG)) v
  rwa [hf, decide_eq_true (elemFlag_bits k (kindOf_lt hk)).2.2.1] at h

theorem Value.wp_CanSet_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanSet")) (Val #()))
    {{ RET #false; True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_CanSet : reflect.Value.CanSet.spec (GF := GF) (hG := hG)) w
  rwa [hf, decide_eq_false ptrFlag_bits.2.2.2.1] at h

theorem Value.wp_CanSet_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanSet")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have h := (reflect.Value.wp_CanSet : reflect.Value.CanSet.spec (GF := GF) (hG := hG)) v
  rwa [hf, decide_eq_true (elemFlag_bits k (kindOf_lt hk)).2.2.2.1] at h

theorem Value.wp_CanInterface_reflPtr (w : Value) (T : go.GoType) (p : Loc)
    (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanInterface")) (Val #()))
    {{ RET #true; True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_CanInterface : reflect.Value.CanInterface.spec (GF := GF) (hG := hG)) w
    (by rw [hf]; exact ptrFlag_bits.2.1)
  rwa [hf, decide_eq_true ptrFlag_bits.2.2.2.2.1] at h

theorem Value.wp_CanInterface_reflElem (v : Value) (T : go.GoType) (p : Loc)
    (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanInterface")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hb := elemFlag_bits k (kindOf_lt hk)
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have h := (reflect.Value.wp_CanInterface : reflect.Value.CanInterface.spec (GF := GF) (hG := hG)) v (by rw [hf]; exact hb.2.1)
  rwa [hf, decide_eq_true hb.2.2.2.2.1] at h

/-! ## `Value.Type` -/

theorem Value.wp_Type_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Type")) (Val #()))
    {{ (rt : Type'), RET #rt; ⌜reflType rt (go.PointerType T)⌝ }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have ht : w.typ_' = go.tok (go.PointerType T) := by rw [h]
  iintro %Φ #Hinit HΦ
  wp_apply reflect.Value.wp_Type w (by rw [hf]; exact ptrFlag_bits.2.1)
    (by rw [hf]; exact ptrFlag_bits.2.2.2.2.2.1)
  iapply HΦ
  ipureintro
  rw [ht]
  rfl

theorem Value.wp_Type_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Type")) (Val #()))
    {{ (rt : Type'), RET #rt; ⌜reflType rt T⌝ }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hb := elemFlag_bits k (kindOf_lt hk)
  have hf : v.flag' = W64 k ||| W64 128 ||| W64 256 := by rw [hv]
  have ht : v.typ_' = go.tok T := by rw [hv]
  iintro %Φ #Hinit HΦ
  wp_apply reflect.Value.wp_Type v (by rw [hf]; exact hb.2.1) (by rw [hf]; exact hb.2.2.2.2.2)
  iapply HΦ
  ipureintro
  rw [ht]
  rfl

/-! ## `Value.Interface` -/

/-- `w.Interface()` of a `reflPtr`: `any(p)`. -/
theorem Value.wp_Interface_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Interface")) (Val #()))
    {{ RET #(interface.mkOk (go.PointerType T) #p); True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  exact reflect.Value.wp_Interface w T p (by rw [h]) (by rw [h]) (by rw [hf]; exact ptrFlag_bits.1)
    (by rw [hf]; exact ptrFlag_bits.2.2.2.2.2.2.2.1)

/-! ## `Value.Elem` -/

/-- `w.Elem()` of a `reflPtr` for a non-nil `p`: a `reflElem`. -/
theorem Value.wp_Elem_reflPtr (w : Value) (T : go.GoType) (p : Loc) (k : Nat)
    (h : reflPtr w T p) (hk : go.kindOf (GoSemanticsFunctions.underlying T) = some k)
    (hp : p ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Elem")) (Val #()))
    {{ (e : Value), RET #e; ⌜reflElem e T p⌝ }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  iintro %Φ #Hinit HΦ
  wp_apply reflect.Value.wp_Elem w T k p hk (by rw [h]) (by rw [h])
    (by rw [hf]; exact ptrFlag_bits.1) (by rw [hf]; exact ptrFlag_bits.2.2.2.2.2.2.2.2)
  rw [ite_eq_right hp, hf, elemOfPtr_flag k (kindOf_lt hk)]
  iapply HΦ
  ipureintro
  exact ⟨k, hk, rfl⟩

/-- `w.Elem()` of a `reflPtr` for a nil `p`: the zero `Value`. -/
theorem Value.wp_Elem_reflPtr_nil (w : Value) (T : go.GoType) (k : Nat)
    (h : reflPtr w T null) (hk : go.kindOf (GoSemanticsFunctions.underlying T) = some k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Elem")) (Val #()))
    {{ RET #(_root_.Perennial.zero_val reflect.Value); True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  have h := (reflect.Value.wp_Elem : reflect.Value.Elem.spec (GF := GF) (hG := hG)) w T k null hk (by rw [h]) (by rw [h])
    (by rw [hf]; exact ptrFlag_bits.1) (by rw [hf]; exact ptrFlag_bits.2.2.2.2.2.2.2.2)
  rwa [ite_eq_left rfl] at h

/-! ## `Value.IsNil` -/

/-- `w.IsNil()` of a `reflPtr`: whether `p` is nil. -/
theorem Value.wp_IsNil_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"IsNil")) (Val #()))
    {{ RET #(decide (p = null)); True }} := by
  have hf : w.flag' = W64 22 := by rw [h]
  exact (reflect.Value.wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG)).1 w (t := go.PointerType T) (e := T) p
    (by rw [hf]; exact ptrFlag_bits.1) (by rw [hf]; exact ptrFlag_bits.2.2.2.2.2.2.1) (by rw [h])

/-- `v.IsNil()` of a `reflElem` of a slice variable `p`: whether the slice `*p` is nil. -/
theorem Value.wp_IsNil_reflElem_slice (v : Value) (T : go.GoType) (p : Loc) (dq : DFrac)
    (s : GoSlice) (h : reflElem v (go.SliceType T) p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗ p ↦{dq} s }}
      (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #()))
    {{ RET #(decide (s = slice.nil)); p ↦{dq} s }} := by
  obtain ⟨k, hk, hv⟩ := h
  have hk23 : k = 23 := by
    have : go.kindOf (go.SliceType T) = some 23 := by simp [go.kindOf]
    rw [show GoSemanticsFunctions.underlying (go.SliceType T) = go.SliceType T from
      go.is_underlying, this] at hk
    cases hk; rfl
  subst hk23
  have hf : v.flag' = W64 23 ||| W64 128 ||| W64 256 := by rw [hv]; rfl
  exact (reflect.Value.wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG)).2.1 v (t := go.SliceType T) (e := T) p dq s
    (by rw [hf]; exact (elemFlag_bits 23 (by omega)).1) (by rw [hv])

/-- `IsNil()` of the zero `Value`: Go's panic `&ValueError{"reflect.Value.IsNil", Invalid}`. -/
theorem Value.wp_IsNil_zero (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      (∀ l : Loc, l ↦ ValueError.mk go!"reflect.Value.IsNil" (W64 0) -∗
        Φ (PanicV #(interface.mkOk (go.PointerType ValueError.ty) #l))) ⊢
      WP (App (Val ((_root_.Perennial.zero_val reflect.Value) @!! Value.ty @!! go!"IsNil"))
        (Val #())) {{ Φ }} := by
  have hf : (_root_.Perennial.zero_val reflect.Value).flag' &&& W64 31 = W64 0 := by
    rw [show (_root_.Perennial.zero_val reflect.Value).flag' = W64 0 from rfl]
    exact isNil_panic_kinds.2.2
  have h := (reflect.Value.wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG)).2.2
    (_root_.Perennial.zero_val reflect.Value) Φ (by rw [hf]; exact isNil_panic_kinds.1)
  rwa [hf] at h

/-- `v.IsNil()` of a `reflElem` of a struct variable: Go's panic
`&ValueError{"reflect.Value.IsNil", Struct}`. -/
theorem Value.wp_IsNil_reflElem_struct (v : Value) (T : go.GoType) (p : Loc)
    (h : reflElem v T p) (hk : go.kindOf (GoSemanticsFunctions.underlying T) = some 25)
    (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      (∀ l : Loc, l ↦ ValueError.mk go!"reflect.Value.IsNil" (W64 25) -∗
        Φ (PanicV #(interface.mkOk (go.PointerType ValueError.ty) #l))) ⊢
      WP (App (Val (v @!! Value.ty @!! go!"IsNil")) (Val #())) {{ Φ }} := by
  obtain ⟨k, hk', hv⟩ := h
  rw [hk] at hk'
  cases hk'
  have hf : v.flag' &&& W64 31 = W64 25 := by
    rw [show v.flag' = W64 25 ||| W64 128 ||| W64 256 by rw [hv]; rfl]
    exact (elemFlag_bits 25 (by omega)).1
  have h := (reflect.Value.wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG)).2.2 v Φ
    (by rw [hf]; exact isNil_panic_kinds.2.1)
  rwa [hf] at h

/-- `w.IsNil()` of the `Value` that `ValueOf` returns for a struct value that is not direct
(`wp_ValueOf_struct_indirect`): Go's panic `&ValueError{"reflect.Value.IsNil", Struct}`. -/
theorem Value.wp_IsNil_struct_value (t : go.GoType) (q : Loc) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      (∀ l : Loc, l ↦ ValueError.mk go!"reflect.Value.IsNil" (W64 25) -∗
        Φ (PanicV #(interface.mkOk (go.PointerType ValueError.ty) #l))) ⊢
      WP (App (Val ((Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q)
        (W64 25 ||| W64 128)) @!! Value.ty @!! go!"IsNil")) (Val #())) {{ Φ }} := by
  have hf : (Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q)
      (W64 25 ||| W64 128)).flag' &&& W64 31 = W64 25 := by
    show (W64 25 ||| W64 128) &&& W64 31 = W64 25
    decide
  have h := (reflect.Value.wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG)).2.2
    (Value.mk (go.tok t) (interface.mkOk (go.PointerType t) #q) (W64 25 ||| W64 128)) Φ
    (by rw [hf]; exact isNil_panic_kinds.2.1)
  rwa [hf] at h

/-! ## `Type.Elem` and `Type.Kind`, through the interface `reflect.Type` -/

/-- `rt.Elem()` of the `Type` of an array, channel, map, pointer or slice type `T`: the `Type` of
its element type `e`. -/
theorem Type.wp_Elem (rt : Type') (T e : go.GoType) {u : go.GoType} [T ↓u u]
    (h : reflType rt T) (he : go.typeQuery .elem T 0 = some #(go.tok e)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (App (Val (GoInstruction (MethodResolve Type'.ty go!"Elem"))) (Val #rt)) (Val #()))
    {{ (et : Type'), RET #et; ⌜reflType et e⌝ }} := by
  subst h
  iintro %Φ #Hinit HΦ
  wp_pures
  unfold go.tok
  wp_apply reflect.rtype.wp_Elem e null he $$ [$Hinit]
  iapply HΦ
  ipureintro
  rfl

theorem Type.wp_Elem_slice (rt : Type') (T : go.GoType) (h : reflType rt (go.SliceType T)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (App (Val (GoInstruction (MethodResolve Type'.ty go!"Elem"))) (Val #rt)) (Val #()))
    {{ (et : Type'), RET #et; ⌜reflType et T⌝ }} :=
  Type.wp_Elem rt (go.SliceType T) T h (by simp [go.typeQuery, go.is_underlying])

theorem Type.wp_Elem_pointer (rt : Type') (T : go.GoType) (h : reflType rt (go.PointerType T)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (App (Val (GoInstruction (MethodResolve Type'.ty go!"Elem"))) (Val #rt)) (Val #()))
    {{ (et : Type'), RET #et; ⌜reflType et T⌝ }} :=
  Type.wp_Elem rt (go.PointerType T) T h (by simp [go.typeQuery, go.is_underlying])

/-- `rt.Kind()` of the `Type` of `T`: `T`'s kind. -/
theorem Type.wp_Kind (rt : Type') (T : go.GoType) {u : go.GoType} [T ↓u u] (k : Nat)
    (h : reflType rt T) (hk : go.kindOf u = some k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (App (Val (GoInstruction (MethodResolve Type'.ty go!"Kind"))) (Val #rt)) (Val #()))
    {{ RET #(W64 k); True }} := by
  subst h
  iintro %Φ #Hinit HΦ
  wp_pures
  unfold go.tok
  wp_apply reflect.rtype.wp_Kind k null hk $$ [$Hinit]
  iapply HΦ
  itrivial

/-! ## `Kind.String` -/

/-- `Pointer.String()`: `"ptr"`. -/
theorem Kind.wp_String_pointer :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((W64 22 : w64) @!! Kind.ty @!! go!"String")) (Val #()))
    {{ RET #(go!"ptr"); True }} :=
  (reflect.Kind.wp_String : reflect.Kind.String.spec (GF := GF) (hG := hG)) (W64 22) _ rfl

/-- `Struct.String()`: `"struct"`. -/
theorem Kind.wp_String_struct :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((W64 25 : w64) @!! Kind.ty @!! go!"String")) (Val #()))
    {{ RET #(go!"struct"); True }} :=
  (reflect.Kind.wp_String : reflect.Kind.String.spec (GF := GF) (hG := hG)) (W64 25) _ rfl

end results

end reflect

end Perennial
