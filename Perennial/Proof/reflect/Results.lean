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

/-- A kind is below 32 (it fits the kind bits of a flag). -/
theorem kindOf_lt {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : k < 27 := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- The flag bits of a `reflElem`: kind `k`, `flagIndir` and `flagAddr`. -/
theorem elemFlag_bits (k : Nat) (hk : k < 27) :
    (W64 k ||| W64 128 ||| W64 256) &&& W64 31 = W64 k ∧
    (W64 k ||| W64 128 ||| W64 256) ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 256 ≠ W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 352 = W64 256 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 96 = W64 0 ∧
    (W64 k ||| W64 128 ||| W64 256) &&& W64 512 = W64 0 := by
  interval_cases k <;> decide

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-! ## `Value.Kind` -/

theorem Value.wp_Kind_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 22); True }} := by
  subst h
  exact reflect.Value.wp_Kind _

theorem Value.wp_Kind_reflElem (v : Value) (T : go.GoType) (p : Loc) (k : Nat)
    (h : reflElem v T p) (hk : go.kindOf (go.underlying T) = some k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 k); True }} := by
  obtain ⟨k', hk', rfl⟩ := h
  rw [hk] at hk'
  cases hk'
  have := (elemFlag_bits k (kindOf_lt hk)).1
  have h := reflect.Value.wp_Kind (GF := GF) (hG := hG)
    (Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p) (W64 k ||| W64 128 ||| W64 256))
  simp only [this] at h
  exact h

theorem Value.wp_Kind_zero :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((zero_val Value) @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W64 0); True }} :=
  reflect.Value.wp_Kind _

/-! ## `Value.IsValid`, `CanAddr`, `CanSet`, `CanInterface` -/

theorem Value.wp_IsValid_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"IsValid")) (Val #()))
    {{ RET #true; True }} := by
  subst h
  have h := reflect.Value.wp_IsValid (GF := GF) (hG := hG)
    (Value.mk (go.tok (go.PointerType T)) (interface.mkOk (go.PointerType T) #p) (W64 22))
  simpa using h

theorem Value.wp_IsValid_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"IsValid")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, rfl⟩ := h
  have hb := (elemFlag_bits k (kindOf_lt hk)).2.1
  have h := reflect.Value.wp_IsValid (GF := GF) (hG := hG)
    (Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p) (W64 k ||| W64 128 ||| W64 256))
  simpa [hb] using h

theorem Value.wp_IsValid_zero :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((zero_val Value) @!! Value.ty @!! go!"IsValid")) (Val #()))
    {{ RET #false; True }} := by
  have h := reflect.Value.wp_IsValid (GF := GF) (hG := hG) (zero_val Value)
  simpa using h

theorem Value.wp_CanAddr_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanAddr")) (Val #()))
    {{ RET #false; True }} := by
  subst h
  have h := reflect.Value.wp_CanAddr (GF := GF) (hG := hG)
    (Value.mk (go.tok (go.PointerType T)) (interface.mkOk (go.PointerType T) #p) (W64 22))
  simpa using h

theorem Value.wp_CanAddr_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanAddr")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, rfl⟩ := h
  have hb := (elemFlag_bits k (kindOf_lt hk)).2.2.1
  have h := reflect.Value.wp_CanAddr (GF := GF) (hG := hG)
    (Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p) (W64 k ||| W64 128 ||| W64 256))
  simpa [hb] using h

theorem Value.wp_CanSet_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanSet")) (Val #()))
    {{ RET #false; True }} := by
  subst h
  have h := reflect.Value.wp_CanSet (GF := GF) (hG := hG)
    (Value.mk (go.tok (go.PointerType T)) (interface.mkOk (go.PointerType T) #p) (W64 22))
  simpa using h

theorem Value.wp_CanSet_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanSet")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, rfl⟩ := h
  have hb := (elemFlag_bits k (kindOf_lt hk)).2.2.2.1
  have h := reflect.Value.wp_CanSet (GF := GF) (hG := hG)
    (Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p) (W64 k ||| W64 128 ||| W64 256))
  simpa [hb] using h

theorem Value.wp_CanInterface_reflPtr (w : Value) (T : go.GoType) (p : Loc)
    (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"CanInterface")) (Val #()))
    {{ RET #true; True }} := by
  subst h
  have h := reflect.Value.wp_CanInterface (GF := GF) (hG := hG)
    (Value.mk (go.tok (go.PointerType T)) (interface.mkOk (go.PointerType T) #p) (W64 22))
    (by decide)
  simpa using h

theorem Value.wp_CanInterface_reflElem (v : Value) (T : go.GoType) (p : Loc)
    (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanInterface")) (Val #()))
    {{ RET #true; True }} := by
  obtain ⟨k, hk, rfl⟩ := h
  have hb := elemFlag_bits k (kindOf_lt hk)
  have h := reflect.Value.wp_CanInterface (GF := GF) (hG := hG)
    (Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #p) (W64 k ||| W64 128 ||| W64 256))
    hb.2.1
  simpa [hb.2.2.2.2.1] using h

/-! ## `Value.Type` -/

theorem Value.wp_Type_reflPtr (w : Value) (T : go.GoType) (p : Loc) (h : reflPtr w T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (w @!! Value.ty @!! go!"Type")) (Val #()))
    {{ (rt : Type'), RET #rt; ⌜reflType rt (go.PointerType T)⌝ }} := by
  subst h
  iintro %Φ #Hinit HΦ
  wp_apply reflect.Value.wp_Type _ (by decide) (by decide) $$ [$Hinit]
  iapply HΦ
  ipureintro
  rfl

theorem Value.wp_Type_reflElem (v : Value) (T : go.GoType) (p : Loc) (h : reflElem v T p) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Type")) (Val #()))
    {{ (rt : Type'), RET #rt; ⌜reflType rt T⌝ }} := by
  obtain ⟨k, hk, rfl⟩ := h
  have hb := elemFlag_bits k (kindOf_lt hk)
  iintro %Φ #Hinit HΦ
  wp_apply reflect.Value.wp_Type _ hb.2.1 hb.2.2.2.2.2 $$ [$Hinit]
  iapply HΦ
  ipureintro
  rfl

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
  wp_apply reflect.rtype.wp_Kind k null hk $$ [$Hinit]
  iapply HΦ
  itrivial

end results

end reflect

end Perennial
