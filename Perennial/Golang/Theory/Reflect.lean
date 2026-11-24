/-
WP lemmas of the reflection primitives (`Perennial/Golang/Defn/Reflect.lean`). The rules with a
premise (`FuncResolveAt`, `FieldRefAt`, `ArraySliceAt`, `TypeQuery`) are stepped by these lemmas
(`wp_apply`); the others are instances, which `wp_pures` steps, and their lemmas here also take
the steps after them.
-/
module

public import Perennial.Golang.Theory.Pre

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- A deterministic pure step of an instruction, as a triple. -/
theorem wp_go_step_val (i : GoInstruction) (v w : val) [go.IsGoStepPureDet i v (Val w)]
    (hv : v.isPanic = false) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction i)) (Val v)) @ s; E {{ RET w; True }} := by
  iintro %Φ _ HΦ
  iapply wp_go_step_receipt' _ _ _ Φ hv
  inext
  iintro _ _
  iapply wp_value'
  iapply HΦ
  itrivial

/-! ## `FuncResolveAt` -/

/-- `FuncResolveAt [sh] f` of one dispatch interface. -/
theorem wp_FuncResolveAt (sh : go.Shape) (f : GoString) (t : go.GoType) (v : val)
    (ts : List go.GoType) (h : go.shapeArgs sh t = some ts) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (FuncResolveAt [sh] f))) (Val #(interface.mkOk t v))) @ s; E
    {{ RET #(functions f ts); True }} := by
  haveI : go.IsGoStepPureDet (FuncResolveAt [sh] f) #(interface.mkOk t v)
      (Val #(functions f ts)) :=
    go.func_resolve_at_step [sh] f [interface.mk t v] ts (by simp [go.shapesArgs, h])
  exact wp_go_step_val _ _ _ (by simp)

/-- `FuncResolveAt [sh1, sh2] f` of two dispatch interfaces. -/
theorem wp_FuncResolveAt_pair (sh1 sh2 : go.Shape) (f : GoString) (t1 t2 : go.GoType)
    (v1 v2 : val) (ts1 ts2 : List go.GoType) (h1 : go.shapeArgs sh1 t1 = some ts1)
    (h2 : go.shapeArgs sh2 t2 = some ts2) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (FuncResolveAt [sh1, sh2] f)))
        (Val (PairV #(interface.mkOk t1 v1) #(interface.mkOk t2 v2)))) @ s; E
    {{ RET #(functions f (ts1 ++ ts2)); True }} := by
  haveI : go.IsGoStepPureDet (FuncResolveAt [sh1, sh2] f)
      (PairV #(interface.mkOk t1 v1) #(interface.mkOk t2 v2)) (Val #(functions f (ts1 ++ ts2))) :=
    go.func_resolve_at_step [sh1, sh2] f [interface.mk t1 v1, interface.mk t2 v2] (ts1 ++ ts2)
      (by simp [go.shapesArgs, h1, h2])
  exact wp_go_step_val _ _ _ rfl

/-! ## `ConvertAt` -/

/-- `ConvertAt` to a non-interface type `u` that `t` converts to in one pure step. -/
theorem wp_ConvertAt {t u uu : go.GoType} [u ↓u uu] (hu : go.isInterfaceType uu = false)
    (hn : go.isUntypedNil uu = false) {X Y : Type} (x : X) (y : Y)
    [go.IsGoStepPureDet (Convert t u) #x (Val #y)] (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction ConvertAt))
        (Val (PairV #(interface.mkOk t #x) #(interface.mkOk (go.PointerType u) #l)))) @ s; E
    {{ RET #(interface.mkOk u #y); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  rw [go.is_underlying, hu]
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_pures
  rw [hu, hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply HΦ
  itrivial

/-- `ConvertAt` of `x : t` to `t` itself, a non-interface type. -/
theorem wp_ConvertAt_same {t tu : go.GoType} [t ↓u tu] (hu : go.isInterfaceType tu = false)
    (hn : go.isUntypedNil tu = false) {X : Type} (x : X) (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction ConvertAt))
        (Val (PairV #(interface.mkOk t #x) #(interface.mkOk (go.PointerType t) #l)))) @ s; E
    {{ RET #(interface.mkOk t #x); True }} :=
  wp_ConvertAt hu hn x x l

/-- `ConvertAt` to an interface type `u` that `t` implements: `x` itself. -/
theorem wp_ConvertAt_interface {t u uu : go.GoType} [u ↓u uu] (hu : go.isInterfaceType uu = true)
    (himpl : go.typeSetContains t u = true) (v : val) (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction ConvertAt))
        (Val (PairV #(interface.mkOk t v) #(interface.mkOk (go.PointerType u) #l)))) @ s; E
    {{ RET #(interface.mkOk t v); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  rw [go.is_underlying, hu, himpl]
  simp only [↓reduceIte]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `FieldRefAt` and `ArraySliceAt` -/

/-- `FieldRefAt` of a non-null pointer to a struct and the index of a non-blank field. -/
theorem wp_FieldRefAt {st : go.GoType} {fs : List go.field_decl} [st ↓u go.StructType fs]
    {V : Type} [ZeroVal V] [TypeRepr (go.StructType fs) V] (l : Loc) (i : w64)
    (fd : go.field_decl) (hl : l ≠ null) (hi : 0 ≤ sint.Z i) (hfd : fs[sint.nat i]? = some fd)
    (hblank : go.isBlankField (go.fieldDeclName fd) = false) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction FieldRefAt))
        (Val (PairV #(interface.mkOk (go.PointerType st) #l) #i))) @ s; E
    {{ RET #(interface.mkOk (go.PointerType (go.fieldDeclType fd))
        #(structFieldRef V (go.fieldDeclName fd) l)); True }} := by
  haveI := go.field_ref_at_step (s := st) l i fd hl hi hfd hblank
  iintro %Φ _ HΦ
  iapply wp_go_step_receipt' _ _ _ Φ rfl
  inext
  iintro _ _
  wp_pures
  iapply HΦ
  itrivial

/-- `ArraySliceAt` of a non-null pointer to an array: the slice of all its elements. -/
theorem wp_ArraySliceAt {a e : go.GoType} {n : Int} [a ↓u go.ArrayType n e] {V : Type}
    [ZeroVal V] [TypeRepr e V] (l : Loc) (hl : l ≠ null) (hn : 0 ≤ n ∧ n < 2 ^ 63) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction ArraySliceAt)) (Val #(interface.mkOk (go.PointerType a) #l)))
        @ s; E
    {{ RET #(interface.mkOk (go.SliceType e) #(slice.mk l (W64 n) (W64 n))); True }} := by
  haveI := go.array_slice_at_step (a := a) l hl
  iintro %Φ _ HΦ
  iapply wp_go_step_receipt' _ _ _ Φ (by simp)
  inext
  iintro _ _
  wp_pures
  have hz : sint.Z (W64 n) = n := word.toInt_ofInt_eq n (by omega)
  have h0 : sint.Z (W64 0) = 0 := rfl
  simp only [h0, hz, Int.le_refl, hn.1, _root_.and_self, ↓reduceIte, go.arrayIndexRef_0,
    show W64 n - W64 0 = W64 n from BitVec.sub_zero _]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `EqNilAt` -/

theorem wp_EqNilAt_pointer {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction EqNilAt)) (Val #(interface.mkOk t #l))) @ s; E
    {{ RET #(decide (l = null)); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_slice {t e : go.GoType} [t ↓u go.SliceType e] (sl : GoSlice) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction EqNilAt)) (Val #(interface.mkOk t #sl))) @ s; E
    {{ RET #(decide (sl = slice.nil)); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  rw [show zero_val GoSlice = slice.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_map {t k v : go.GoType} [t ↓u go.MapType k v] (m : GoMap) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction EqNilAt)) (Val #(interface.mkOk t #m))) @ s; E
    {{ RET #(decide (m = map.nil)); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  rw [show zero_val GoMap = map.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_chan {t e : go.GoType} {d : go.ChanDir} [t ↓u go.ChannelType d e]
    (c : GoChan) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction EqNilAt)) (Val #(interface.mkOk t #c))) @ s; E
    {{ RET #(decide (c = null)); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_func {t : go.GoType} {sig : go.signature} [t ↓u go.FunctionType sig]
    (f : GoFunc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction EqNilAt)) (Val #(interface.mkOk t #f))) @ s; E
    {{ RET #(decide (f = func.nil)); True }} := by
  iintro %Φ _ HΦ
  wp_pures
  rw [show zero_val GoFunc = func.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `PointerOfAt` -/

theorem wp_PointerOfAt_pointer {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction PointerOfAt)) (Val #(interface.mkOk t #l))) @ s; E
    {{ RET #l; True }} :=
  wp_go_step_val _ _ _ (by simp)

theorem wp_PointerOfAt_slice_nil {t e : go.GoType} [t ↓u go.SliceType e] :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction PointerOfAt)) (Val #(interface.mkOk t #slice.nil))) @ s; E
    {{ RET #null; True }} :=
  wp_go_step_val _ _ _ (by simp)

theorem wp_PointerOfAt_slice {t e : go.GoType} [t ↓u go.SliceType e] (sl : GoSlice)
    (h : 0 < uint.Z sl.cap) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction PointerOfAt)) (Val #(interface.mkOk t #sl))) @ s; E
    {{ RET #sl.ptr; True }} :=
  haveI := go.pointer_of_at_slice (t := t) sl h
  wp_go_step_val _ _ _ (by simp)

/-! ## `TypeQuery` -/

theorem wp_TypeQuery (q : go.TypeQ) (t : go.GoType) (l : Loc) (i : w64) (v : val)
    (h : go.typeQuery q t (sint.Z i) = some v) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (TypeQuery q)))
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET v; True }} := by
  haveI := go.type_query_step q t l i v h
  exact wp_go_step_val _ _ _ rfl

theorem wp_TypeQuery_kind {t u : go.GoType} [t ↓u u] (k : Nat) (hk : go.kindOf u = some k)
    (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (TypeQuery .kind)))
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(W64 k); True }} :=
  wp_TypeQuery _ _ _ _ _ (by simp [go.typeQuery, go.is_underlying, hk])

theorem wp_TypeQuery_elem_pointer {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (TypeQuery .elem)))
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(go.tok e); True }} :=
  wp_TypeQuery _ _ _ _ _ (by simp [go.typeQuery, go.is_underlying])

theorem wp_TypeQuery_elem_slice {t e : go.GoType} [t ↓u go.SliceType e] (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (TypeQuery .elem)))
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(go.tok e); True }} :=
  wp_TypeQuery _ _ _ _ _ (by simp [go.typeQuery, go.is_underlying])

end wps

end Perennial
