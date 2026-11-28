/-
WP lemmas of the reflection primitives (`Perennial/GooseLang/Ext/Reflect/Impl.lean`), as triples
of their operations on the values the stubs of `internal/reflectcore` pass, with the steps after
them; they need `[HasExt reflectExt]`.
-/
module

public import Perennial.Golang.Theory.Pre
public import Perennial.GooseLang.Ext.Reflect.Specs

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section layout
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

/-- A type of which `typeQuery` answers a question other than `identByName` is not
`go.layoutModelled`. -/
theorem go.notLayoutModelled_of_typeQuery {q : go.TypeQ} {t : go.GoType} {i : Int} {v : val}
    (h : go.typeQuery q t i = some v) (hq : q ≠ .identByName) : go.layoutModelled t = false := by
  cases hm : go.layoutModelled t
  · rfl
  · unfold go.typeQuery at h
    simp [hm, hq] at h

instance go.NotLayoutModelled.error : go.NotLayoutModelled go.error := ⟨rfl⟩

/-- A pointer to a type that is not `go.layoutModelled` is not exposed to a conversion
(`go.convertExposed`). -/
theorem go.convertExposed_pointer (T : go.GoType) [hm : go.NotLayoutModelled T]
    [go.PointerType T ↓u go.PointerType T] : go.convertExposed (go.PointerType T) = false := by
  have h : underlying (go.PointerType T) = go.PointerType T := go.is_underlying
  simp only [go.convertExposed, h, hm.not_layout_modelled]
  rfl

end layout

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt reflectExt]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-! ## `FuncResolveAt` -/

/-- `FuncResolveAt` of the shape `sh` and one dispatch interface. -/
theorem wp_FuncResolveAt (sh : go.Shape) (f : GoString) (t : go.GoType) (v : val)
    (ts : List go.GoType) (h : go.shapeArgs sh t = some ts) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "FuncResolveAt"
        (Val (PairV (go.funcAtArg f [sh]) #(interface.mkOk t v)))) @ s; E
    {{ RET #(functions f ts); True }} := by
  rw [show (#(interface.mkOk t v) : val) = go.dispatchArgs [interface.mk t v] from rfl]
  iintro %Φ _ HΦ
  iapply wp_reflect_FuncResolveAt f [sh] [interface.mk t v] ts (by simp [go.shapesArgs, h])
  inext
  wp_pures
  iapply HΦ
  itrivial

/-- `FuncResolveAt` of the shapes `sh1`, `sh2` and two dispatch interfaces. -/
theorem wp_FuncResolveAt_pair (sh1 sh2 : go.Shape) (f : GoString) (t1 t2 : go.GoType)
    (v1 v2 : val) (ts1 ts2 : List go.GoType) (h1 : go.shapeArgs sh1 t1 = some ts1)
    (h2 : go.shapeArgs sh2 t2 = some ts2) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "FuncResolveAt"
        (Val (PairV (go.funcAtArg f [sh1, sh2])
          (PairV #(interface.mkOk t1 v1) #(interface.mkOk t2 v2))))) @ s; E
    {{ RET #(functions f (ts1 ++ ts2)); True }} := by
  rw [show PairV #(interface.mkOk t1 v1) #(interface.mkOk t2 v2) =
    go.dispatchArgs [interface.mk t1 v1, interface.mk t2 v2] from rfl]
  iintro %Φ _ HΦ
  iapply wp_reflect_FuncResolveAt f [sh1, sh2] [interface.mk t1 v1, interface.mk t2 v2]
    (ts1 ++ ts2) (by simp [go.shapesArgs, h1, h2])
  inext
  wp_pures
  iapply HΦ
  itrivial

/-! ## `ConvertAt` -/

/-- `ConvertAt` to a non-interface type `u` that a `Convert` rule converts `t` to in one pure
step. -/
theorem wp_ConvertAt {t u uu : go.GoType} [u ↓u uu] (hu : go.isInterfaceType uu = false)
    (hn : go.isUntypedNil uu = false) {X Y : Type} (x : X) (y : Y)
    [go.IsGoStepPureDet (Convert t u) #x (Val #y)] (l : Loc)
    (het : go.convertExposed t = false) (heu : go.convertExposed u = false) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "ConvertAt"
        (Val (PairV #(interface.mkOk t #x) #(interface.mkOk (go.PointerType u) #l)))) @ s; E
    {{ RET #(interface.mkOk u #y); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_ConvertAt t u #x l
    (by rw [go.is_underlying (t := u), hu]; exact fun h => nomatch h) het heu
  inext
  rw [go.is_underlying (t := u), hu]
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_pures
  rw [hu, hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply HΦ
  itrivial

/-- `ConvertAt` of `x : t` to `t` itself, a non-interface type. -/
theorem wp_ConvertAt_same {t tu : go.GoType} [t ↓u tu] (hu : go.isInterfaceType tu = false)
    (hn : go.isUntypedNil tu = false) {X : Type} (x : X) (l : Loc)
    (he : go.convertExposed t = false) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "ConvertAt"
        (Val (PairV #(interface.mkOk t #x) #(interface.mkOk (go.PointerType t) #l)))) @ s; E
    {{ RET #(interface.mkOk t #x); True }} :=
  wp_ConvertAt hu hn x x l he he

/-- `ConvertAt` to an interface type `u` that `t` implements: `x` itself. -/
theorem wp_ConvertAt_interface {t u uu : go.GoType} [u ↓u uu] (hu : go.isInterfaceType uu = true)
    (himpl : go.typeSetContains t u = true) (v : val) (l : Loc)
    (het : go.convertExposed t = false) (heu : go.convertExposed u = false) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "ConvertAt"
        (Val (PairV #(interface.mkOk t v) #(interface.mkOk (go.PointerType u) #l)))) @ s; E
    {{ RET #(interface.mkOk t v); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_ConvertAt t u v l (fun _ => himpl) het heu
  inext
  rw [go.is_underlying (t := u), hu]
  simp only [↓reduceIte]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `FieldRefAt` and `ArraySliceAt` -/

/-- `FieldRefAt` of a non-null pointer to a struct and the index of a non-blank field. -/
theorem wp_FieldRefAt {st : go.GoType} {fs : List go.field_decl} [st ↓u go.StructType fs]
    [hm : go.NotLayoutModelled st]
    {V : Type} [ZeroVal V] [TypeRepr (go.StructType fs) V] (l : Loc) (i : w64)
    (fd : go.field_decl) (hl : l ≠ null) (hi : 0 ≤ sint.Z i) (hfd : fs[sint.nat i]? = some fd)
    (hblank : go.isBlankField (go.fieldDeclName fd) = false) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "FieldRefAt"
        (Val (PairV #(interface.mkOk (go.PointerType st) #l) #i))) @ s; E
    {{ RET #(interface.mkOk (go.PointerType (go.fieldDeclType fd))
        #(structFieldRef V (go.fieldDeclName fd) l)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_FieldRefAt st fs l i fd go.is_underlying hm.not_layout_modelled hl hi hfd
    hblank
  inext
  wp_pures
  iapply HΦ
  itrivial

/-- `ArraySliceAt` of a non-null pointer to an array: the slice of all its elements. -/
theorem wp_ArraySliceAt {a e : go.GoType} {n : Int} [a ↓u go.ArrayType n e]
    [hm : go.NotLayoutModelled a] {V : Type}
    [ZeroVal V] [TypeRepr e V] (l : Loc) (hl : l ≠ null) (hn : 0 ≤ n ∧ n < 2 ^ 63) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "ArraySliceAt" (Val #(interface.mkOk (go.PointerType a) #l)))
        @ s; E
    {{ RET #(interface.mkOk (go.SliceType e) #(slice.mk l (W64 n) (W64 n))); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_ArraySliceAt a e n l go.is_underlying hm.not_layout_modelled hl
  inext
  wp_pures
  have hz : sint.Z (W64 n) = n := word.toInt_ofInt_eq n (by omega)
  have h0 : sint.Z (W64 0) = 0 := rfl
  simp only [h0, hz, Int.le_refl, hn.1, _root_.and_self, ↓reduceIte, go.arrayIndexRef_0,
    show W64 n - W64 0 = W64 n from BitVec.sub_zero _]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `EqNilAt` -/

theorem wp_EqNilAt_pointer {t e : go.GoType} [t ↓u go.PointerType e]
    [hm : go.NotLayoutModelled t] (l : Loc) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t #l))) @ s; E
    {{ RET #(decide (l = null)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_EqNilAt t #l (by rw [go.is_underlying (t := t)]; exact .pointer e)
    hm.not_layout_modelled
  inext
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_slice {t e : go.GoType} [t ↓u go.SliceType e]
    [hm : go.NotLayoutModelled t] (sl : GoSlice) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t #sl))) @ s; E
    {{ RET #(decide (sl = slice.nil)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_EqNilAt t #sl (by rw [go.is_underlying (t := t)]; exact .slice e)
    hm.not_layout_modelled
  inext
  wp_pures
  rw [show zero_val GoSlice = slice.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_map {t k v : go.GoType} [t ↓u go.MapType k v]
    [hm : go.NotLayoutModelled t] (m : GoMap) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t #m))) @ s; E
    {{ RET #(decide (m = map.nil)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_EqNilAt t #m (by rw [go.is_underlying (t := t)]; exact .map k v)
    hm.not_layout_modelled
  inext
  wp_pures
  rw [show zero_val GoMap = map.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_chan {t e : go.GoType} {d : go.ChanDir} [t ↓u go.ChannelType d e]
    [hm : go.NotLayoutModelled t]
    (c : GoChan) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t #c))) @ s; E
    {{ RET #(decide (c = null)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_EqNilAt t #c (by rw [go.is_underlying (t := t)]; exact .chan d e)
    hm.not_layout_modelled
  inext
  wp_pures
  iapply HΦ
  itrivial

theorem wp_EqNilAt_func {t : go.GoType} {sig : go.signature} [t ↓u go.FunctionType sig]
    [hm : go.NotLayoutModelled t]
    (f : GoFunc) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t #f))) @ s; E
    {{ RET #(decide (f = func.nil)); True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_EqNilAt t #f (by rw [go.is_underlying (t := t)]; exact .func sig)
    hm.not_layout_modelled
  inext
  wp_pures
  rw [show zero_val GoFunc = func.nil from rfl]
  wp_pures
  iapply HΦ
  itrivial

/-! ## `TypeQuery` -/

theorem wp_TypeQuery (o : String) (q : go.TypeQ) (hq : go.TypeQ.ofOp o = some q) (t : go.GoType)
    (l : Loc) (i : w64) (v : val) (h : go.typeQuery q t (sint.Z i) = some v) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName o
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET v; True }} := by
  iintro %Φ _ HΦ
  iapply wp_reflect_TypeQuery o q hq t l i v h
  inext
  iapply wp_value'
  iapply HΦ
  itrivial

theorem wp_TypeQuery_kind {t u : go.GoType} [t ↓u u] [hm : go.NotLayoutModelled t] (k : Nat)
    (hk : go.kindOf u = some k) (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "TypeQuery.kind"
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(W64 k); True }} :=
  wp_TypeQuery (s := s) (E := E) "TypeQuery.kind" .kind rfl t l i _
    (by simp [go.typeQuery, go.is_underlying, hk, hm.not_layout_modelled])

theorem wp_TypeQuery_elem_pointer {t e : go.GoType} [t ↓u go.PointerType e]
    [hm : go.NotLayoutModelled t] (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "TypeQuery.elem"
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(go.tok e); True }} :=
  wp_TypeQuery (s := s) (E := E) "TypeQuery.elem" .elem rfl t l i _
    (by simp [go.typeQuery, go.is_underlying, hm.not_layout_modelled])

theorem wp_TypeQuery_elem_slice {t e : go.GoType} [t ↓u go.SliceType e]
    [hm : go.NotLayoutModelled t] (l : Loc) (i : w64) :
    {{ (True : IProp GF) }}
      (ExternalOp reflectExtName "TypeQuery.elem"
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E
    {{ RET #(go.tok e); True }} :=
  wp_TypeQuery (s := s) (E := E) "TypeQuery.elem" .elem rfl t l i _
    (by simp [go.typeQuery, go.is_underlying, hm.not_layout_modelled])

end wps

end Perennial
