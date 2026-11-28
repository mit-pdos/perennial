/-
Iris reasoning principles for the reflection extension (`Ext/Reflect/Impl.lean`).

* `reflect_interp`: no ghost state (the extension has no state).
* The functions of the ambient Go context that the specs are written in (`go.shapeArgs`,
  `go.shapesArgs`, `go.typeQuery`, `go.convertExposed`, `go.NotLayoutModelled`), with the lemmas
  that they are the extension's at the machine's type functions (`GoLocalContext.typeFns`).
* `wp_reflectStep`: an operation whose step from its argument is determined; and one lemma per
  operation (`wp_reflect_FuncResolveAt`, ...), each taking its case's conditions as hypotheses.
-/
module

public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Ext.Reflect.Impl
public import Perennial.Golang.Theory.PostLifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The ghost state of the reflection extension: none. -/
instance reflect_interp : ExtInterp reflectExt where
  LocalGS _ := Unit
  GlobalGS _ := Unit
  localCtx _ _ := iprop(True)
  globalCtx _ _ := iprop(True)
  PreG _ := Unit
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro
    iexists ()
    isplitl [] <;> itrivial
  local_init _ _ _ _ _ := by
    iapply bupd_intro
    iexists ()
    isplitl [] <;> itrivial

/-- The ghost state makes no assumption on the initial states. -/
instance reflect_init_compat : ExtInitCompat reflectExt where
  initgP_of_init _ _ := trivial
  initP_of_init _ _ _ := trivial

/-! ## The extension's functions in the ambient Go context -/

namespace go
section defs
variable [GooseExts] [GoLocalContext] [GoGlobalContext]

/-- The type arguments that the shape `s` gives for a dispatch argument of dynamic type `d`. -/
def shapeArgs : Shape → go.GoType → Option (List go.GoType)
  | .self, d => some [d]
  | .slice, d => match underlying d with | go.SliceType e => some [d, e] | _ => none
  | .map, d => match underlying d with | go.MapType k v => some [d, k, v] | _ => none
  | .ptr, d => match underlying d with | go.PointerType e => some [d, e] | _ => none
  | .chan c, d => match underlying d with
    | go.ChannelType c' e => if c = c' then some [d, e] else none
    | _ => none
  | .deref s, d => match d with | go.PointerType t => shapeArgs s t | _ => none

/-- `shapeArgs` of each shape and dispatch type, concatenated; none if the lengths differ. -/
def shapesArgs : List Shape → List go.GoType → Option (List go.GoType)
  | [], [] => some []
  | s :: shs, d :: ds => do
    let ts ← shapeArgs s d
    let ts' ← shapesArgs shs ds
    pure (ts ++ ts')
  | _, _ => none

/-- `TypeQuery q`'s result for the type `t` and the index `i` (`GoTypeFns.typeQuery`). -/
noncomputable def typeQuery (q : TypeQ) (t : go.GoType) (i : Int) : Option val :=
  if layoutModelled t ∧ q ≠ .identByName then none else
  match q, underlying t with
  | .kind, u => (kindOf u).map fun k => #(W64 k)
  | .numTypeArgs, _ => match t with
    | go.Named _ args => some #(W64 args.length)
    | _ => some #(W64 0)
  | .elem, go.PointerType e | .elem, go.SliceType e | .elem, go.ArrayType _ e
  | .elem, go.ChannelType _ e | .elem, go.MapType _ e => some #(tok e)
  | .key, go.MapType k _ => some #(tok k)
  | .len, go.ArrayType n _ => some #(W64 n)
  | .chanDir, go.ChannelType d _ => some #(W64 (chanDirOf d))
  | .numField, go.StructType fs => some #(W64 fs.length)
  | .fieldName, go.StructType fs => (listAt fs i).map fun fd => #(fieldNameOf fd)
  | .fieldType, go.StructType fs => (listAt fs i).map fun fd => #(tok (fieldDeclType fd))
  | .fieldEmbedded, go.StructType fs => (listAt fs i).map fun fd => #(isEmbeddedField fd)
  | .numIn, go.FunctionType (go.Signature ins _ _) => some #(W64 ins.length)
  | .inType, go.FunctionType (go.Signature ins _ _) => (listAt ins i).map fun e => #(tok e)
  | .numOut, go.FunctionType (go.Signature _ _ outs) => some #(W64 outs.length)
  | .outType, go.FunctionType (go.Signature _ _ outs) => (listAt outs i).map fun e => #(tok e)
  | .variadic, go.FunctionType (go.Signature _ v _) => some #v
  | .underlying, u => some #(tok u)
  | .identByName, _ => some #(identByName t)
  | _, _ => none

/-- `t` is not `layoutModelled`: the guard of the operations that read `t`'s representation. A
class, so that instance search finds it for the unnamed types (`rfl`). -/
class NotLayoutModelled (t : go.GoType) : Prop where
  not_layout_modelled : layoutModelled t = false

instance NotLayoutModelled.pointer (e : go.GoType) : NotLayoutModelled (go.PointerType e) := ⟨rfl⟩
instance NotLayoutModelled.slice (e : go.GoType) : NotLayoutModelled (go.SliceType e) := ⟨rfl⟩
instance NotLayoutModelled.map (k v : go.GoType) : NotLayoutModelled (go.MapType k v) := ⟨rfl⟩
instance NotLayoutModelled.chan (d : go.ChanDir) (e : go.GoType) :
    NotLayoutModelled (go.ChannelType d e) := ⟨rfl⟩
instance NotLayoutModelled.func (sig : go.signature) : NotLayoutModelled (go.FunctionType sig) :=
  ⟨rfl⟩
instance NotLayoutModelled.array (n : Int) (e : go.GoType) :
    NotLayoutModelled (go.ArrayType n e) := ⟨rfl⟩
instance NotLayoutModelled.struct (fs : List go.field_decl) :
    NotLayoutModelled (go.StructType fs) := ⟨rfl⟩
instance NotLayoutModelled.interface (elems : List go.InterfaceElem) :
    NotLayoutModelled (go.InterfaceType elems) := ⟨rfl⟩

/-- `ConvertAt`'s guard (`GoTypeFns.convertExposed`). -/
def convertExposed (t : go.GoType) : Bool :=
  layoutModelled t || match underlying t with
    | go.PointerType e => layoutModelled e
    | _ => false

/-! ### They are the extension's at the machine's type functions -/

theorem shapeArgs_eq (s : Shape) (d : go.GoType) :
    GoLocalContext.typeFns.shapeArgs s d = shapeArgs s d := by
  induction s generalizing d <;> simp only [GoTypeFns.shapeArgs, shapeArgs] <;> try rfl
  case deref s ih => cases d <;> simp only [ih]

theorem shapesArgs_eq (shs : List Shape) (ds : List go.GoType) :
    GoLocalContext.typeFns.shapesArgs shs ds = shapesArgs shs ds := by
  induction shs generalizing ds with
  | nil => cases ds <;> rfl
  | cons s shs ih => cases ds <;> simp only [GoTypeFns.shapesArgs, shapesArgs, shapeArgs_eq, ih]

theorem typeQuery_eq (q : TypeQ) (t : go.GoType) (i : Int) :
    GoLocalContext.typeFns.typeQuery q t i = typeQuery q t i := rfl

theorem convertExposed_eq (t : go.GoType) :
    GoLocalContext.typeFns.convertExposed t = convertExposed t := rfl

theorem isInterface_eq (t : go.GoType) :
    GoLocalContext.typeFns.isInterface t = isInterfaceType (underlying t) := rfl

theorem typeSetContains_eq (t u : go.GoType) :
    GoLocalContext.typeFns.typeSetContains t u = typeSetContains t u := rfl

end defs
end go

/-! ## Injectivity of the encodings -/

section enc
variable [GooseExts] [GoGlobalContext]

/-- The shape of a value (the inverse of `go.Shape.toVal`). -/
def go.Shape.ofVal : val → Option go.Shape
  | PairV (LitV LitUnit) v => (go.Shape.ofVal v).map .deref
  | LitV (LitInt n) =>
    if n = 0 then some .self else if n = 1 then some .slice else if n = 2 then some .map
    else if n = 3 then some .ptr else if n = 4 then some (.chan .recvonly)
    else if n = 5 then some (.chan .sendonly) else if n = 6 then some (.chan .sendrecv) else none
  | _ => none

theorem go.Shape.ofVal_toVal (s : go.Shape) : go.Shape.ofVal s.toVal = some s := by
  induction s with
  | deref s ih => simp only [go.Shape.toVal, go.Shape.ofVal, ih, Option.map_some]
  | chan c => cases c <;> simp only [go.Shape.toVal, go.Shape.ofVal] <;> decide
  | _ => simp only [go.Shape.toVal, go.Shape.ofVal] <;> decide

theorem go.Shape.toVal_inj {s s' : go.Shape} (h : s.toVal = s'.toVal) : s = s' := by
  have := congrArg go.Shape.ofVal h
  rw [go.Shape.ofVal_toVal, go.Shape.ofVal_toVal] at this
  exact Option.some.inj this

theorem go.shapesVal_inj {shs shs' : List go.Shape}
    (h : go.shapesVal shs = go.shapesVal shs') : shs = shs' := by
  induction shs generalizing shs' with
  | nil => cases shs' <;> first | rfl | (simp only [go.shapesVal] at h; cases h)
  | cons s shs ih =>
    cases shs' with
    | nil => simp only [go.shapesVal] at h; cases h
    | cons s' shs' =>
      simp only [go.shapesVal, val.PairV.injEq] at h
      rw [go.Shape.toVal_inj h.1, ih h.2]

theorem go.funcAtArg_inj [go.IntoValInj GoString] {f f' : GoString}
    {shs shs' : List go.Shape} (h : go.funcAtArg f shs = go.funcAtArg f' shs') :
    f = f' ∧ shs = shs' := by
  simp only [go.funcAtArg, val.PairV.injEq] at h
  exact ⟨go.intoVal_inj h.1, go.shapesVal_inj h.2⟩

theorem go.dispatchArgs_inj [go.IntoValInj GoInterface] {is is' : List GoInterfaceOk}
    (hl : is.length = is'.length) (h : go.dispatchArgs is = go.dispatchArgs is') : is = is' := by
  induction is generalizing is' with
  | nil => cases is' <;> simp_all
  | cons i is ih =>
    cases is' with
    | nil => simp at hl
    | cons i' is' =>
      cases is with
      | nil =>
        cases is' with
        | nil =>
          simp only [go.dispatchArgs] at h
          have := go.intoVal_inj h
          injection this with h; rw [h]
        | cons => simp at hl
      | cons j js =>
        cases is' with
        | nil => simp at hl
        | cons j' js' =>
          simp only [go.dispatchArgs] at h
          injection h with h1 h2
          have := go.intoVal_inj h1
          injection this with h1
          rw [h1, ih (by simpa using hl) h2]

theorem GoTypeFns.shapesArgs_length (tf : GoTypeFns) {shs : List go.Shape} {ds ts : List go.GoType}
    (h : tf.shapesArgs shs ds = some ts) : shs.length = ds.length := by
  induction shs generalizing ds ts with
  | nil => cases ds <;> simp_all [GoTypeFns.shapesArgs]
  | cons s shs ih =>
    cases ds with
    | nil => simp [GoTypeFns.shapesArgs] at h
    | cons d ds =>
      simp only [GoTypeFns.shapesArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, h', _⟩ := h
      simp [ih h']

end enc

/-! ## The operations' cases of `ReflectOpStep` -/

theorem go.TypeQ.ofOp_FuncResolveAt : go.TypeQ.ofOp "FuncResolveAt" = none := rfl
theorem go.TypeQ.ofOp_ConvertAt : go.TypeQ.ofOp "ConvertAt" = none := rfl
theorem go.TypeQ.ofOp_FieldRefAt : go.TypeQ.ofOp "FieldRefAt" = none := rfl
theorem go.TypeQ.ofOp_ArraySliceAt : go.TypeQ.ofOp "ArraySliceAt" = none := rfl
theorem go.TypeQ.ofOp_EqNilAt : go.TypeQ.ofOp "EqNilAt" = none := rfl

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt reflectExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- An operation of the reflection extension whose result `e` from the argument `v` is
determined: it steps to `e`, the heap unchanged. -/
theorem wp_reflectStep (o : String) (v : val) (e : Expr) (hv : v.isPanic = false)
    (hstep : ReflectOpStep GoLocalContext.typeFns o v e)
    (hdet : ∀ e', ReflectOpStep GoLocalContext.typeFns o v e' → e' = e) (Φ : val → IProp GF) :
    ▷ WP e @ s; E {{ Φ }} ⊢ WP (ExternalOp reflectExtName o (Val v)) @ s; E {{ Φ }} := by
  show _ ⊢ WP (ExternalOp reflectExt.name o (Val v)) @ s; E {{ Φ }}
  iintro Hwp
  iapply wp_extStep (X := reflectExt) o v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨e, h, (), (), rfl, hstep⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, Hst⟩ := Hst
  obtain rfl := hdet e' Hst
  imod Hclose
  imodintro
  iframe Hheap Hl Hg Hwp

/-- `FuncResolveAt`: `FuncResolve f ts` for the type arguments `ts` that the shapes `shs` give
for the dispatch interfaces `is`. -/
theorem wp_reflect_FuncResolveAt (f : GoString) (shs : List go.Shape) (is : List GoInterfaceOk)
    (ts : List go.GoType) (h : go.shapesArgs shs (is.map (·.ty)) = some ts)
    (Φ : val → IProp GF) :
    ▷ WP (App (Val (GoInstruction (FuncResolve f ts))) (Val #())) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName "FuncResolveAt"
        (Val (PairV (go.funcAtArg f shs) (go.dispatchArgs is)))) @ s; E {{ Φ }} := by
  have h' : GoLocalContext.typeFns.shapesArgs shs (is.map (·.ty)) = some ts := by
    rw [go.shapesArgs_eq]; exact h
  apply wp_reflectStep _ _ _ rfl (by simp only [ReflectOpStep, go.TypeQ.ofOp_FuncResolveAt]; exact ⟨f, shs, is, ts, rfl, h', rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, go.TypeQ.ofOp_FuncResolveAt] at Hst
  obtain ⟨f', shs', is', ts', hv, hts, rfl⟩ := Hst
  injection hv with hv1 hv2
  obtain ⟨rfl, rfl⟩ := go.funcAtArg_inj hv1
  have hl := GoTypeFns.shapesArgs_length _ h'
  have hl' := GoTypeFns.shapesArgs_length _ hts
  simp only [List.length_map] at hl hl'
  obtain rfl := go.dispatchArgs_inj (by omega) hv2
  rw [h'] at hts
  cases hts
  rfl

theorem go.mkOk_val_inj [go.IntoValInj GoInterface] {t t' : go.GoType} {w w' : val}
    (h : (#(interface.mkOk t w) : val) = #(interface.mkOk t' w')) : t = t' ∧ w = w' := by
  have := go.intoVal_inj h
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at this
  exact this

/-- `ConvertAt`: for a non-interface `u`, `Convert t u` and the boxing in `any`; for an interface
`u` that `t` implements, `x` itself. -/
theorem wp_reflect_ConvertAt (t u : go.GoType) (w : val) (l : Loc)
    (hi : go.isInterfaceType (underlying u) = true → go.typeSetContains t u = true)
    (ht : go.convertExposed t = false) (hu : go.convertExposed u = false) (Φ : val → IProp GF) :
    ▷ WP (if go.isInterfaceType (underlying u) then gl(#(interface.mkOk t w))
        else gl(Convert u go.any (Convert t u (Val w)))) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName "ConvertAt"
        (Val (PairV #(interface.mkOk t w) #(interface.mkOk (go.PointerType u) #l)))) @ s; E
        {{ Φ }} := by
  have hi' : GoLocalContext.typeFns.isInterface u = true →
      GoLocalContext.typeFns.typeSetContains t u = true := by
    rw [go.isInterface_eq, go.typeSetContains_eq]; exact hi
  have he : (if GoLocalContext.typeFns.isInterface u then gl(#(interface.mkOk t w))
      else gl(Convert u go.any (Convert t u (Val w)))) =
      (if go.isInterfaceType (underlying u) then gl(#(interface.mkOk t w))
        else gl(Convert u go.any (Convert t u (Val w)))) := by
    rw [go.isInterface_eq]
  rw [← he]
  apply wp_reflectStep _ _ _ rfl (by simp only [ReflectOpStep, go.TypeQ.ofOp_ConvertAt]; exact ⟨t, u, w, l, rfl, hi', ht, hu, rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, go.TypeQ.ofOp_ConvertAt] at Hst
  obtain ⟨t', u', w', l', hv, -, -, -, rfl⟩ := Hst
  injection hv with hv1 hv2
  obtain ⟨rfl, rfl⟩ := go.mkOk_val_inj hv1
  obtain ⟨hu', -⟩ := go.mkOk_val_inj hv2
  cases hu'
  rfl

/-- `FieldRefAt`: `&(*p).f` boxed in `any`, for the `i`th field `f` of the struct type `st`. -/
theorem wp_reflect_FieldRefAt (st : go.GoType) (fs : List go.field_decl) (l : Loc) (i : w64)
    (fd : go.field_decl) (hst : underlying st = go.StructType fs)
    (hm : go.layoutModelled st = false) (hl : l ≠ null) (hi : 0 ≤ sint.Z i)
    (hfd : fs[sint.nat i]? = some fd) (hblank : go.isBlankField (go.fieldDeclName fd) = false)
    (Φ : val → IProp GF) :
    ▷ WP gl(Convert (go.PointerType (go.fieldDeclType fd)) go.any
        (StructFieldRef st (go.fieldDeclName fd) (Val #l))) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName "FieldRefAt"
        (Val (PairV #(interface.mkOk (go.PointerType st) #l) #i))) @ s; E {{ Φ }} := by
  apply wp_reflectStep _ _ _ rfl (by simp only [ReflectOpStep, go.TypeQ.ofOp_FieldRefAt]; exact ⟨st, fs, l, i, fd, rfl, hst, hm, hl, hi, hfd, hblank, rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, go.TypeQ.ofOp_FieldRefAt] at Hst
  obtain ⟨st', fs', l', i', fd', hv, hst', -, -, -, hfd', -, rfl⟩ := Hst
  injection hv with hv1 hv2
  obtain ⟨hs, hl'⟩ := go.mkOk_val_inj hv1
  cases hs
  obtain rfl := go.intoVal_inj hl'
  obtain rfl := go.intoVal_inj hv2
  have : go.StructType fs = go.StructType fs' := hst.symm.trans hst'
  cases this
  rw [hfd] at hfd'
  cases hfd'
  rfl

/-- `ArraySliceAt`: `(*p)[:]` boxed in `any`, for `p` a pointer to the array type `a`. -/
theorem wp_reflect_ArraySliceAt (a e : go.GoType) (n : Int) (l : Loc)
    (ha : underlying a = go.ArrayType n e) (hm : go.layoutModelled a = false) (hl : l ≠ null)
    (Φ : val → IProp GF) :
    ▷ WP gl(Convert (go.SliceType e) go.any
        (Slice (go.ArrayType n e) (#l, #(W64 0), #(W64 n)))) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName "ArraySliceAt"
        (Val #(interface.mkOk (go.PointerType a) #l))) @ s; E {{ Φ }} := by
  apply wp_reflectStep _ _ _ (GoGlobalContext.intoVal_not_panic _)
    (by simp only [ReflectOpStep, go.TypeQ.ofOp_ArraySliceAt]; exact ⟨a, e, n, l, rfl, ha, hm, hl, rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, go.TypeQ.ofOp_ArraySliceAt] at Hst
  obtain ⟨a', e'', n', l', hv, ha', -, -, rfl⟩ := Hst
  obtain ⟨hs, hl'⟩ := go.mkOk_val_inj hv
  cases hs
  obtain rfl := go.intoVal_inj hl'
  have : go.ArrayType n e = go.ArrayType n' e'' := ha.symm.trans ha'
  cases this
  rfl

/-- `EqNilAt`: `x == nil` at `x`'s dynamic type `t`, whose underlying type is nilable. -/
theorem wp_reflect_EqNilAt (t : go.GoType) (w : val) (hn : go.IsNilable (underlying t))
    (hm : go.layoutModelled t = false) (Φ : val → IProp GF) :
    ▷ WP gl(GoOp GoEquals t (Val w, GoZeroVal t #())) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName "EqNilAt" (Val #(interface.mkOk t w))) @ s; E {{ Φ }} := by
  apply wp_reflectStep _ _ _ (GoGlobalContext.intoVal_not_panic _) (by simp only [ReflectOpStep, go.TypeQ.ofOp_EqNilAt]; exact ⟨t, w, rfl, hn, hm, rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, go.TypeQ.ofOp_EqNilAt] at Hst
  obtain ⟨t', w', hv, -, -, rfl⟩ := Hst
  obtain ⟨rfl, rfl⟩ := go.mkOk_val_inj hv
  rfl

/-- `TypeQuery.<q>`: the fact `q` about the type `t` of a token. -/
theorem wp_reflect_TypeQuery (o : String) (q : go.TypeQ) (hq : go.TypeQ.ofOp o = some q)
    (t : go.GoType) (l : Loc) (i : w64) (w : val) (h : go.typeQuery q t (sint.Z i) = some w)
    (Φ : val → IProp GF) :
    ▷ WP (Val w) @ s; E {{ Φ }} ⊢
      WP (ExternalOp reflectExtName o
        (Val (PairV #(interface.mkOk (go.PointerType t) #l) #i))) @ s; E {{ Φ }} := by
  have h' : GoLocalContext.typeFns.typeQuery q t (sint.Z i) = some w := by
    rw [go.typeQuery_eq]; exact h
  apply wp_reflectStep _ _ _ rfl (by simp only [ReflectOpStep, hq]; exact ⟨t, l, i, w, rfl, h', rfl⟩)
  intro e' Hst
  simp only [ReflectOpStep, hq] at Hst
  obtain ⟨t', l', i', w', hv, h'', rfl⟩ := Hst
  injection hv with hv1 hv2
  obtain ⟨hs, -⟩ := go.mkOk_val_inj hv1
  cases hs
  obtain rfl := go.intoVal_inj hv2
  rw [h'] at h''
  cases h''
  rfl

end lifting

end Perennial
