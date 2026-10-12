/-
Sketch: the program logic of interfaces over the byte memory
(`Golang/Defn/StaticImage.lean`).

Program proofs use an interface value as an opaque `i : GoIface` (or
`GoEface`) with the persistent fact `isIface i I T x` ("an interface of type
`I` holding `x : T`"), and the instruction-level specs at the end of this
file; that an interface value is an itab and a boxed value is internal to
this file. The steps of the interface instructions are local instances here,
so automation stops at those instructions elsewhere.

`isItab` is defined by an itab's contents, not its address, so an itab built
by `runtime.getitab` would satisfy it like a static one: the specs that use an
interface value do not depend on where its itab came from. The premises of
the conversions are goose-generated facts (`HasTypeDesc`, `StaticItab`,
`Implements`, `IfaceMethods`); proofs only meet them through instance search.
-/
module

public import Perennial.Golang.Defn.StaticImage
public import Perennial.Golang.Theory.Pre
public import Perennial.GooseLang.ByteLifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

set_option linter.unusedSectionVars false

theorem flatMap_encode_length (l : List w64) :
    (l.flatMap (ByteRepr.encode (V := w64))).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, ByteRepr.length_encode, List.length_cons]
    show 8 + 8 * l.length = 8 * (l.length + 1)
    omega

theorem w64_combine_encode (w : w64) :
    BitVec.ofNat 64 (LittleEndian.combine (ByteRepr.encode w)) = w := by
  show BitVec.ofNat 64 (LittleEndian.combine (LittleEndian.split 8 w.toNat)) = w
  rw [LittleEndian.combine_split, Nat.mod_eq_of_lt (by have := w.isLt; simpa using this)]
  exact BitVec.ofNat_toNat 64 w |>.trans (BitVec.setWidth_eq w)

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics] [go.StaticSymbols] [go.BytesSemantics]
variable [go.InterfaceSemanticsB]
variable {s : Stuckness} {E : CoPset}

open ProofMode go

attribute [local instance] InterfaceSemanticsB.go_eq_interface
  InterfaceSemanticsB.convert_to_interface InterfaceSemanticsB.type_assert_step
  InterfaceSemanticsB.method_interface

/-! ## Byte lemmas about itabs -/

/-- The `Type` field of an itab. -/
theorem itab_type_bytes (tab inter typ : w64) (h : w32) (fns : List w64) :
    bytesPointsto (GF := GF) tab .discard (itabBytes inter typ h fns) ⊢
      bytesPointsto (byteAddr tab 8) .discard (ByteRepr.encode typ) := by
  unfold itabBytes
  iintro H
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨-, H⟩
  rw [ByteRepr.length_encode]
  iexact H

/-- `Fun[k]` of an itab. -/
theorem itab_fun_bytes (tab inter typ : w64) (h : w32) (fns : List w64) (k : Nat)
    (hk : k < fns.length) :
    bytesPointsto (GF := GF) tab .discard (itabBytes inter typ h fns) ⊢
      bytesPointsto (byteAddr tab (24 + 8 * k)) .discard (ByteRepr.encode fns[k]) := by
  unfold itabBytes
  iintro H
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨-, H⟩
  have hlen : (ByteRepr.encode inter ++ ByteRepr.encode typ ++ ByteRepr.encode h ++
      [(0 : w8), 0, 0, 0]).length = 24 := by
    simp only [List.length_append, ByteRepr.length_encode]; rfl
  rw [hlen]
  have hfm : fns.flatMap (ByteRepr.encode (V := w64)) =
      (fns.take k).flatMap ByteRepr.encode ++
        (ByteRepr.encode fns[k] ++ (fns.drop (k + 1)).flatMap ByteRepr.encode) := by
    have h1 : fns.drop k = fns[k] :: fns.drop (k + 1) := List.drop_eq_getElem_cons hk
    calc fns.flatMap (ByteRepr.encode (V := w64))
        = (fns.take k ++ fns.drop k).flatMap ByteRepr.encode := by rw [List.take_append_drop]
      _ = _ := by rw [List.flatMap_append, h1, List.flatMap_cons]
  rw [hfm]
  icases (bytesPointsto_app _ _ _ _).1 $$ H with ⟨-, H⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ H with ⟨H, -⟩
  rw [flatMap_encode_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have : byteAddr (byteAddr tab 24) (8 * k) = byteAddr tab (24 + 8 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [this]
  iexact H

/-! ## Typed points-to for interface values (one heap cell, as for `GoInterface`) -/

instance typedPointsto_eface : TypedPointsto (GF := GF) GoEface :=
  heapTypedPointsto GoEface go.intoVal_inj

instance typedPointsto_iface : TypedPointsto (GF := GF) GoIface :=
  heapTypedPointsto GoIface go.intoVal_inj

attribute [local instance] go.tagged_internal_inst in
instance intoVal_typed_eface (elems : List go.InterfaceElem)
    [IfaceMethods (go.InterfaceType elems) []] :
    IntoValTypedUnderlying (GF := GF) GoEface (go.InterfaceType elems) := by
  solve_into_val_typed

attribute [local instance] go.tagged_internal_inst in
instance intoVal_typed_iface (elems : List go.InterfaceElem) {m : GoString} {ms : List GoString}
    [IfaceMethods (go.InterfaceType elems) (m :: ms)] :
    IntoValTypedUnderlying (GF := GF) GoIface (go.InterfaceType elems) := by
  solve_into_val_typed

/-! ## Resources -/

/-- `tab` is an itab of `T` for the interface `I`: it points at `T`'s descriptor
and at the code of `T`'s methods, in `I`'s itab order. -/
def isItab (tab : w64) (T I : go.GoType) : IProp GF :=
  iprop(∃ (inter : w64) (h : w32),
    bytesPointsto tab .discard
      (itabBytes inter (typeAddr T) h ((itabMethods I).map (methodAddr T))) ∗
    ⌜tab ≠ 0 ∧ ∀ m ∈ itabMethods I, StaticMethod T m⌝)

/-- A non-empty interface value of interface type `I`, with dynamic type `T` and
value `x`. -/
def isIface {V : Type} [ByteRepr V] (i : GoIface) (I T : go.GoType) (x : V) : IProp GF :=
  iprop(isItab i.tab T I ∗ bytesPointsto i.data .discard (ByteRepr.encode x))

/-- An empty interface value with dynamic type `T` and value `x`. -/
def isEface {V : Type} [ByteRepr V] (i : GoEface) (T : go.GoType) (x : V) : IProp GF :=
  iprop(⌜i.tptr = typeAddr T⌝ ∗ bytesPointsto i.data .discard (ByteRepr.encode x))

instance isItab_persistent (tab : w64) (T I : go.GoType) :
    Persistent (isItab (GF := GF) tab T I) := by
  unfold isItab; infer_instance

instance isIface_persistent {V : Type} [ByteRepr V] (i : GoIface) I T (x : V) :
    Persistent (isIface (GF := GF) i I T x) := by
  unfold isIface; infer_instance

instance isEface_persistent {V : Type} [ByteRepr V] (i : GoEface) T (x : V) :
    Persistent (isEface (GF := GF) i T x) := by
  unfold isEface; infer_instance

/-- `T` implements the interface `I`: the code of `T`'s methods is in the image
(generated by goose; all that `runtime.getitab` needs to build an itab). -/
class Implements (T I : go.GoType) : Prop where
  methods : ∀ m ∈ itabMethods I, StaticMethod T m

/-- A static itab gives `isItab`. -/
theorem static_isItab {e : Expr} {Φ : val → IProp GF} (T I : go.GoType) [StaticItab T I]
    [Implements T I] (he : toVal e = none) :
    (isItab (GF := GF) (itabAddr T I) T I -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  obtain ⟨hash, hbytes⟩ := StaticItab.itab (T := T) (I := I)
  iintro H
  iapply wp_static_bytes _ _ hbytes he
  iintro #Hb
  iapply H
  unfold isItab
  iexists typeAddr I, hash
  iframe Hb
  ipureintro
  exact ⟨StaticItab.ne_zero, Implements.methods⟩

/-! ## Specs of the lowered operations -/

omit [FfiSemantics ext ffi] in
include hG in
theorem iface_val (tab d : w64) : PairV #true (PairV #tab #d) = #(⟨tab, d⟩ : GoIface) := by
  rw [intoVal_unfold GoIface]

omit [FfiSemantics ext ffi] in
include hG in
theorem eface_val (t d : w64) : PairV #false (PairV #t #d) = #(⟨t, d⟩ : GoEface) := by
  rw [intoVal_unfold GoEface]

theorem wp_boxBytes {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V] (x : V) :
    {{ (True : IProp GF) }} (App (Val (boxBytes T)) (Val #x)) @ s; E
    {{ (d : w64), RET #d; bytesPointsto d .discard (ByteRepr.encode x) }} := by
  iintro %Φ _ HΦ
  unfold boxBytes
  wp_pures
  wp_apply wp_balloc_frozen (ByteRepr.encode x) as %d #Hd
  iapply HΦ $$ Hd

theorem wp_unbox {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V] (d : w64)
    (dq : DFrac) (x : V) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ bytesPointsto (GF := GF) d dq (ByteRepr.encode x) }}
      (App (Val (unboxV T)) (Val #d)) @ s; E
    {{ RET #x; bytesPointsto d dq (ByteRepr.encode x) }} := by
  iintro %Φ Hd HΦ
  unfold unboxV
  wp_pures
  wp_apply wp_bload d (W64 (ByteRepr.size V)) dq (ByteRepr.encode x)
    (by rw [ByteRepr.length_encode]; simp; omega) $$ [$Hd] as Hd
  wp_pures
  rw [ByteRepr.decode_encode]
  wp_pures
  iapply HΦ $$ Hd

/-! ## The interface specs (what program proofs use) -/

/-- `I(x)` for a concrete `x : T` and a non-empty interface `I`. -/
theorem wp_convert_iface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] {elems : List go.InterfaceElem} [I ≤u go.InterfaceType elems]
    {m : GoString} {ms : List GoString} [IfaceMethods I (m :: ms)] [StaticItab T I]
    [Implements T I] (hT : isInterfaceType Tunder = false) (hN : isUntypedNil Tunder = false)
    (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoIface), RET #i; isIface i I T x }} := by
  iintro %Φ _ HΦ
  iapply static_isItab T I rfl
  iintro #Htab
  wp_pures
  have hm : (itabMethods I).isEmpty = false := by rw [IfaceMethods.itab_methods]; rfl
  simp only [hT, hN, hm, Bool.false_eq_true, ↓reduceIte]
  wp_apply wp_boxBytes T x as %d #Hd
  wp_pures
  rw [iface_val (GF := GF)]
  iapply HΦ
  unfold isIface
  isplitl
  · iexact Htab
  · iexact Hd

/-- `I(x)` for a concrete `x : T` and an empty interface `I`. -/
theorem wp_convert_eface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] {elems : List go.InterfaceElem} [I ≤u go.InterfaceType elems]
    [IfaceMethods I []] (hT : isInterfaceType Tunder = false)
    (hN : isUntypedNil Tunder = false) (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoEface), RET #i; isEface i T x }} := by
  iintro %Φ _ HΦ
  wp_pures
  have hm : (itabMethods I).isEmpty = true := by rw [IfaceMethods.itab_methods]; rfl
  simp only [hT, hN, hm, Bool.false_eq_true, ↓reduceIte]
  wp_apply wp_boxBytes T x as %d #Hd
  wp_pures
  rw [eface_val (GF := GF)]
  iapply HΦ
  unfold isEface
  isplitr
  · ipureintro; rfl
  · iexact Hd

/-- `i.m` on an interface holding `x : T` resolves to `T`'s method `m` on `x`. -/
theorem wp_iface_method_resolve {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] [NotInterface Tunder] {elems : List go.InterfaceElem}
    [I ≤u go.InterfaceType elems] (m : GoString) (i : GoIface) (x : V)
    (hm : m ∈ itabMethods I) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isIface (GF := GF) i I T x }}
      (App (Val (GoInstruction (MethodResolve I m))) (Val #i)) @ s; E
    {{ RET #(methods T m #x); True }} := by
  unfold isIface isItab
  iintro %Φ ⟨⟨%inter, %h, #Hb, %hp⟩, #Hd⟩ HΦ
  obtain ⟨hne, hmeth⟩ := hp
  wp_pures
  simp only [hne, ↓reduceIte]
  have hk : (itabMethods I).idxOf m < ((itabMethods I).map (methodAddr T)).length := by
    rw [List.length_map]; exact List.idxOf_lt_length_of_mem hm
  ihave #Hf := itab_fun_bytes i.tab inter (typeAddr T) h _ _ hk $$ Hb
  have hget : ((itabMethods I).map (methodAddr T))[(itabMethods I).idxOf m] = methodAddr T m := by
    rw [List.getElem_map, List.getElem_idxOf]
  rw [hget]
  unfold itabFun
  wp_pures
  wp_apply wp_bload (byteAddr i.tab (24 + 8 * (itabMethods I).idxOf m)) (W64 8) .discard
    (ByteRepr.encode (methodAddr T m)) (by rw [ByteRepr.length_encode]; rfl) $$ [$Hf] as -
  wp_pures
  rw [w64_combine_encode]
  iapply wp_static_func _ _ (hmeth m hm) rfl
  iintro #Hfn
  wp_apply wp_func_load (methodAddr T m) (ifnWrapper T m) $$ [$Hfn]
  unfold ifnWrapper
  wp_pures
  wp_apply wp_unbox T i.data .discard x hsz $$ [$Hd] as -
  wp_pures
  iapply HΦ; itrivial

/-- `i.(T)` for a non-empty interface holding `x : T`. -/
theorem wp_type_assert_iface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] (hT : isInterfaceType Tunder = false)
    (i : GoIface) (I : go.GoType) (x : V) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isIface (GF := GF) i I T x }} (App (Val (GoInstruction (TypeAssert T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  unfold isIface isItab
  iintro %Φ ⟨⟨%inter, %h, #Hb, %hp⟩, #Hd⟩ HΦ
  obtain ⟨hne, -⟩ := hp
  ihave #Ht := itab_type_bytes i.tab inter (typeAddr T) h _ $$ Hb
  obtain ⟨tab, d⟩ := i
  rw [← iface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssertConcrete dynType
  wp_pures
  simp only at hne
  have hne' : tab ≠ W64 0 := hne
  rw [decide_eq_false hne']
  wp_pures
  unfold itabType
  wp_pures
  rw [show tab + W64 8 = byteAddr tab 8 from rfl]
  wp_apply wp_bload (byteAddr tab 8) (W64 8) .discard (ByteRepr.encode (typeAddr T))
    (by rw [ByteRepr.length_encode]; rfl) $$ [$Ht] as -
  wp_pures
  rw [w64_combine_encode]
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  iapply HΦ; itrivial

/-- `i.(T)` for an empty interface holding `x : T`. -/
theorem wp_type_assert_eface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] (hT : isInterfaceType Tunder = false)
    (i : GoEface) (x : V) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isEface (GF := GF) i T x }} (App (Val (GoInstruction (TypeAssert T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  unfold isEface
  iintro %Φ ⟨%ht, #Hd⟩ HΦ
  obtain ⟨tp, d⟩ := i
  simp only at ht
  subst ht
  rw [← eface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssertConcrete dynType
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  iapply HΦ; itrivial

/-- `==` on two nil empty interfaces. -/
theorem wp_eq_eface_nil :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType []))))
        (Val (PairV #(zero_val GoEface) #(zero_val GoEface)))) @ s; E
    {{ RET #true; True }} := by
  iintro %Φ _ HΦ
  rw [show (zero_val GoEface) = ⟨0, 0⟩ from rfl, ← eface_val (GF := GF)]
  wp_pures
  unfold ifaceEqV
  wp_pures
  iapply HΦ; itrivial

end proofs

end Perennial
