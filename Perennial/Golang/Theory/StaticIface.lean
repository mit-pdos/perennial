/-
Sketch: the program logic of interfaces over the byte memory
(`Golang/Defn/StaticImage.lean`).

Program proofs use an interface value as an opaque `i : GoIface` (or
`GoEface`) with the persistent fact `isIface i I T x` ("an interface of type
`I` holding `x : T`"), and the instruction-level specs at the end of this
file; that an interface value is an itab and a boxed value is internal to
this file. The steps of the interface instructions are local instances here,
so automation stops at those instructions elsewhere.

`isIface i I T x` says that `i`'s itab is `go:itab.T,I` (`itabAddr T I`), with
the contents an itab of `T` for `I` has (`isItab`). The address matters: the
compiler's `x.(T)` compares the itab pointer, relying on the runtime keeping
one itab per (interface, type) pair (`runtime.itabsinit` registers the static
itabs before `getitab` can build one). An itab built by `getitab` will
therefore satisfy `isIface` through the runtime's invariant that the itab it
returns for a pair with a static itab is that one. The premises of the specs are
goose-generated facts (`StaticItab`, `Implements`, `HasTypeDesc`, `TypeEqual`,
`IfaceMethods`, `TypeBytes`), found by instance search; the itab method order
appears only through `m ∈ itabMethods I` in `wp_iface_method_resolve`.
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

attribute [local instance] InterfaceSemanticsB.convert_to_interface InterfaceSemanticsB.type_assert_step
  InterfaceSemanticsB.type_assert2_step InterfaceSemanticsB.method_interface

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

/-- The `Inter` field of an itab. -/
theorem itab_inter_bytes (tab inter typ : w64) (h : w32) (fns : List w64) :
    bytesPointsto (GF := GF) tab .discard (itabBytes inter typ h fns) ⊢
      bytesPointsto tab .discard (ByteRepr.encode inter) := by
  unfold itabBytes
  iintro H
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
  icases (bytesPointsto_app tab _ _ _).1 $$ H with ⟨H, -⟩
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

/-- `tab` is an itab of `T` for the interface `I`: it points at `I`'s and `T`'s
descriptors and at the code of `T`'s methods, in `I`'s itab order. -/
def isItab (tab : w64) (T I : go.GoType) : IProp GF :=
  iprop(∃ (h : w32),
    bytesPointsto tab .discard
      (itabBytes (typeAddr I) (typeAddr T) h ((itabMethods I).map (methodAddr T))) ∗
    ⌜tab ≠ 0 ∧ ∀ m ∈ itabMethods I, StaticMethod T m⌝)

/-- A non-empty interface value of interface type `I`, with dynamic type `T` and
value `x`: its itab is `go:itab.T,I`. -/
def isIface {V : Type} [ByteRepr V] (i : GoIface) (I T : go.GoType) (x : V) : IProp GF :=
  iprop(⌜i.tab = itabAddr T I⌝ ∗ isItab i.tab T I ∗ bytesPointsto i.data .discard (ByteRepr.encode x))

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
  iexists hash
  iframe Hb
  ipureintro
  exact ⟨StaticItab.ne_zero, Implements.methods⟩

/-! ## Specs of the lowered operations -/

omit [FfiSemantics ext ffi] in
include hG in
theorem iface_val (tab d : w64) : PairV #tab #d = #(⟨tab, d⟩ : GoIface) := by
  rw [intoVal_unfold GoIface]

omit [FfiSemantics ext ffi] in
include hG in
theorem eface_val (t d : w64) : PairV #t #d = #(⟨t, d⟩ : GoEface) := by
  rw [intoVal_unfold GoEface]

theorem wp_boxBytes {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] (T : go.GoType) [TypeRepr T V] [TypeBytes T V] (x : V) :
    {{ (True : IProp GF) }} (App (Val (boxBytes T)) (Val #x)) @ s; E
    {{ (d : w64), RET #d; bytesPointsto d .discard (ByteRepr.encode x) }} := by
  iintro %Φ _ HΦ
  unfold boxBytes
  wp_pures
  wp_apply wp_balloc_frozen (ByteRepr.encode x) as %d #Hd
  iapply HΦ $$ Hd

theorem wp_unbox {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] (T : go.GoType) [TypeRepr T V] [TypeBytes T V] (d : w64)
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
  iapply HΦ $$ Hd

/-! ## Loads from descriptors and itabs -/

theorem wp_loadWord (p : w64) (off : Nat) (dq : DFrac) (w : w64) :
    {{ bytesPointsto (GF := GF) (byteAddr p off) dq (ByteRepr.encode w) }}
      (App (Val (loadWord off)) (Val #p)) @ s; E
    {{ RET #w; bytesPointsto (byteAddr p off) dq (ByteRepr.encode w) }} := by
  iintro %Φ Hb HΦ
  unfold loadWord
  wp_pures
  wp_apply wp_bload (byteAddr p off) (W64 8) dq (ByteRepr.encode w)
    (by rw [ByteRepr.length_encode]; rfl) $$ [$Hb] as Hb
  wp_pures
  iapply HΦ $$ Hb

theorem wp_loadByte (p : w64) (off : Nat) (dq : DFrac) (b : w8) :
    {{ bytesPointsto (GF := GF) (byteAddr p off) dq (ByteRepr.encode b) }}
      (App (Val (loadByte off)) (Val #p)) @ s; E
    {{ RET #b; bytesPointsto (byteAddr p off) dq (ByteRepr.encode b) }} := by
  iintro %Φ Hb HΦ
  unfold loadByte
  wp_pures
  wp_apply wp_bload (byteAddr p off) (W64 1) dq (ByteRepr.encode b)
    (by rw [ByteRepr.length_encode]; rfl) $$ [$Hb] as Hb
  wp_pures
  iapply HΦ $$ Hb

/-! ## The interface specs (what program proofs use) -/

/-- `I(x)` for a concrete `x : T` and a non-empty interface `I`. -/
theorem wp_convert_iface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem} [I ≤u go.InterfaceType elems]
    {m : GoString} {ms : List GoString} [IfaceMethods I (m :: ms)] [StaticItab T I]
    [Implements T I] (hT : isInterfaceType Tunder = false) (hN : isUntypedNil Tunder = false)
    (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoIface), RET #i; isIface i I T x }} := by
  haveI : NoGetitab Tunder I := ⟨fun h => by rw [hT] at h; cases h⟩
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
  isplitr
  · ipureintro; rfl
  isplitl
  · iexact Htab
  · iexact Hd

/-- `I(x)` for a concrete `x : T` and an empty interface `I`. -/
theorem wp_convert_eface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem} [I ≤u go.InterfaceType elems]
    [IfaceMethods I []] (hT : isInterfaceType Tunder = false)
    (hN : isUntypedNil Tunder = false) (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoEface), RET #i; isEface i T x }} := by
  haveI : NoGetitab Tunder I := ⟨fun h => by rw [hT] at h; cases h⟩
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
theorem wp_iface_method_resolve {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] [NotInterface Tunder] {elems : List go.InterfaceElem}
    [I ≤u go.InterfaceType elems] (m : GoString) (i : GoIface) (x : V)
    (hm : m ∈ itabMethods I) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isIface (GF := GF) i I T x }}
      (App (Val (GoInstruction (MethodResolve I m))) (Val #i)) @ s; E
    {{ RET #(methods T m #x); True }} := by
  unfold isIface isItab
  iintro %Φ ⟨-, ⟨%h, #Hb, %hp⟩, #Hd⟩ HΦ
  obtain ⟨hne, hmeth⟩ := hp
  wp_pures
  simp only [hne, ↓reduceIte]
  have hk : (itabMethods I).idxOf m < ((itabMethods I).map (methodAddr T)).length := by
    rw [List.length_map]; exact List.idxOf_lt_length_of_mem hm
  ihave #Hf := itab_fun_bytes i.tab (typeAddr I) (typeAddr T) h _ _ hk $$ Hb
  have hget : ((itabMethods I).map (methodAddr T))[(itabMethods I).idxOf m] = methodAddr T m := by
    rw [List.getElem_map, List.getElem_idxOf]
  rw [hget]
  wp_apply wp_loadWord i.tab (24 + 8 * (itabMethods I).idxOf m) .discard (methodAddr T m)
    $$ [$Hf] as -
  iapply wp_static_func _ _ (hmeth m hm) rfl
  iintro #Hfn
  wp_apply wp_func_load (methodAddr T m) (ifnWrapper T m) $$ [$Hfn]
  unfold ifnWrapper
  wp_pures
  wp_apply wp_unbox T i.data .discard x hsz $$ [$Hd] as -
  wp_pures
  iapply HΦ; itrivial

/-- `i.(T)` for a non-empty interface of type `I` holding `x : T`. -/
theorem wp_type_assert_iface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem}
    [I ≤u go.InterfaceType elems] {m : GoString} {ms : List GoString} [IfaceMethods I (m :: ms)]
    (hT : isInterfaceType Tunder = false) (i : GoIface) (x : V)
    (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isIface (GF := GF) i I T x }} (App (Val (GoInstruction (TypeAssert I T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  haveI : NoGetitab Tunder T := ⟨fun h => by rw [hT] at h; cases h⟩
  have hm : (itabMethods I).isEmpty = false := by rw [IfaceMethods.itab_methods]; rfl
  unfold isIface
  iintro %Φ ⟨%htab, -, #Hd⟩ HΦ
  obtain ⟨tab, d⟩ := i
  simp only at htab
  subst htab
  rw [← iface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssertConcrete assertWord
  simp only [hm, Bool.false_eq_true, ↓reduceIte]
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  iapply HΦ; itrivial

/-- `i.(T)` for an empty interface of type `Ie` holding `x : T`. -/
theorem wp_type_assert_eface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder Ie : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem}
    [Ie ≤u go.InterfaceType elems] [IfaceMethods Ie []] (hT : isInterfaceType Tunder = false)
    (i : GoEface) (x : V) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isEface (GF := GF) i T x }} (App (Val (GoInstruction (TypeAssert Ie T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  haveI : NoGetitab Tunder T := ⟨fun h => by rw [hT] at h; cases h⟩
  have hm : (itabMethods Ie).isEmpty = true := by rw [IfaceMethods.itab_methods]; rfl
  unfold isEface
  iintro %Φ ⟨%ht, #Hd⟩ HΦ
  obtain ⟨tp, d⟩ := i
  simp only at ht
  subst ht
  rw [← eface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssertConcrete assertWord
  simp only [hm, ↓reduceIte]
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  iapply HΦ; itrivial

/-- `v, ok := i.(T)` for a non-empty interface of type `I` holding `x : T`. -/
theorem wp_type_assert2_iface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem}
    [I ≤u go.InterfaceType elems] {m : GoString} {ms : List GoString} [IfaceMethods I (m :: ms)]
    {z : val} [⟦GoZeroVal T, #()⟧ ⤳ Val z]
    (hT : isInterfaceType Tunder = false) (i : GoIface) (x : V)
    (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isIface (GF := GF) i I T x }} (App (Val (GoInstruction (TypeAssert2 I T))) (Val #i)) @ s; E
    {{ RET (PairV #x #true); True }} := by
  haveI : NoGetitab Tunder T := ⟨fun h => by rw [hT] at h; cases h⟩
  have hm : (itabMethods I).isEmpty = false := by rw [IfaceMethods.itab_methods]; rfl
  unfold isIface
  iintro %Φ ⟨%htab, -, #Hd⟩ HΦ
  obtain ⟨tab, d⟩ := i
  simp only at htab
  subst htab
  rw [← iface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssert2Concrete assertWord
  simp only [hm, Bool.false_eq_true, ↓reduceIte]
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  wp_pures
  iapply HΦ; itrivial

/-- `v, ok := i.(T)` for an empty interface of type `Ie` holding `x : T`. -/
theorem wp_type_assert2_eface {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T Tunder Ie : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [T ↓u Tunder] {elems : List go.InterfaceElem}
    [Ie ≤u go.InterfaceType elems] [IfaceMethods Ie []] {z : val} [⟦GoZeroVal T, #()⟧ ⤳ Val z]
    (hT : isInterfaceType Tunder = false)
    (i : GoEface) (x : V) (hsz : ByteRepr.size V < 2 ^ 64) :
    {{ isEface (GF := GF) i T x }} (App (Val (GoInstruction (TypeAssert2 Ie T))) (Val #i)) @ s; E
    {{ RET (PairV #x #true); True }} := by
  haveI : NoGetitab Tunder T := ⟨fun h => by rw [hT] at h; cases h⟩
  have hm : (itabMethods Ie).isEmpty = true := by rw [IfaceMethods.itab_methods]; rfl
  unfold isEface
  iintro %Φ ⟨%ht, #Hd⟩ HΦ
  obtain ⟨tp, d⟩ := i
  simp only at ht
  subst ht
  rw [← eface_val (GF := GF)]
  wp_pures
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  unfold typeAssert2Concrete assertWord
  simp only [hm, ↓reduceIte]
  wp_pures
  wp_apply wp_unbox T d .discard x hsz $$ [$Hd] as -
  wp_pures
  iapply HΦ; itrivial

/-- `==` on two nil empty interfaces. -/
theorem wp_eq_eface_nil :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType []))))
        (Val (PairV #(zero_val GoEface) #(zero_val GoEface)))) @ s; E
    {{ RET #true; True }} := by
  iintro %Φ _ HΦ
  rw [show (zero_val GoEface) = ⟨W64 0, W64 0⟩ from rfl, ← eface_val (GF := GF)]
  haveI := InterfaceSemanticsB.go_eq_interface [] (W64 0) (W64 0) (W64 0) (W64 0)
  iapply wp_go_step_receipt' (GoOp GoEquals (go.InterfaceType [])) _ _ Φ rfl
  inext
  iintro - -
  have hm : (itabMethods (go.InterfaceType [])).isEmpty = true := by
    rw [IfaceMethods.itab_methods]; rfl
  simp only [hm, ↓reduceIte]
  unfold efaceEq
  wp_pures
  iapply HΦ; itrivial

/-- `efaceeq` on two data pointers of the same comparable dynamic type `T`
calls `T`'s `Equal`. -/
theorem wp_efaceEq (T : go.GoType) [HasTypeDesc T] [TypeEqual T] (d1 d2 : w64)
    (Φ : val → IProp GF) :
    WP (App (Val (eqWrapper T)) (Val (PairV #d1 #d2))) @ s; E {{ Φ }} -∗
      WP (App (Val efaceEq) (Val (PairV #(typeAddr T) (PairV #d1 #d2)))) @ s; E {{ Φ }} := by
  obtain ⟨p, hp0, hpb, hpf⟩ := TypeEqual.equal (T := T)
  obtain ⟨f, hf, hfb⟩ := HasTypeDesc.tflag (T := T)
  have hne : typeAddr T ≠ W64 0 := HasTypeDesc.ne_zero (T := T)
  have hp0' : p ≠ W64 0 := hp0
  iintro Hwp
  iapply wp_static_bytes _ _ hpb rfl
  iintro #Hp
  iapply wp_static_bytes _ _ hfb rfl
  iintro #Hf
  iapply wp_static_func _ _ hpf rfl
  iintro #Hfn
  unfold efaceEq
  wp_pures
  rw [decide_eq_false hne]
  wp_pures
  wp_apply wp_loadWord (typeAddr T) 24 .discard p $$ [$Hp] as -
  wp_pures
  rw [decide_eq_false hp0']
  wp_pures
  wp_apply wp_loadByte (typeAddr T) 20 .discard f $$ [$Hf] as -
  wp_pures
  rw [hf, decide_eq_true rfl]
  wp_pures
  wp_apply wp_func_load p (eqWrapper T) $$ [$Hfn]
  iexact Hwp

/-- `Equal` of `T` on two boxed values is `==` on the values. -/
theorem wp_eqWrapper {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] (T : go.GoType)
    [TypeRepr T V] [TypeBytes T V] (d1 d2 : w64) (x1 x2 : V) (hsz : ByteRepr.size V < 2 ^ 64)
    (Φ : val → IProp GF) :
    bytesPointsto d1 .discard (ByteRepr.encode x1) -∗ bytesPointsto d2 .discard (ByteRepr.encode x2) -∗
      WP (App (Val (GoInstruction (GoOp GoEquals T))) (Val (PairV #x1 #x2))) @ s; E {{ Φ }} -∗
      WP (App (Val (eqWrapper T)) (Val (PairV #d1 #d2))) @ s; E {{ Φ }} := by
  iintro #Hd1 #Hd2 Hwp
  unfold eqWrapper
  wp_pures
  wp_apply wp_unbox T d1 .discard x1 hsz $$ [$Hd1] as -
  wp_pures
  wp_apply wp_unbox T d2 .discard x2 hsz $$ [$Hd2] as -
  wp_pures
  iexact Hwp

/-- `==` on two empty interfaces holding values of the same comparable type `T`
is `==` on the values (`efaceeq` calls `T`'s `Equal`). -/
theorem wp_eq_eface_same {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [HasTypeDesc T] [TypeEqual T] {elems : List go.InterfaceElem}
    [IfaceMethods (go.InterfaceType elems) []] (i1 i2 : GoEface) (x1 x2 : V)
    (hsz : ByteRepr.size V < 2 ^ 64) (Φ : val → IProp GF) :
    isEface i1 T x1 -∗ isEface i2 T x2 -∗
      WP (App (Val (GoInstruction (GoOp GoEquals T))) (Val (PairV #x1 #x2))) @ s; E {{ Φ }} -∗
      WP (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType elems))))
        (Val (PairV #i1 #i2))) @ s; E {{ Φ }} := by
  unfold isEface
  iintro ⟨%h1, #Hd1⟩ ⟨%h2, #Hd2⟩ Hwp
  obtain ⟨t1, d1⟩ := i1
  obtain ⟨t2, d2⟩ := i2
  simp only at h1 h2
  subst h1 h2
  rw [← eface_val (GF := GF), ← eface_val (GF := GF)]
  haveI := InterfaceSemanticsB.go_eq_interface elems (typeAddr T) d1 (typeAddr T) d2
  iapply wp_go_step_receipt' (GoOp GoEquals (go.InterfaceType elems)) _ _ Φ rfl
  inext
  iintro - -
  have hm : (itabMethods (go.InterfaceType elems)).isEmpty = true := by
    rw [IfaceMethods.itab_methods]; rfl
  simp only [hm, ↓reduceIte]
  iapply wp_efaceEq T d1 d2
  iapply wp_eqWrapper T d1 d2 x1 x2 hsz $$ Hd1 Hd2 Hwp

/-- `==` on two non-empty interfaces of type `I` holding values of the same
comparable type `T` is `==` on the values (`ifaceeq` calls `T`'s `Equal`). -/
theorem wp_eq_iface_same {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {T I : go.GoType}
    [TypeRepr T V] [TypeBytes T V] [HasTypeDesc T] [TypeEqual T] {elems : List go.InterfaceElem}
    {m : GoString} {ms : List GoString} [IfaceMethods (go.InterfaceType elems) (m :: ms)]
    (i1 i2 : GoIface) (x1 x2 : V) (hsz : ByteRepr.size V < 2 ^ 64) (Φ : val → IProp GF) :
    isIface i1 I T x1 -∗ isIface i2 I T x2 -∗
      WP (App (Val (GoInstruction (GoOp GoEquals T))) (Val (PairV #x1 #x2))) @ s; E {{ Φ }} -∗
      WP (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType elems))))
        (Val (PairV #i1 #i2))) @ s; E {{ Φ }} := by
  unfold isIface isItab
  iintro ⟨%h1, ⟨%h, #Hb, %hp⟩, #Hd1⟩ ⟨%h2, -, #Hd2⟩ Hwp
  obtain ⟨hne, -⟩ := hp
  obtain ⟨t1, d1⟩ := i1
  obtain ⟨t2, d2⟩ := i2
  simp only at h1 h2 hne
  subst h1 h2
  have hne' : itabAddr T I ≠ W64 0 := hne
  ihave #Ht := itab_type_bytes (itabAddr T I) (typeAddr I) (typeAddr T) h _ $$ Hb
  rw [← iface_val (GF := GF), ← iface_val (GF := GF)]
  haveI := InterfaceSemanticsB.go_eq_interface elems (itabAddr T I) d1 (itabAddr T I) d2
  iapply wp_go_step_receipt' (GoOp GoEquals (go.InterfaceType elems)) _ _ Φ rfl
  inext
  iintro - -
  have hm : (itabMethods (go.InterfaceType elems)).isEmpty = false := by
    rw [IfaceMethods.itab_methods]; rfl
  simp only [hm, Bool.false_eq_true, ↓reduceIte]
  unfold ifaceEq
  wp_pures
  rw [decide_eq_false hne']
  wp_pures
  wp_apply wp_loadWord (itabAddr T I) 8 .discard (typeAddr T) $$ [$Ht] as -
  wp_pures
  iapply wp_efaceEq T d1 d2
  iapply wp_eqWrapper T d1 d2 x1 x2 hsz $$ Hd1 Hd2 Hwp

/-- A non-empty interface holding a value is not `nil`. -/
theorem wp_eq_iface_nil {V : Type} [ByteRepr V] {T I : go.GoType} {elems : List go.InterfaceElem}
    (i : GoIface) (x : V) :
    {{ isIface (GF := GF) i I T x }}
      (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType elems))))
        (Val (PairV #i #(zero_val GoIface)))) @ s; E
    {{ RET #false; True }} := by
  unfold isIface isItab
  iintro %Φ ⟨-, ⟨%h, -, %hp⟩, -⟩ HΦ
  obtain ⟨hne, -⟩ := hp
  obtain ⟨tab, d⟩ := i
  simp only at hne
  have hne' : tab ≠ W64 0 := hne
  rw [show (zero_val GoIface) = ⟨W64 0, W64 0⟩ from rfl, ← iface_val (GF := GF),
    ← iface_val (GF := GF)]
  haveI := InterfaceSemanticsB.go_eq_interface elems tab d (W64 0) (W64 0)
  iapply wp_go_step_receipt' (GoOp GoEquals (go.InterfaceType elems)) _ _ Φ rfl
  inext
  iintro - -
  simp only [hne', ↓reduceIte]
  wp_pures
  iapply HΦ; itrivial

/-- An empty interface holding a value is not `nil`. -/
theorem wp_eq_eface_nil' {V : Type} [ByteRepr V] {T : go.GoType} [HasTypeDesc T]
    {elems : List go.InterfaceElem} (i : GoEface) (x : V) :
    {{ isEface (GF := GF) i T x }}
      (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType elems))))
        (Val (PairV #i #(zero_val GoEface)))) @ s; E
    {{ RET #false; True }} := by
  unfold isEface
  iintro %Φ ⟨%ht, -⟩ HΦ
  obtain ⟨tp, d⟩ := i
  simp only at ht
  subst ht
  have hne' : typeAddr T ≠ W64 0 := HasTypeDesc.ne_zero (T := T)
  rw [show (zero_val GoEface) = ⟨W64 0, W64 0⟩ from rfl, ← eface_val (GF := GF),
    ← eface_val (GF := GF)]
  haveI := InterfaceSemanticsB.go_eq_interface elems (typeAddr T) d (W64 0) (W64 0)
  iapply wp_go_step_receipt' (GoOp GoEquals (go.InterfaceType elems)) _ _ Φ rfl
  inext
  iintro - -
  simp only [hne', ↓reduceIte]
  wp_pures
  iapply HΦ; itrivial

end proofs

end Perennial
