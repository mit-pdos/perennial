/-
Sketch: the program logic of interfaces over the byte memory
(`Golang/Defn/StaticImage.lean`).

Resources, all persistent:
* `isItab tab T elems`: `tab` is an itab of the concrete type `T` for an
  interface with method set `elems`. It holds the itab's bytes (pointing at
  `T`'s descriptor and at `T`'s methods' code) and the facts about that code. A
  static itab gives one (`static_isItab`); so would one built by
  `runtime.getitab`, since it is defined by contents, not by address.
* `isIface i elems T x`, `isEface i T x`: an interface value whose dynamic type
  is `T`, with dynamic value `x` (boxed: `data ↦∗□ encode x`).

The specs of the lowered primitives are `sorry`'d.
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

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics] [go.StaticSymbols] [go.InterfaceSemanticsB]
variable {s : Stuckness} {E : CoPset}

open ProofMode go

attribute [local instance] InterfaceSemanticsB.go_eq_interface
  InterfaceSemanticsB.convert_to_interface InterfaceSemanticsB.type_assert_step
  InterfaceSemanticsB.method_interface

/-! ## Typed points-to for interface values (one heap cell, as for `GoInterface`) -/

instance typedPointsto_eface : TypedPointsto (GF := GF) GoEface :=
  heapTypedPointsto GoEface go.intoVal_inj

instance typedPointsto_iface : TypedPointsto (GF := GF) GoIface :=
  heapTypedPointsto GoIface go.intoVal_inj

instance intoVal_typed_eface :
    IntoValTypedUnderlying (GF := GF) GoEface (go.InterfaceType []) := by
  sorry -- as `intoVal_typed_interface`; `solve_into_val_typed` does not step `GoAlloc` here

instance intoVal_typed_iface (e : go.InterfaceElem) (es : List go.InterfaceElem) :
    IntoValTypedUnderlying (GF := GF) GoIface (go.InterfaceType (e :: es)) := by
  sorry

/-! ## Resources -/

/-- `tab` is an itab of `T` for an interface with methods `elems`. -/
def isItab (tab : w64) (T : go.GoType) (elems : List go.InterfaceElem) : IProp GF :=
  iprop(∃ (inter : w64) (h : w32),
    bytesPointsto tab .discard
      (itabBytes inter (typeAddr T) h ((ifaceMethodNames elems).map (methodAddr T))) ∗
    ⌜IsTypeDesc (typeAddr T) T ∧ ∀ m ∈ ifaceMethodNames elems, StaticMethod T m⌝)

/-- A non-empty interface value of dynamic type `T` and value `x`. -/
def isIface {V : Type} [ByteRepr V] (i : GoIface) (elems : List go.InterfaceElem)
    (T : go.GoType) (x : V) : IProp GF :=
  iprop(isItab i.tab T elems ∗ bytesPointsto i.data .discard (ByteRepr.encode x))

/-- An empty interface value of dynamic type `T` and value `x`. -/
def isEface {V : Type} [ByteRepr V] (i : GoEface) (T : go.GoType) (x : V) : IProp GF :=
  iprop(⌜IsTypeDesc i.tptr T ∧ i.tptr = typeAddr T⌝ ∗
    bytesPointsto i.data .discard (ByteRepr.encode x))

instance isItab_persistent (tab : w64) (T : go.GoType) (elems : List go.InterfaceElem) :
    Persistent (isItab (GF := GF) tab T elems) := by
  unfold isItab; infer_instance

instance isIface_persistent {V : Type} [ByteRepr V] (i : GoIface) elems T (x : V) :
    Persistent (isIface (GF := GF) i elems T x) := by
  unfold isIface; infer_instance

instance isEface_persistent {V : Type} [ByteRepr V] (i : GoEface) T (x : V) :
    Persistent (isEface (GF := GF) i T x) := by
  unfold isEface; infer_instance

/-- A static itab gives `isItab` (from the static bytes). -/
theorem static_isItab {e : Expr} {Φ : val → IProp GF} (T I : go.GoType)
    (elems : List go.InterfaceElem) (h : StaticItab T I (ifaceMethodNames elems))
    (hm : ∀ m ∈ ifaceMethodNames elems, StaticMethod T m) (he : toVal e = none) :
    (isItab (GF := GF) (itabAddr T I) T elems -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  obtain ⟨hT, -, hash, hbytes⟩ := h
  iintro H
  iapply wp_static_bytes _ _ hbytes he
  iintro #Hb
  iapply H
  unfold isItab
  iexists typeAddr I, hash
  iframe Hb
  ipureintro; exact ⟨hT, hm⟩

/-! ## Specs of the primitives (`sorry`'d) -/

theorem wp_boxBytes {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V] (x : V) :
    {{ (True : IProp GF) }} (App (Val (boxBytes T)) (Val #x)) @ s; E
    {{ (d : w64), RET #d; bytesPointsto d .discard (ByteRepr.encode x) }} := by
  sorry

theorem wp_loadAt {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V] (d : w64)
    (dq : DFrac) (x : V) :
    {{ bytesPointsto (GF := GF) d dq (ByteRepr.encode x) }} (App (Val (loadAt T)) (Val #d)) @ s; E
    {{ RET #x; bytesPointsto d dq (ByteRepr.encode x) }} := by
  sorry

theorem wp_itabFun (tab : w64) (T : go.GoType) (elems : List go.InterfaceElem) (m : GoString)
    (hm : m ∈ ifaceMethodNames elems) :
    {{ isItab (GF := GF) tab T elems }}
      (App (Val (itabFun (methodIndex elems m))) (Val #tab)) @ s; E
    {{ RET #(methodAddr T m); True }} := by
  sorry

/-- The code at a static code address. -/
theorem wp_static_func {e : Expr} {Φ : val → IProp GF} (p : w64) (v : val)
    (h : staticFuncs !! p = some v) (he : toVal e = none) :
    (isFunc (GF := GF) p v -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  sorry

/-- `x.(T)` for an empty interface holding a `T`. -/
theorem wp_typeAssert_eface {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V]
    (i : GoEface) (x : V) :
    {{ isEface (GF := GF) i T x }} (App (Val (typeAssertV T)) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  sorry

/-- `i.(T)` for a non-empty interface holding a `T`. -/
theorem wp_typeAssert_iface {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V]
    (i : GoIface) (elems : List go.InterfaceElem) (x : V) :
    {{ isIface (GF := GF) i elems T x }} (App (Val (typeAssertV T)) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  sorry

/-- `i.(J)` for a non-empty interface `J` that the dynamic type `T` implements:
`runtime.getitab` returns an itab of `T` for `J` (the static one if there is
one; otherwise a new one). TODO: the runtime's itab-table invariant
(`runtime`'s `isPkgInit`) as a premise. -/
theorem wp_typeAssert_iface_iface {V : Type} [ByteRepr V] (J : go.GoType)
    {Jelems : List go.InterfaceElem} [J ≤u go.InterfaceType Jelems] (i : GoIface)
    (elems : List go.InterfaceElem) (T : go.GoType) (x : V) (hne : Jelems ≠ [])
    (hm : ∀ m ∈ ifaceMethodNames Jelems, StaticMethod T m) :
    {{ isIface (GF := GF) i elems T x }} (App (Val (typeAssertV J)) (Val #i)) @ s; E
    {{ (j : GoIface), RET #j; isIface j Jelems T x }} := by
  sorry

/-- `==` on two nil empty interfaces. -/
theorem wp_ifaceEq_nil :
    {{ (True : IProp GF) }}
      (App (Val ifaceEqV) (Val (PairV #(zero_val GoEface) #(zero_val GoEface)))) @ s; E
    {{ RET #true; True }} := by
  sorry

/-! ## The interface abstraction

Program proofs use `isIface i elems T x` and the specs below, at the level of the
Go instructions; that an interface value is an itab and a boxed value is
internal to this file. The static prerequisites of a conversion are an instance
of `ImplementsStatic T I` (goose would generate one per conversion in the
package's static assumptions). -/

/-- `T` implements an interface with methods `elems`: its methods' code is in the
image (all that `runtime.getitab` needs to build an itab). -/
class Implements (T : go.GoType) (elems : List go.InterfaceElem) : Prop where
  methods : ∀ m ∈ ifaceMethodNames elems, StaticMethod T m

/-- A conversion of `T` to the interface `I` (with methods `elems`) also relies on
the static itab. -/
class ImplementsStatic (T I : go.GoType) (elems : outParam (List go.InterfaceElem)) : Prop
    extends Implements T elems where
  itab : StaticItab T I (ifaceMethodNames elems)

/-- `T`'s descriptor is in the image. -/
class HasTypeDesc (T : go.GoType) : Prop where
  desc : IsTypeDesc (typeAddr T) T

/-- Solves `m ∈ ifaceMethodNames elems` for a concrete method set. -/
macro "solve_iface_mem" : tactic => `(tactic| (apply mem_ifaceMethodNames'; simp))

omit [FfiSemantics ext ffi] in
include hG in
theorem iface_val (tab d : w64) : PairV #true (PairV #tab #d) = #(⟨tab, d⟩ : GoIface) := by
  rw [intoVal_unfold GoIface]

/-- `I(x)` for a concrete `x : T` and a non-empty interface `I`. -/
theorem wp_convert_iface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] {elems : List go.InterfaceElem} [I ≤u go.InterfaceType elems]
    [ImplementsStatic T I elems] (hT : isInterfaceType Tunder = false) (hne : elems ≠ []) (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoIface), RET #i; isIface i elems T x }} := by
  iintro %Φ _ HΦ
  iapply static_isItab T I elems (ImplementsStatic.itab) (Implements.methods (T := T)) rfl
  iintro #Htab
  wp_pures
  have he : elems.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hT, he, Bool.false_eq_true, ↓reduceIte]
  wp_apply wp_boxBytes T x as %d #Hd
  wp_pures
  rw [iface_val (GF := GF)]
  iapply HΦ
  unfold isIface
  isplitl
  · iexact Htab
  · iexact Hd

/-- `i.m` on an interface holding `x : T` resolves to `T`'s method `m` on `x`. -/
theorem wp_iface_method_resolve {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] [NotInterface Tunder] {elems : List go.InterfaceElem}
    [I ≤u go.InterfaceType elems] (m : GoString) (i : GoIface) (x : V)
    (hm : m ∈ ifaceMethodNames elems := by solve_iface_mem) :
    {{ isIface (GF := GF) i elems T x }}
      (App (Val (GoInstruction (MethodResolve I m))) (Val #i)) @ s; E
    {{ RET #(methods T m #x); True }} := by
  unfold isIface
  iintro %Φ ⟨#Htab, #Hd⟩ HΦ
  unfold isItab
  icases Htab with ⟨%inter, %h, #Hb, %hpure⟩
  obtain ⟨hdesc, hmeth⟩ := hpure
  wp_pures
  wp_apply wp_itabFun i.tab T elems m hm $$ []
  · unfold isItab; iexists inter, h; iframe Hb; ipureintro; exact ⟨hdesc, hmeth⟩
  iapply wp_static_func _ _ (hmeth m hm) rfl
  iintro #Hf
  wp_apply wp_func_load (methodAddr T m) (ifnWrapper T m) $$ [$Hf]
  unfold ifnWrapper
  wp_pures
  wp_apply wp_loadAt T i.data .discard x $$ [$Hd] as -
  wp_pures
  iapply HΦ; itrivial

omit [FfiSemantics ext ffi] in
include hG in
theorem eface_val (t d : w64) : PairV #false (PairV #t #d) = #(⟨t, d⟩ : GoEface) := by
  rw [intoVal_unfold GoEface]

/-- `I(x)` for a concrete `x : T` and the empty interface. -/
theorem wp_convert_eface {V : Type} [ZeroVal V] [ByteRepr V] {T Tunder I : go.GoType}
    [TypeRepr T V] [T ↓u Tunder] [I ≤u go.InterfaceType []] [HasTypeDesc T]
    (hT : isInterfaceType Tunder = false) (x : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert T I))) (Val #x)) @ s; E
    {{ (i : GoEface), RET #i; isEface i T x }} := by
  iintro %Φ _ HΦ
  wp_pures
  simp only [hT, List.isEmpty_nil, Bool.false_eq_true, ↓reduceIte]
  wp_apply wp_boxBytes T x as %d #Hd
  wp_pures
  rw [eface_val (GF := GF)]
  iapply HΦ
  unfold isEface
  isplitr
  · ipureintro; exact ⟨HasTypeDesc.desc, rfl⟩
  · iexact Hd

/-- `i.(T)` for an empty interface holding `x : T`. -/
theorem wp_type_assert_eface {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V]
    (i : GoEface) (x : V) :
    {{ isEface (GF := GF) i T x }} (App (Val (GoInstruction (TypeAssert T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  iintro %Φ #Hi HΦ
  wp_pures
  wp_apply wp_typeAssert_eface T i x $$ [$Hi]
  iapply HΦ; itrivial

/-- `i.(T)` for a non-empty interface holding `x : T`. -/
theorem wp_type_assert_iface {V : Type} [ZeroVal V] [ByteRepr V] (T : go.GoType) [TypeRepr T V]
    (i : GoIface) (elems : List go.InterfaceElem) (x : V) :
    {{ isIface (GF := GF) i elems T x }} (App (Val (GoInstruction (TypeAssert T))) (Val #i)) @ s; E
    {{ RET #x; True }} := by
  iintro %Φ #Hi HΦ
  wp_pures
  wp_apply wp_typeAssert_iface T i elems x $$ [$Hi]
  iapply HΦ; itrivial

/-- `i.(J)` for a non-empty interface `J` that the dynamic type implements (through
`runtime.getitab`); the result is an interface like any other. -/
theorem wp_type_assert_iface_iface {V : Type} [ByteRepr V] (J : go.GoType)
    {Jelems : List go.InterfaceElem} [J ≤u go.InterfaceType Jelems] (i : GoIface)
    (elems : List go.InterfaceElem) (T : go.GoType) [Implements T Jelems] (x : V)
    (hne : Jelems ≠ []) :
    {{ isIface (GF := GF) i elems T x }} (App (Val (GoInstruction (TypeAssert J))) (Val #i)) @ s; E
    {{ (j : GoIface), RET #j; isIface j Jelems T x }} := by
  iintro %Φ #Hi HΦ
  wp_pures
  wp_apply wp_typeAssert_iface_iface J i elems T x hne Implements.methods $$ [$Hi] as %j #Hj
  iapply HΦ $$ Hj

/-- `==` on two nil empty interfaces. -/
theorem wp_eq_eface_nil :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoOp GoEquals (go.InterfaceType []))))
        (Val (PairV #(zero_val GoEface) #(zero_val GoEface)))) @ s; E
    {{ RET #true; True }} := by
  iintro %Φ _ HΦ
  wp_pures
  wp_apply wp_ifaceEq_nil
  iapply HΦ; itrivial

end proofs

end Perennial
