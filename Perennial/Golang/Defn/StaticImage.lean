/-
Sketch: interfaces over the byte memory, with the program image's static data
(type descriptors, itabs, method code) as assumptions.

What the compiler and linker emit statically is not constructed by the
semantics: it is abstract (`staticBytes`, `staticFuncs` in `GoGlobalContext`;
the symbol addresses in `StaticSymbols`), and packages state facts about their
own static data (`IsTypeDesc`, `StaticItab`, `StaticMethod`), like the
generated `Assumptions` classes. The byte memory starts with the static bytes
frozen (`staticImage`), so `a ↦∗□ bs` is available for them
(`wp_static_bytes`).

Interfaces follow the Go runtime's representation:
* an empty interface is `(tptr, data)`, a type-descriptor pointer and a data
  pointer (`GoEface`); a non-empty one is `(itab, data)` (`GoIface`);
* a dynamic value is boxed: `data` points to its bytes (`boxBytes`);
* `Convert T I` uses the static itab `itabAddr T I`; a method call loads
  `itab.Fun[k]` and calls that code with the data word (`methodAddr T m`, the
  method's wrapper `ifnWrapper T m`); an assertion to an interface goes through
  `runtime.getitab`.

Status: the lowered operations are `sorry`'d primitives, and the contents of
type descriptors are not yet constrained (`IsTypeDesc`). Two simplifications:
* `GoEface` and `GoIface` values are tagged (`(false, _)`/`(true, _)`): goose emits
  `TypeAssert t` with the target type only, while the lowering needs to know
  whether the source is an empty interface (whose first word is a type) or not
  (an itab). The compiler knows the source type; goose should emit it, and the
  tag then disappears.
* dynamic values whose representation is not bytes yet (pointers are `Loc`s,
  strings `GoString`s) cannot be boxed; only `ByteRepr` types are.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Golang.Defn.ByteRepr

@[expose] public section

noncomputable section

namespace Perennial

namespace go

/-! ## Symbols and static facts -/

/-- Symbol addresses of the program image (to become fields of
`GoSemanticsFunctions`). -/
class StaticSymbols where
  /-- `type:T`: the descriptor of a type -/
  typeAddr : go.GoType → w64
  /-- `go:itab.T,I`: the static itab of the concrete type `T` for the interface `I` -/
  itabAddr : go.GoType → go.GoType → w64
  /-- the entry of method `m` of `T` as called through an itab: it takes the
  data word (`ifnWrapper`) -/
  methodAddr : go.GoType → GoString → w64
  /-- which type's descriptor is at an address: one address, one type -/
  staticTypeAt : w64 → Option go.GoType

export StaticSymbols (typeAddr itabAddr methodAddr staticTypeAt)

section facts
variable [FfiSyntax] [GoGlobalContext]

/-- The static bytes at `a` are `bs`. -/
def StaticBytesAt (a : w64) (bs : List w8) : Prop :=
  ∀ i (hi : i < bs.length), staticBytes !! byteAddr a i = some bs[i]

variable [StaticSymbols]

/-- `p` is the descriptor of `t` (an `internal/abi.Type`). TODO: constrain the
contents (kind, size, alignment, `Equal`, element types, the uncommon section). -/
def IsTypeDesc (p : w64) (t : go.GoType) : Prop :=
  staticTypeAt p = some t ∧ ∃ bs : List w8, bs.length = 48 ∧ StaticBytesAt p bs

/-- The bytes of an itab (`internal/abi.ITab`): `Inter`, `Type`, `Hash`
(padded) and `Fun[0..k)`. -/
def itabBytes (inter typ : w64) (hash : w32) (fns : List w64) : List w8 :=
  ByteRepr.encode inter ++ ByteRepr.encode typ ++ ByteRepr.encode hash ++ [0, 0, 0, 0] ++
    fns.flatMap ByteRepr.encode

/-- The method names of an interface type in itab order (sorted by name). -/
def ifaceMethodNames (elems : List go.InterfaceElem) : List GoString :=
  (elems.filterMap fun | .MethodElem m _ => some m | _ => none).mergeSort
    (fun a b => decide (GoStringLe a b))

theorem mem_ifaceMethodNames {elems : List go.InterfaceElem} {m : GoString} {sig : go.signature}
    (h : go.InterfaceElem.MethodElem m sig ∈ elems) : m ∈ ifaceMethodNames elems := by
  unfold ifaceMethodNames
  rw [List.mem_mergeSort]
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_ifaceMethodNames' {elems : List go.InterfaceElem} {m : GoString}
    (h : m ∈ elems.filterMap fun | .MethodElem m _ => some m | _ => none) :
    m ∈ ifaceMethodNames elems := by
  unfold ifaceMethodNames
  rw [List.mem_mergeSort]
  exact h

/-- The index of method `m` in the itab of an interface type. -/
def methodIndex (elems : List go.InterfaceElem) (m : GoString) : Nat :=
  (ifaceMethodNames elems).idxOf m

/-- The static itab of `t` for the interface `i` (with methods `ms`, in order). -/
def StaticItab (t i : go.GoType) (ms : List GoString) : Prop :=
  IsTypeDesc (typeAddr t) t ∧ IsTypeDesc (typeAddr i) i ∧
  ∃ h, StaticBytesAt (itabAddr t i) (itabBytes (typeAddr i) (typeAddr t) h (ms.map (methodAddr t)))

end facts

/-! ## Lowered operations (primitives, `sorry`'d) -/

section primitives
variable [FfiSyntax] [GoGlobalContext]

/-- `convT`: box a value of type `t` (allocate its bytes). -/
def boxBytes (_t : go.GoType) : val := sorry
/-- Load the value of type `t` whose bytes are at the data word. -/
def loadAt (_t : go.GoType) : val := sorry
/-- `itab.Fun[k]`: the code address of the `k`-th method. -/
def itabFun (_k : Nat) : val := sorry
/-- `itab.Type`. -/
def itabType : val := sorry
/-- `runtime.getitab(inter, typ, canfail)` (to be translated). -/
def getitab : val := sorry
/-- `x.(T)` (`TypeAssert T`), lowered: compare descriptors, or `getitab`. -/
def typeAssertV (_t : go.GoType) : val := sorry
/-- `efaceeq`/`ifaceeq`. -/
def ifaceEqV : val := sorry
/-- Interface-to-interface conversion. -/
def convI2IV (_to : go.GoType) : val := sorry

/-- The code of method `m` of `t` called through an itab: load the receiver from
the data word and call the method. -/
def ifnWrapper (t : go.GoType) (m : GoString) : val :=
  LamV "d" (App (Val (GoInstruction (MethodResolve t m))) (App (Val (loadAt t)) (Var "d")))

variable [StaticSymbols]

/-- The code of method `m` of `t` is at `methodAddr t m`. -/
def StaticMethod (t : go.GoType) (m : GoString) : Prop :=
  staticFuncs !! methodAddr t m = some (ifnWrapper t m)

end primitives

/-! ## The representation of interface values -/

/-- An empty interface value: a type-descriptor pointer and a data pointer. -/
structure _root_.Perennial.GoEface where
  tptr : w64
  data : w64
deriving DecidableEq, Inhabited

/-- A non-empty interface value: an itab pointer and a data pointer. -/
structure _root_.Perennial.GoIface where
  tab : w64
  data : w64
deriving DecidableEq, Inhabited

instance : ZeroVal GoEface := ⟨⟨0, 0⟩⟩
instance : ZeroVal GoIface := ⟨⟨0, 0⟩⟩

section semantics
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [StaticSymbols]

/-- The interface semantics over the byte memory (replaces `InterfaceSemantics`). -/
class InterfaceSemanticsB : Prop where
  eface_repr : TypeReprUnderlying (go.InterfaceType []) GoEface
  iface_repr (e : go.InterfaceElem) (es : List go.InterfaceElem) :
    TypeReprUnderlying (go.InterfaceType (e :: es)) GoIface
  eface_unfold : IntoValUnfold GoEface (fun i => PairV #false (PairV #i.tptr #i.data))
  iface_unfold : IntoValUnfold GoIface (fun i => PairV #true (PairV #i.tab #i.data))
  eface_inj : IntoValInj GoEface
  iface_inj : IntoValInj GoIface
  is_comparable_interface (elems : List go.InterfaceElem) :
    ⟦CheckComparable (go.InterfaceType elems), #()⟧ ⤳[under] #()
  go_eq_interface (elems : List go.InterfaceElem) (v : val) :
    ⟦GoOp GoEquals (go.InterfaceType elems), v⟧ ⤳[under] (App (Val ifaceEqV) (Val v))
  /-- `I(v)` for a concrete `v`: box it, with the static itab (or descriptor) -/
  convert_to_interface (v : val) {from_ funder to : go.GoType} {elems : List go.InterfaceElem}
    [from_ ↓u funder] [to ≤u go.InterfaceType elems] :
    ⟦Convert from_ to, v⟧ ⤳
    (if isInterfaceType funder then App (Val (convI2IV to)) (Val v)
     else if elems.isEmpty then
       App (Val (LamV "d" (Pair (Val #false) (Pair (Val #(typeAddr from_)) (Var "d")))))
         (App (Val (boxBytes from_)) (Val v))
     else
       App (Val (LamV "d" (Pair (Val #true) (Pair (Val #(itabAddr from_ to)) (Var "d")))))
         (App (Val (boxBytes from_)) (Val v)))
  type_assert_step (t : go.GoType) (v : val) :
    ⟦TypeAssert t, v⟧ ⤳ (App (Val (typeAssertV t)) (Val v))
  /-- `i.M`: the method's code from the itab, applied to the data word -/
  method_interface (m : GoString) {t : go.GoType} {elems : List go.InterfaceElem}
    [t ≤u go.InterfaceType elems] (i : GoIface) :
    ⟦MethodResolve t m, #i⟧ ⤳
    (App (FuncLoad (App (Val (itabFun (methodIndex elems m))) (Val #i.tab))) (Val #i.data))

/- The steps of the interface instructions are not instances: program proofs
use the specs of `Golang/Theory/StaticIface.lean`, which hide the representation;
that file makes them local instances. -/
attribute [instance] InterfaceSemanticsB.eface_repr InterfaceSemanticsB.iface_repr
  InterfaceSemanticsB.eface_unfold InterfaceSemanticsB.iface_unfold
  InterfaceSemanticsB.eface_inj InterfaceSemanticsB.iface_inj
  InterfaceSemanticsB.is_comparable_interface

end semantics

/-- The Go semantics with interfaces over the byte memory (`go.Semantics` with
`InterfaceSemanticsB` in place of `InterfaceSemantics`). -/
class SemanticsB [FfiSyntax] [GoLocalContext] [GoGlobalContext] where
  [sem_fn : GoSemanticsFunctions]
  [symbols : StaticSymbols]
  [core_sem : go.PreSemantics]
  [interface_sem : go.InterfaceSemanticsB]
  [chan_sem : go.ChanSemantics]
  [string_sem : go.StringSemantics]

attribute [instance] SemanticsB.sem_fn SemanticsB.symbols SemanticsB.core_sem
  SemanticsB.interface_sem SemanticsB.chan_sem SemanticsB.string_sem

end go

end Perennial
