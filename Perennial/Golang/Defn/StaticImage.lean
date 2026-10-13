/-
Sketch: interfaces over the byte memory, with the program image's static data
(type descriptors, itabs, method and equality code) as assumptions.

What the compiler and linker emit statically is not constructed by the
semantics: it is abstract (`staticBytes`, `staticFuncs` in `GoGlobalContext`;
the symbols and the itab method order in `StaticSymbols`), and packages state
facts about their own static data (`HasTypeDesc`, `TypeEqual`, `StaticItab`,
`StaticMethod`, `IfaceMethods`, `TypeBytes`), like the generated `Assumptions`
classes. The byte memory starts with the static bytes frozen (`staticImage`),
so `a ↦∗□ bs` is available for them (`wp_static_bytes`).

Interfaces follow the gc compiler and runtime (`internal/abi`, `runtime/iface.go`,
`runtime/alg.go`):
* an interface whose method set is empty is two words `(type, data)`, a
  type-descriptor pointer and a data pointer (`GoEface`, `runtime.eface`); any
  other is `(tab, data)`, an itab pointer and a data pointer (`GoIface`,
  `runtime.iface`); nil is `(0, 0)`. There is no tag: an interface value is
  read according to its static type, so memory reinterpreted through
  `unsafe.Pointer` or `(*I2)(&a)` behaves as in Go;
* a dynamic value is boxed: `data` points to a frozen copy of its bytes
  (`boxBytes`, `runtime.convT`);
* `I(x)` for a concrete `x : T` uses the static itab `itabAddr T I`
  (`go:itab.T,I`), or the descriptor `typeAddr T` when `I`'s method set is empty;
  a method call loads `itab.Fun[k]`, `k` the method's index in the itab
  (`itabMethods I`), and calls that code with the data word (`methodAddr T m`,
  whose code is `ifnWrapper T m`);
* `x.(T)` and `x, ok := x.(T)` compare the type word with `type:T`, or the itab
  pointer with `go:itab.T,I`, as the compiler does (not the itab's contents);
* `==` compares the type words, then calls the dynamic type's `Equal` from its
  descriptor (`runtime.efaceeq`, `ifaceeq`).

Status and simplifications:
* not modelled (stuck): an assertion or conversion to a non-empty interface
  from an interface (`runtime.getitab`, to be translated, as are the runtime's
  type-switch caches); the contents of type descriptors are constrained only in
  the fields the lowerings read (`TFlag`, `Equal`) and their size;
* dynamic values are boxed even when Go stores them directly in the data word
  (pointer-shaped types): only types with a `ByteRepr` layout can be boxed, and
  pointers are still `Loc`s, strings `GoString`s, so no direct type has one;
* the boxes are frozen and allocated with `BAllocFrozen`, which may share
  them (as Go may: `zerobase`, `staticuint64s`, read-only constants).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Golang.Defn.ByteRepr

@[expose] public section

noncomputable section

namespace Perennial

/-! ## Interface values and their layout -/

/-- An empty interface value (`runtime.eface`): a type-descriptor pointer and a
data pointer. -/
structure GoEface where
  tptr : w64
  data : w64
deriving DecidableEq, Inhabited

/-- A non-empty interface value (`runtime.iface`): an itab pointer and a data
pointer. -/
structure GoIface where
  tab : w64
  data : w64
deriving DecidableEq, Inhabited

instance : ZeroVal GoEface := ⟨⟨0, 0⟩⟩
instance : ZeroVal GoIface := ⟨⟨0, 0⟩⟩

namespace ByteRepr

/-- Two words (16 bytes, aligned to 8). -/
instance instGoEface : ByteRepr GoEface where
  size := 16
  align := 8
  encode i := encode i.tptr ++ encode i.data
  decode bs := (decodePair bs).map fun p => ⟨p.1, p.2⟩
  align_pos := by decide
  align_pow2 := ⟨3, rfl⟩
  align_dvd_size := by decide
  length_encode i := by simp [length_encode]; rfl
  decode_encode i := by simp [(decodePair_iff _ i.tptr i.data).mpr rfl]
  length_of_decode bs v h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, _⟩ := h
    exact decodePair_length bs p hp

/-- Two words (16 bytes, aligned to 8). -/
instance instGoIface : ByteRepr GoIface where
  size := 16
  align := 8
  encode i := encode i.tab ++ encode i.data
  decode bs := (decodePair bs).map fun p => ⟨p.1, p.2⟩
  align_pos := by decide
  align_pow2 := ⟨3, rfl⟩
  align_dvd_size := by decide
  length_encode i := by simp [length_encode]; rfl
  decode_encode i := by simp [(decodePair_iff _ i.tab i.data).mpr rfl]
  length_of_decode bs v h := by
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨p, hp, _⟩ := h
    exact decodePair_length bs p hp

end ByteRepr

/-- The zero value of `V` is all zero bytes: Go's zeroed memory holds zero
values (`mallocgc` zeroes, and `var x T` is the zero value). Required of every
layout a type is given (`TypeBytes`). -/
class ZeroBytes (V : Type) [ZeroVal V] [ByteRepr V] : Prop where
  encode_zero : ByteRepr.encode (zero_val V) = List.replicate (ByteRepr.size V) 0

instance : ZeroBytes w8 := ⟨rfl⟩
instance : ZeroBytes w16 := ⟨rfl⟩
instance : ZeroBytes w32 := ⟨rfl⟩
instance : ZeroBytes w64 := ⟨rfl⟩
instance : ZeroBytes Bool := ⟨rfl⟩
instance : ZeroBytes GoEface := ⟨rfl⟩
instance : ZeroBytes GoIface := ⟨rfl⟩

namespace go

/-! ## Symbols and static facts -/

/-- Symbol addresses of the program image and the itab layout of interface
types (to become fields of `GoSemanticsFunctions`). -/
class StaticSymbols where
  /-- `type:T`: the descriptor of a type -/
  typeAddr : go.GoType → w64
  /-- `go:itab.T,I`: the static itab of the concrete type `T` for the interface `I` -/
  itabAddr : go.GoType → go.GoType → w64
  /-- the entry of method `m` of `T` as called through an itab: it takes the
  data word (`ifnWrapper`) -/
  methodAddr : go.GoType → GoString → w64
  /-- the methods of an interface type in its itabs' order: the flattened method
  set, sorted as `cmd/compile` sorts it (`types.CompareSyms`: exported names
  first); goose provides it (`IfaceMethods`) -/
  itabMethods : go.GoType → List GoString
  /-- the byte layout of each type: the representation type and its layout; goose
  provides it (`TypeBytes`). A function of the type, so that a layout cannot be
  chosen by a proof. -/
  layoutOf : go.GoType → (V : Type) × ByteRepr V

export StaticSymbols (typeAddr itabAddr methodAddr itabMethods layoutOf)

/-- The layout of the Go type `t` is the `ByteRepr V` instance (generated by goose
for the program's types; the predeclared numeric and boolean types' are in
`BytesSemantics`). The layout's zero value must be zero bytes (`ZeroBytes`). -/
class TypeBytes [StaticSymbols] (t : go.GoType) (V : Type) [ZeroVal V] [inst : ByteRepr V]
    [ZeroBytes V] : Prop where
  type_bytes : layoutOf t = ⟨V, inst⟩

/-- The itab method order of the interface type `t` (generated by goose). -/
class IfaceMethods [StaticSymbols] (t : go.GoType) (ms : outParam (List GoString)) : Prop where
  itab_methods : itabMethods t = ms

/-- A conversion to `to`, or an assertion to `to`, of a value whose type has the
underlying type `funder` needs no `runtime.getitab`: the source is not an
interface, or `to`'s method set is empty. The steps that would need `getitab`
are left out (stuck), not modelled yet. -/
class NoGetitab [StaticSymbols] (funder to : go.GoType) : Prop where
  no_getitab : isInterfaceType funder = true → (itabMethods to).isEmpty = true

section facts
variable [FfiSyntax] [GoGlobalContext]

/-- The static bytes at `a` are `bs`. -/
def StaticBytesAt (a : w64) (bs : List w8) : Prop :=
  ∀ i (hi : i < bs.length), staticBytes !! byteAddr a i = some bs[i]

variable [StaticSymbols]

/-- An `internal/abi.Type` (48 bytes) is at `p`. -/
def IsTypeDesc (p : w64) : Prop :=
  ∃ bs : List w8, bs.length = 48 ∧ StaticBytesAt p bs

/-- `abi.TFlagDirectIface`: the type's values are stored in the data word. -/
abbrev tflagDirectIface : w8 := 32

/-- `T`'s descriptor is in the image (generated by goose), at a non-zero
address, with `TFlagDirectIface` clear in its `TFlag` (offset 20): the types
with a layout here are not pointer-shaped, so their values are boxed. TODO:
constrain the other fields (size, hash, kind, element types, ...). -/
class HasTypeDesc (T : go.GoType) : Prop where
  ne_zero : typeAddr T ≠ 0
  desc : IsTypeDesc (typeAddr T)
  tflag : ∃ f : w8, f &&& tflagDirectIface = 0 ∧
    StaticBytesAt (byteAddr (typeAddr T) 20) (ByteRepr.encode f)

/-- The bytes of an itab (`internal/abi.ITab`): `Inter`, `Type`, `Hash`
(padded) and `Fun[0..k)`. -/
def itabBytes (inter typ : w64) (hash : w32) (fns : List w64) : List w8 :=
  ByteRepr.encode inter ++ ByteRepr.encode typ ++ ByteRepr.encode hash ++ [0, 0, 0, 0] ++
    fns.flatMap ByteRepr.encode

/-- The static itab of `T` for the interface `I` (generated by goose for each
conversion of a `T` to an `I`, and each assertion of an `I` to `T`, in the
package): at a non-zero address, in read-only data. -/
class StaticItab (T I : go.GoType) : Prop where
  ne_zero : itabAddr T I ≠ 0
  itab : ∃ h, StaticBytesAt (itabAddr T I)
    (itabBytes (typeAddr I) (typeAddr T) h ((itabMethods I).map (methodAddr T)))

end facts

/-! ## Lowered operations -/

section code
variable [FfiSyntax] [GoGlobalContext] [StaticSymbols]

abbrev gi (i : GoInstruction) (e : Expr) : Expr := App (Val (GoInstruction i)) e
abbrev eqU (a b : Expr) : Expr := gi (GoOp GoEquals go.uint64) (Pair a b)
abbrev addU (a b : Expr) : Expr := gi (GoOp GoPlus go.uint64) (Pair a b)

/-- `convT`: box a value of type `t` (a frozen copy of its bytes). -/
def boxBytes (t : go.GoType) : val :=
  LamV "v" (BAllocFrozen (gi (EncodeBytes t) (Var "v")))

/-- The value of type `t` whose bytes are at the data word. -/
def unboxV (t : go.GoType) : val :=
  LamV "d" (gi (DecodeBytes t) (BLoad (Pair (Var "d") (gi (SizeOf t) (Val #())))))

/-- The word at offset `off` of a descriptor or itab. -/
def loadWord (off : Nat) : val :=
  LamV "p" (gi (DecodeBytes go.uint64)
    (BLoad (Pair (addU (Var "p") (Val #(BitVec.ofNat 64 off))) (Val #(W64 8)))))

/-- The byte at offset `off` of a descriptor. -/
def loadByte (off : Nat) : val :=
  LamV "p" (gi (DecodeBytes go.uint8)
    (BLoad (Pair (addU (Var "p") (Val #(BitVec.ofNat 64 off))) (Val #(W64 1)))))

/-- `itab.Fun[k]`, the code address of the itab's `k`-th method. -/
abbrev itabFun (k : Nat) : val := loadWord (24 + 8 * k)

/-- `itab.Type`. -/
abbrev itabType : val := loadWord 8

/-- The type word of an interface value of the interface type `from_` that
`x.(t)` compares, as the compiler does: `type:t` from an empty interface, the
itab `go:itab.t,from_` from a non-empty one. -/
def assertWord (from_ t : go.GoType) : w64 :=
  if (itabMethods from_).isEmpty then typeAddr t else itabAddr t from_

/-- `i.(t)` for a concrete `t` and `i` of the interface type `from_`
(`assertWord`): the value, or a run-time panic. -/
def typeAssertConcrete (from_ t : go.GoType) : val :=
  LamV "i" (If (eqU (Fst (Var "i")) (Val #(assertWord from_ t)))
    (App (Val (unboxV t)) (Snd (Var "i")))
    (Panic "type assertion failed"))

/-- `v, ok := i.(t)` for a concrete `t`: `(the value, true)`, or `(z, false)`
with `z` the zero value of `t`. -/
def typeAssert2Concrete (from_ t : go.GoType) (z : val) : val :=
  LamV "i" (If (eqU (Fst (Var "i")) (Val #(assertWord from_ t)))
    (Pair (App (Val (unboxV t)) (Snd (Var "i"))) (Val #true))
    (Pair (Val z) (Val #false)))

/-- Conversion of an interface of type `from_` to an empty interface (nil stays
nil): from a non-empty interface the type word is `itab.Type`. -/
def convToEface (from_ : go.GoType) : val :=
  if (itabMethods from_).isEmpty then LamV "i" (Var "i")
  else
    LamV "i" (Pair
      (If (eqU (Fst (Var "i")) (Val #(W64 0))) (Val #(W64 0))
        (App (Val itabType) (Fst (Var "i"))))
      (Snd (Var "i")))

/-- `i.(E)` for `i` of the interface type `from_` and an empty interface `E`: a
non-nil interface as an empty interface. -/
def typeAssertEface (from_ : go.GoType) : val :=
  LamV "i" (If (eqU (Fst (Var "i")) (Val #(W64 0))) (Panic "type assertion failed")
    (App (Val (convToEface from_)) (Var "i")))

/-- `v, ok := i.(E)` for an empty interface `E`: `(i as an empty interface,
true)` if `i` is not nil, else `(nil, false)`. -/
def typeAssert2Eface (from_ : go.GoType) : val :=
  LamV "i" (If (eqU (Fst (Var "i")) (Val #(W64 0))) (Pair (Val #(zero_val GoEface)) (Val #false))
    (Pair (App (Val (convToEface from_)) (Var "i")) (Val #true)))

/-- `runtime.efaceeq(t, x, y)`, applied to `(t, (x, y))`: `true` for a nil type;
for an uncomparable type (its descriptor's `Equal`, at offset 24, is nil) a
run-time panic; for a type stored in the data word (`TFlagDirectIface`, in
`TFlag` at offset 20) the words are compared; for any other, `Equal(x, y)` on
the data pointers. -/
def efaceEq : val :=
  LamV "a" (
    Let "t" (Fst (Var "a")) (
    If (eqU (Var "t") (Val #(W64 0))) (Val #true) (
    Let "eq" (App (Val (loadWord 24)) (Var "t")) (
    If (eqU (Var "eq") (Val #(W64 0))) (Panic "comparing uncomparable type") (
    If (gi (GoOp GoEquals go.uint8) (Pair
          (gi (GoOp GoAnd go.uint8) (Pair (App (Val (loadByte 20)) (Var "t"))
            (Val #tflagDirectIface)))
          (Val #(0 : w8))))
      (App (FuncLoad (Var "eq")) (Snd (Var "a")))
      (eqU (Fst (Snd (Var "a"))) (Snd (Snd (Var "a")))))))))

/-- `runtime.ifaceeq(tab, x, y)`: `true` for a nil itab, else `efaceeq` with the
itab's `Type`. -/
def ifaceEq : val :=
  LamV "a" (If (eqU (Fst (Var "a")) (Val #(W64 0))) (Val #true)
    (App (Val efaceEq) (Pair (App (Val itabType) (Fst (Var "a"))) (Snd (Var "a")))))

/-- The code of method `m` of `t` called through an itab: load the receiver from
the data word and call the method. -/
def ifnWrapper (t : go.GoType) (m : GoString) : val :=
  LamV "d" (gi (MethodResolve t m) (App (Val (unboxV t)) (Var "d")))

/-- The code of `t`'s descriptor's `Equal`: `==` on the values of type `t` at the
two pointers (what the compiler's equality function for `t` computes, e.g.
`runtime.memequal64`, `f64equal`, or a generated `type:.eq.T`). -/
def eqWrapper (t : go.GoType) : val :=
  LamV "pq" (gi (GoOp GoEquals t)
    (Pair (App (Val (unboxV t)) (Fst (Var "pq"))) (App (Val (unboxV t)) (Snd (Var "pq")))))

/-- The code of method `m` of `t` is at `methodAddr t m` (generated by goose). -/
def StaticMethod (t : go.GoType) (m : GoString) : Prop :=
  staticFuncs !! methodAddr t m = some (ifnWrapper t m)

/-- `T` is comparable, and its descriptor's `Equal` (offset 24) is a non-nil
func value whose code is `eqWrapper T` (generated by goose for the comparable
types the package converts to interfaces). -/
class TypeEqual (T : go.GoType) : Prop where
  equal : ∃ p : w64, p ≠ 0 ∧ StaticBytesAt (byteAddr (typeAddr T) 24) (ByteRepr.encode p) ∧
    staticFuncs !! p = some (eqWrapper T)

end code

section semantics
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [StaticSymbols]

/-- The byte encoding of values: the layout of `t` (`TypeBytes`, a function of the
type), and the layouts of the predeclared numeric and boolean types (Go's on
64-bit platforms: `int`, `uint` and `uintptr` are 8 bytes; floats are their
IEEE 754 bits). -/
class BytesSemantics : Prop where
  int_bytes : TypeBytes go.int w64
  int64_bytes : TypeBytes go.int64 w64
  int32_bytes : TypeBytes go.int32 w32
  int16_bytes : TypeBytes go.int16 w16
  int8_bytes : TypeBytes go.int8 w8
  uint_bytes : TypeBytes go.uint w64
  uint64_bytes : TypeBytes go.uint64 w64
  uint32_bytes : TypeBytes go.uint32 w32
  uint16_bytes : TypeBytes go.uint16 w16
  uint8_bytes : TypeBytes go.uint8 w8
  uintptr_bytes : TypeBytes go.uintptr w64
  float64_bytes : TypeBytes go.float64 w64
  float32_bytes : TypeBytes go.float32 w32
  bool_bytes : TypeBytes go.bool Bool
  encode_step {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {t : go.GoType} [TypeRepr t V]
    [TypeBytes t V] (x : V) :
    ⟦EncodeBytes t, #x⟧ ⤳ (Val (blobV (ByteRepr.encode x)))
  /-- Decoding the encoding of `x` gives `x`. Bytes that are not an encoding have
  no step: Go has no behaviour for them (only `unsafe` code can produce them). -/
  decode_step {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {t : go.GoType} [TypeRepr t V]
    [TypeBytes t V] (x : V) :
    ⟦DecodeBytes t, blobV (ByteRepr.encode x)⟧ ⤳ Val #x
  size_step {V : Type} [ZeroVal V] [ByteRepr V] [ZeroBytes V] {t : go.GoType} [TypeRepr t V]
    [TypeBytes t V] :
    ⟦SizeOf t, #()⟧ ⤳ (Val #(W64 (ByteRepr.size V)))

attribute [instance] BytesSemantics.int_bytes BytesSemantics.int64_bytes
  BytesSemantics.int32_bytes BytesSemantics.int16_bytes BytesSemantics.int8_bytes
  BytesSemantics.uint_bytes BytesSemantics.uint64_bytes BytesSemantics.uint32_bytes
  BytesSemantics.uint16_bytes BytesSemantics.uint8_bytes BytesSemantics.uintptr_bytes
  BytesSemantics.float64_bytes BytesSemantics.float32_bytes BytesSemantics.bool_bytes
  BytesSemantics.encode_step BytesSemantics.decode_step BytesSemantics.size_step

/-- The interface semantics over the byte memory (replaces `InterfaceSemantics`). -/
class InterfaceSemanticsB : Prop where
  [empty_methods : IfaceMethods (go.InterfaceType []) []]
  /-- the itab layout depends only on the method set -/
  itab_methods_underlying {t u : go.GoType} [t ↓u u] : itabMethods t = itabMethods u
  eface_repr (elems : List go.InterfaceElem) [IfaceMethods (go.InterfaceType elems) []] :
    TypeReprUnderlying (go.InterfaceType elems) GoEface
  iface_repr (elems : List go.InterfaceElem) {m : GoString} {ms : List GoString}
    [IfaceMethods (go.InterfaceType elems) (m :: ms)] :
    TypeReprUnderlying (go.InterfaceType elems) GoIface
  /-- An interface value is its two words. -/
  eface_unfold : IntoValUnfold GoEface (fun i => PairV #i.tptr #i.data)
  iface_unfold : IntoValUnfold GoIface (fun i => PairV #i.tab #i.data)
  eface_inj : IntoValInj GoEface
  iface_inj : IntoValInj GoIface
  is_comparable_interface (elems : List go.InterfaceElem) :
    ⟦CheckComparable (go.InterfaceType elems), #()⟧ ⤳[under] #()
  /-- `==` on interface values (`runtime.nilinterequal`, `interequal`): the type
  words (type descriptors or itabs) are compared, and equal ones go to
  `efaceeq`/`ifaceeq`. -/
  go_eq_interface (elems : List go.InterfaceElem) (a d b e : w64) :
    ⟦GoOp GoEquals (go.InterfaceType elems), PairV (PairV #a #d) (PairV #b #e)⟧ ⤳[under]
    (if a = b then
       App (Val (if (itabMethods (go.InterfaceType elems)).isEmpty then efaceEq else ifaceEq))
         (Val (PairV #a (PairV #d #e)))
     else Val #false)
  /-- `I(v)`. From an interface to an empty interface it keeps the dynamic type
(the identity from the same type, as `convert_same` says); `nil` is `(0, 0)`; a
concrete value is boxed, with its type descriptor or its static itab. From an
interface to a non-empty interface (`NoGetitab` fails) there is no step: it
needs the itab for the target type from `runtime.getitab`, not modelled, even
between two interface types with the same underlying type (Go recomputes the
itab: an interface of type `I` has an itab for `I`); from the same non-empty
interface type it is `convert_same`. -/
  convert_to_interface (v : val) {from_ funder to : go.GoType} {elems : List go.InterfaceElem}
    [from_ ↓u funder] [to ≤u go.InterfaceType elems] [NoGetitab funder to] :
    ⟦Convert from_ to, v⟧ ⤳
    (if isInterfaceType funder then
       (if from_ = to then Val v else App (Val (convToEface from_)) (Val v))
     else if isUntypedNil funder then
       (if (itabMethods to).isEmpty then Val #(zero_val GoEface) else Val #(zero_val GoIface))
     else if (itabMethods to).isEmpty then
       App (Val (LamV "d" (Pair (Val #(typeAddr from_)) (Var "d"))))
         (App (Val (boxBytes from_)) (Val v))
     else
       App (Val (LamV "d" (Pair (Val #(itabAddr from_ to)) (Var "d"))))
         (App (Val (boxBytes from_)) (Val v)))
  /-- `(*I2)(p)` for `p : *I1`, where `I1` and `I2` have the same underlying
  interface type (the Go spec's conversion between unnamed pointer types whose
  base types have identical underlying types): the pointer is kept, so the value
  at `p`, read as an `I2`, still has `I1`'s itab; `.(T)` on it compares that
  itab with `go:itab.T,I2` and panics, as in gc (where this contradicts the
  spec's "the dynamic type of x is identical to T"). -/
  convert_pointer_interface {t1 t2 : go.GoType} {elems : List go.InterfaceElem}
    [t1 ↓u go.InterfaceType elems] [t2 ↓u go.InterfaceType elems] (l : Loc) :
    ⟦Convert (go.PointerType t1) (go.PointerType t2), #l⟧ ⤳[under] #l
  /-- `x.(T)` for `x` of the interface type `from_`: to a concrete type, compare
  the type word or itab pointer (`typeAssertConcrete`); to an empty interface,
  the value as an empty interface; to a non-empty interface (`NoGetitab` fails)
  there is no step (`runtime.getitab`, not modelled). -/
  type_assert_step {from_ t tunder : go.GoType} {selems : List go.InterfaceElem}
    [from_ ≤u go.InterfaceType selems] [t ↓u tunder] [NoGetitab tunder t] (v : val) :
    ⟦TypeAssert from_ t, v⟧ ⤳
    (if isInterfaceType tunder then App (Val (typeAssertEface from_)) (Val v)
     else App (Val (typeAssertConcrete from_ t)) (Val v))
  /-- `x, ok := x.(T)` (and each case of a type switch): as `type_assert_step`,
  with the zero value `z` of `T` and `false` when the assertion fails. -/
  type_assert2_step {from_ t tunder : go.GoType} {selems : List go.InterfaceElem}
    [from_ ≤u go.InterfaceType selems] [t ↓u tunder] [NoGetitab tunder t] {z : val}
    [⟦GoZeroVal t, #()⟧ ⤳ Val z] (v : val) :
    ⟦TypeAssert2 from_ t, v⟧ ⤳
    (if isInterfaceType tunder then App (Val (typeAssert2Eface from_)) (Val v)
     else App (Val (typeAssert2Concrete from_ t z)) (Val v))
  /-- `i.m`: the method's code from the itab, applied to the data word; a nil
  interface is a run-time panic -/
  method_interface (m : GoString) {t : go.GoType} {elems : List go.InterfaceElem}
    [t ≤u go.InterfaceType elems] (i : GoIface) :
    ⟦MethodResolve t m, #i⟧ ⤳
    (if i.tab = 0 then Panic "nil interface"
     else App (FuncLoad (App (Val (itabFun ((itabMethods t).idxOf m))) (Val #i.tab)))
       (Val #i.data))

/- The steps of the interface instructions are not instances: program proofs
use the specs of `Golang/Theory/StaticIface.lean`, which hide the representation;
that file makes them local instances. -/
attribute [instance] InterfaceSemanticsB.empty_methods InterfaceSemanticsB.eface_repr
  InterfaceSemanticsB.iface_repr InterfaceSemanticsB.eface_unfold
  InterfaceSemanticsB.iface_unfold InterfaceSemanticsB.eface_inj InterfaceSemanticsB.iface_inj
  InterfaceSemanticsB.is_comparable_interface

end semantics

/-- The Go semantics with interfaces over the byte memory (`go.Semantics` with
`InterfaceSemanticsB` in place of `InterfaceSemantics`). -/
class SemanticsB [FfiSyntax] [GoLocalContext] [GoGlobalContext] where
  [sem_fn : GoSemanticsFunctions]
  [symbols : StaticSymbols]
  [core_sem : go.PreSemantics]
  [bytes_sem : go.BytesSemantics]
  [interface_sem : go.InterfaceSemanticsB]
  [chan_sem : go.ChanSemantics]
  [string_sem : go.StringSemantics]

attribute [instance] SemanticsB.sem_fn SemanticsB.symbols SemanticsB.core_sem
  SemanticsB.bytes_sem SemanticsB.interface_sem SemanticsB.chan_sem SemanticsB.string_sem

end go

end Perennial
