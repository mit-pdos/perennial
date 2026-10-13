/-
Go's predeclared identifiers and the
semantics of the predeclared types.

Word operations: add/sub/mul are `+ - *`, unsigned div/mod are `/ %`, signed
div/mod are `BitVec.sdiv/srem` (truncated: Go's `/` rounds towards zero and `%`
has the sign of the dividend; `MinInt / -1` wraps to `MinInt`, remainder 0),
and/or/xor are `&&& ||| ^^^`, left and logical right shift are `<<< >>>`,
arithmetic right shift is `BitVec.sshiftRight'`, negation is `-` and bitwise
not is `~~~`.

Integer division and remainder by zero are a run-time panic in Go (spec,
"Integer operators"): `Panic "integer divide by zero"` (stuck, like the other
run-time panics of the model). The condition is `uint.Z v2 = 0` (`sint.Z v2 = 0`
at the signed types), the form arithmetic facts about the divisor take.

Shifts (spec, "Operators" and "Integer operators"): `x << y` and `x >> y` are
`GoShift o t ct` with `t` the type of `x` and `ct` that of `y`, which need not be
the same. The count is normalized by a rule of the count's type (`shift_count_int8`,
..., `shift_count_untyped_int`) to the same shift at count type `uint64`, which
the shifted type's rules (`shiftl_uint8`, ...) take: a signed count is
`Panic "negative shift amount"` when negative, and otherwise (like an unsigned
one) its value. It is never truncated to the width of `x`: a count of at least
that width shifts every bit out (`<<<`, `>>>` give `0`, `sshiftRight'` the sign).
-/
module

public import Perennial.Golang.Defn.PostLang
public import Perennial.Golang.Defn.Layout

@[expose] public section

namespace Perennial

namespace error
abbrev _root_.Perennial.GoError [FfiSyntax] : Type := GoInterface
end error

section helpers
variable [FfiSyntax] [GoGlobalContext]

/-- `min(x, y)` as `x < y`'s choice, for the types where that is Go's `min` (`MinByLt`);
floats have their own (`minFloat.impl`). -/
def min.impl (t : go.GoType) (n : Nat) : val :=
  match n with
  | 2 => λ: "x" "y", if: ("x" <⟨t⟩ "y") then "x" else "y"
  | _ => LitV LitPoison

/-- `max(x, y)` as `x > y`'s choice (`MinByLt`). -/
def max.impl (t : go.GoType) (n : Nat) : val :=
  match n with
  | 2 => λ: "x" "y", if: "x" >⟨t⟩ "y" then "x" else "y"
  | _ => LitV LitPoison

/-- `panic(v)` is the outcome `("panic", v)` of the exception monad (`panicVal v`,
`Defn/Exception.lean`), which ends the function body like a `return:`; the
function's deferred functions then run and may `recover()` it (`Defn/Defer.lean`).

`panic(nil)` is stuck: Go (since 1.21) replaces it by a run-time panic with a
`*runtime.PanicNilError`, which the model does not have, and a `nil` in the
`$panic` cell of `wrapDeferRecover` means "not panicking", so a `nil` panic
value would read as recovered. The argument is always an `interface{}` (Goose
converts it). -/
def panic.impl : val :=
  λ: "v",
    if: "v" =⟨go.InterfaceType []⟩ #interface.nil then Panic "panic called with nil argument"
    else (#"panic", Var "v")

end helpers

namespace «unsafe»
def Pointer : go.GoType := go.Named go!"unsafe.Pointer" []
/-- `unsafe.Add(ptr, len)`: `ptr` moved `len` bytes (Goose also emits it for
`unsafe.Pointer(uintptr(ptr) + len)`, the same thing when it stays in `ptr`'s allocation). -/
def Add : GoString := go!"unsafe.Add"
/-- `unsafe.Slice(ptr, len)`: the slice of `len` elements from `ptr`. -/
def Slice : GoString := go!"unsafe.Slice"
/-- `(*[n]T)(ptr)[lo:hi:max]`, which goose emits as one operation (not a conversion
followed by a slice): only the `max` elements are accessed, not the whole array. -/
def ArraySlice : GoString := go!"unsafe.ArraySlice"

class Semantics [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  go_zero_val_Pointer : go.TypeReprUnderlying Pointer Loc
  go_eq_Pointer : go.IsStrictlyComparable Pointer Loc
  underlying_pointer : unsafe.Pointer ↓u unsafe.Pointer
  convert_pointer_to_unsafe (elem : go.GoType) (l : Loc) :
    ⟦Convert (go.PointerType elem) unsafe.Pointer, #l⟧ ⤳[under] #l

attribute [instance] Semantics.go_zero_val_Pointer Semantics.go_eq_Pointer
  Semantics.underlying_pointer Semantics.convert_pointer_to_unsafe
export Semantics (go_zero_val_Pointer go_eq_Pointer underlying_pointer convert_pointer_to_unsafe)
end «unsafe»

namespace any
abbrev _root_.Perennial.GoAny [FfiSyntax] : Type := GoInterface
end any

namespace go

/-! Functions from https://go.dev/ref/spec#Predeclared_identifiers -/
def append : GoString := go!"append"
def cap : GoString := go!"cap"
def clear : GoString := go!"clear"
def close : GoString := go!"close"
def complex : GoString := go!"close"
def copy : GoString := go!"copy"
def delete : GoString := go!"delete"
def imag : GoString := go!"imag"
def len : GoString := go!"len"
def make3 : GoString := go!"make3"
def make2 : GoString := go!"make2"
def make1 : GoString := go!"make1"
def max : GoString := go!"max"
def min : GoString := go!"min"
-- Instead of `new`, the model uses `GoAlloc`
def panic : GoString := go!"panic"
def print : GoString := go!"print"
def println : GoString := go!"println"
def real : GoString := go!"real"
def recover : GoString := go!"recover"

/-! Types from https://go.dev/ref/spec#Predeclared_identifiers -/
@[reducible] def any : go.GoType := go.InterfaceType []
--  bool is declared in PreLang.
--  byte is aliased below
--  comparable is omitted: it's only used in type constraints and does not
--  affect executions
def complex64 : go.GoType := go.Named go!"complex64" []
def complex128 : go.GoType := go.Named go!"complex128" []
--  error is aliased below, after defining string.
def float32 : go.GoType := go.Named go!"float32" []
def float64 : go.GoType := go.Named go!"float64" []
def int : go.GoType := go.Named go!"int" []
def int8 : go.GoType := go.Named go!"int8" []
def int16 : go.GoType := go.Named go!"int16" []
def int32 : go.GoType := go.Named go!"int32" []
def int64 : go.GoType := go.Named go!"int64" []
abbrev rune : go.GoType := int32
def string : go.GoType := go.Named go!"string" []
/-- `error` is reducible (like `any`), so that
typeclass search sees that it is an interface type (`go.error ↓u go.InterfaceType _`,
`IntoValTyped GoInterface go.error`, ...). -/
@[reducible] def error : go.GoType :=
  go.InterfaceType [go.MethodElem go!"Error" (go.Signature [] false [go.string])]

def uint : go.GoType := go.Named go!"uint" []
def uint8 : go.GoType := go.Named go!"uint8" []
abbrev byte : go.GoType := uint8
def uint16 : go.GoType := go.Named go!"uint16" []
def uint32 : go.GoType := go.Named go!"uint32" []
def uint64 : go.GoType := go.Named go!"uint64" []
/-- 64-bit unsigned integer; see `go.UintptrSemantics`. -/
def uintptr : go.GoType := go.Named go!"uintptr" []

-- Untyped types
def untypedInt : go.GoType := go.Named go!"untyped int" []
abbrev untypedString : go.GoType := go.string
abbrev untypedBool : go.GoType := go.bool
def untypedNil : go.GoType := go.Named go!"untyped nil" []
def untypedFloat : go.GoType := go.Named go!"untyped float" []
abbrev untypedRune : go.GoType := untypedInt

def prophId : go.GoType := go.Named go!"proph id" []

section reinterpretable
variable [FfiSyntax] [GoSemanticsFunctions]

mutual
/-- `Reinterpretable t`: memory reached through an `unsafe.Pointer` may be accessed as a `t`
(`(*t)(p)`, `unsafe.Slice`, `UnsafeSemantics`): numbers, and arrays and structs of them
without padding (`ReinterpretableFields`, `StructSize`). Such a value is its bytes, in the model as
in Go, so reading or writing it over any bytes means what it means in Go; `UnsafeSemantics`
also checks that the memory accessed is bytes (`CheckBytes`). Not the other types, whose
model representation is not Go's bytes (a pointer, a string, an interface, a map, a
channel, a function or a `bool` is one value in its cells; padding is no value). -/
inductive Reinterpretable : go.GoType → Prop
  | uint8 : Reinterpretable go.uint8
  | uint16 : Reinterpretable go.uint16
  | uint32 : Reinterpretable go.uint32
  | uint64 : Reinterpretable go.uint64
  | uint : Reinterpretable go.uint
  | uintptr : Reinterpretable go.uintptr
  | int8 : Reinterpretable go.int8
  | int16 : Reinterpretable go.int16
  | int32 : Reinterpretable go.int32
  | int64 : Reinterpretable go.int64
  | int : Reinterpretable go.int
  | float32 : Reinterpretable go.float32
  | float64 : Reinterpretable go.float64
  | array (n : Int) (t : go.GoType) (h : Reinterpretable t) :
      Reinterpretable (go.ArrayType n t)
  | struct (fds fds' : List go.field_decl) (heq : EqualsUnfold fds fds') (sum : Int)
      (h : ReinterpretableFields fds' sum) (V : Type) [ZeroVal V]
      (hr : TypeRepr (go.StructType fds) V) (hsz : typeSize V = sum) :
      Reinterpretable (go.StructType fds)
  | named (t u : go.GoType) (hu : IsUnderlying t u) (h : Reinterpretable u) : Reinterpretable t

/-- Every field of the list is `Reinterpretable`, and their sizes add up to `sum`: a struct of
them whose size is `sum` has no padding. (A blank field is zero-size: goose refuses others.) -/
inductive ReinterpretableFields : List go.field_decl → outParam Int → Prop
  | nil : ReinterpretableFields [] 0
  | field (n : GoString) (t : go.GoType) (fs : List go.field_decl) (sum : Int)
      (h : Reinterpretable t) (F : Type) [ZeroVal F] (hr : TypeRepr t F)
      (hs : ReinterpretableFields fs sum) :
      ReinterpretableFields (go.FieldDecl n t :: fs) (typeSize F + sum)
  | embedded (n : GoString) (t : go.GoType) (fs : List go.field_decl) (sum : Int)
      (h : Reinterpretable t) (F : Type) [ZeroVal F] (hr : TypeRepr t F)
      (hs : ReinterpretableFields fs sum) :
      ReinterpretableFields (go.EmbeddedField n t :: fs) (typeSize F + sum)
end

attribute [class] Reinterpretable ReinterpretableFields
attribute [instance] Reinterpretable.uint8 Reinterpretable.uint16 Reinterpretable.uint32
  Reinterpretable.uint64 Reinterpretable.uint Reinterpretable.uintptr Reinterpretable.int8
  Reinterpretable.int16 Reinterpretable.int32 Reinterpretable.int64 Reinterpretable.int
  Reinterpretable.float32 Reinterpretable.float64
  ReinterpretableFields.nil

/-- The size of a struct type, for `Reinterpretable`'s premise that it is its fields'
sizes' sum; proofs give it per struct. -/
class StructSize (t : go.GoType) (sum : Int) : Prop where
  size : ∀ (V : Type) [ZeroVal V], TypeRepr t V → typeSize V = sum

instance (n : Int) (t : go.GoType) [h : Reinterpretable t] :
    Reinterpretable (go.ArrayType n t) := .array n t h
instance (fds fds' : List go.field_decl) [heq : EqualsUnfold fds fds'] {sum : Int}
    [h : ReinterpretableFields fds' sum] {V : Type} [ZeroVal V] [hr : TypeRepr (go.StructType fds) V]
    [hsz : StructSize (go.StructType fds) sum] :
    Reinterpretable (go.StructType fds) :=
  .struct fds fds' heq sum h V hr (hsz.size V hr)
instance (priority := low) (t u : go.GoType) [hu : IsUnderlying t u] [h : Reinterpretable u] :
    Reinterpretable t := .named t u hu h
instance (n : GoString) (t : go.GoType) (fs : List go.field_decl) {sum : Int} [h : Reinterpretable t]
    {F : Type} [ZeroVal F] [hr : TypeRepr t F] [hs : ReinterpretableFields fs sum] :
    ReinterpretableFields (go.FieldDecl n t :: fs) (typeSize F + sum) := .field n t fs sum h F hr hs
instance (n : GoString) (t : go.GoType) (fs : List go.field_decl) {sum : Int} [h : Reinterpretable t]
    {F : Type} [ZeroVal F] [hr : TypeRepr t F] [hs : ReinterpretableFields fs sum] :
    ReinterpretableFields (go.EmbeddedField n t :: fs) (typeSize F + sum) :=
  .embedded n t fs sum h F hr hs

end reinterpretable

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

/-- How the values of a predeclared type occupy memory (`Encoding`), with gc/amd64's sizes
(`Layout.lean`): the integers, and the floats by their bits, are their little-endian bytes;
a `bool` (one cell), a `string` (16), an `unsafe.Pointer` (8) or a prophecy id (8) is one
value followed by tails, which nothing reads as bytes (Go would give the bytes of its
representation: the model is less defined there). -/
class inductive PredeclaredEncoding : go.GoType → outParam Encoding → Prop
  | enc_uint8 : PredeclaredEncoding go.uint8 (.word 1)
  | enc_int8 : PredeclaredEncoding go.int8 (.word 1)
  | enc_uint16 : PredeclaredEncoding go.uint16 (.word 2)
  | enc_int16 : PredeclaredEncoding go.int16 (.word 2)
  | enc_uint32 : PredeclaredEncoding go.uint32 (.word 4)
  | enc_int32 : PredeclaredEncoding go.int32 (.word 4)
  | enc_float32 : PredeclaredEncoding go.float32 (.word 4)
  | enc_uint64 : PredeclaredEncoding go.uint64 (.word 8)
  | enc_int64 : PredeclaredEncoding go.int64 (.word 8)
  | enc_uint : PredeclaredEncoding go.uint (.word 8)
  | enc_int : PredeclaredEncoding go.int (.word 8)
  | enc_uintptr : PredeclaredEncoding go.uintptr (.word 8)
  | enc_float64 : PredeclaredEncoding go.float64 (.word 8)
  | enc_bool : PredeclaredEncoding go.bool (.cell 1)
  | enc_string : PredeclaredEncoding go.string (.cell 16)
  | enc_Pointer : PredeclaredEncoding unsafe.Pointer (.cell 8)
  | enc_proph_id : PredeclaredEncoding go.prophId (.cell 8)

attribute [instance] PredeclaredEncoding.enc_uint8 PredeclaredEncoding.enc_int8
  PredeclaredEncoding.enc_uint16 PredeclaredEncoding.enc_int16 PredeclaredEncoding.enc_uint32
  PredeclaredEncoding.enc_int32 PredeclaredEncoding.enc_float32 PredeclaredEncoding.enc_uint64
  PredeclaredEncoding.enc_int64 PredeclaredEncoding.enc_uint PredeclaredEncoding.enc_int
  PredeclaredEncoding.enc_uintptr PredeclaredEncoding.enc_float64 PredeclaredEncoding.enc_bool
  PredeclaredEncoding.enc_string PredeclaredEncoding.enc_Pointer PredeclaredEncoding.enc_proph_id

/-- These are the predeclareds that are modeled as taking up a single heap
location. A `class` so that the `[IsPredeclared u]`
premises below are found by typeclass search. -/
class inductive IsPredeclared : go.GoType → Prop
  | isPredeclared_uint : IsPredeclared go.uint
  | isPredeclared_uint8 : IsPredeclared go.uint8
  | isPredeclared_uint16 : IsPredeclared go.uint16
  | isPredeclared_uint32 : IsPredeclared go.uint32
  | isPredeclared_uint64 : IsPredeclared go.uint64
  | isPredeclared_uintptr : IsPredeclared go.uintptr
  | isPredeclared_int : IsPredeclared go.int
  | isPredeclared_int8 : IsPredeclared go.int8
  | isPredeclared_int16 : IsPredeclared go.int16
  | isPredeclared_int32 : IsPredeclared go.int32
  | isPredeclared_int64 : IsPredeclared go.int64
  | isPredeclared_string : IsPredeclared go.string
  | isPredeclared_bool : IsPredeclared go.bool
  | isPredeclared_Pointer : IsPredeclared unsafe.Pointer
  | isPredeclared_float32 : IsPredeclared go.float32
  | isPredeclared_float64 : IsPredeclared go.float64
  -- Treating this like a predeclared too.
  | isPredeclared_proph_id : IsPredeclared go.prophId

attribute [instance] IsPredeclared.isPredeclared_uint IsPredeclared.isPredeclared_uint8
  IsPredeclared.isPredeclared_uint16 IsPredeclared.isPredeclared_uint32
  IsPredeclared.isPredeclared_uint64 IsPredeclared.isPredeclared_uintptr
  IsPredeclared.isPredeclared_int
  IsPredeclared.isPredeclared_int8 IsPredeclared.isPredeclared_int16
  IsPredeclared.isPredeclared_int32 IsPredeclared.isPredeclared_int64
  IsPredeclared.isPredeclared_string IsPredeclared.isPredeclared_bool
  IsPredeclared.isPredeclared_Pointer IsPredeclared.isPredeclared_float32
  IsPredeclared.isPredeclared_float64 IsPredeclared.isPredeclared_proph_id
export IsPredeclared (isPredeclared_uint isPredeclared_uint8 isPredeclared_uint16
  isPredeclared_uint32 isPredeclared_uint64 isPredeclared_uintptr isPredeclared_int
  isPredeclared_int8
  isPredeclared_int16 isPredeclared_int32 isPredeclared_int64 isPredeclared_string
  isPredeclared_bool isPredeclared_Pointer isPredeclared_float32 isPredeclared_float64
  isPredeclared_proph_id)

class ProphIdSemantics [GoSemanticsFunctions] : Prop where
  underlying_proph_id : go.prophId ↓u go.prophId
  go_zero_val_proph_id : TypeReprUnderlying go.prophId Perennial.proph_id

attribute [instance] ProphIdSemantics.underlying_proph_id ProphIdSemantics.go_zero_val_proph_id
export ProphIdSemantics (underlying_proph_id go_zero_val_proph_id)

class UntypedIntSemantics [GoSemanticsFunctions] : Prop where
  underlying_untyped_int : go.untypedInt ↓u go.untypedInt
  neg_untyped_int (v : Int) : ⟦GoUnOp GoNeg go.untypedInt, #v⟧ ⤳ #(-v)

  convert_untyped_int_to_int (v : Int) : ⟦Convert go.untypedInt go.int, #v⟧ ⤳[under] #(W64 v)
  convert_untyped_int_to_int64 (v : Int) : ⟦Convert go.untypedInt go.int64, #v⟧ ⤳[under] #(W64 v)
  convert_untyped_int_to_int32 (v : Int) : ⟦Convert go.untypedInt go.int32, #v⟧ ⤳[under] #(W32 v)
  convert_untyped_int_to_int16 (v : Int) : ⟦Convert go.untypedInt go.int16, #v⟧ ⤳[under] #(W16 v)
  convert_untyped_int_to_int8 (v : Int) : ⟦Convert go.untypedInt go.int8, #v⟧ ⤳[under] #(W8 v)
  convert_untyped_int_to_uint (v : Int) : ⟦Convert go.untypedInt go.uint, #v⟧ ⤳[under] #(W64 v)
  convert_untyped_int_to_uint64 (v : Int) : ⟦Convert go.untypedInt go.uint64, #v⟧ ⤳[under] #(W64 v)
  convert_untyped_int_to_uint32 (v : Int) : ⟦Convert go.untypedInt go.uint32, #v⟧ ⤳[under] #(W32 v)
  convert_untyped_int_to_uint16 (v : Int) : ⟦Convert go.untypedInt go.uint16, #v⟧ ⤳[under] #(W16 v)
  convert_untyped_int_to_uint8 (v : Int) : ⟦Convert go.untypedInt go.uint8, #v⟧ ⤳[under] #(W8 v)
  /-- A constant count must be representable as a `uint` (spec, "Operators"): any other is a
  compile-time error, so this `Panic` is unreachable from a Go program. -/
  shift_count_untyped_int (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : Int) :
    ⟦GoShift o t go.untypedInt, (v1, #y)⟧ ⤳[under]
      (if 0 ≤ y ∧ y < 2 ^ 64 then GoShift o t go.uint64 (Pair v1 #(W64 y))
      else Panic "constant shift count out of range")

attribute [instance] UntypedIntSemantics.underlying_untyped_int UntypedIntSemantics.neg_untyped_int
  UntypedIntSemantics.convert_untyped_int_to_int UntypedIntSemantics.convert_untyped_int_to_int64
  UntypedIntSemantics.convert_untyped_int_to_int32 UntypedIntSemantics.convert_untyped_int_to_int16
  UntypedIntSemantics.convert_untyped_int_to_int8 UntypedIntSemantics.convert_untyped_int_to_uint
  UntypedIntSemantics.convert_untyped_int_to_uint64
  UntypedIntSemantics.convert_untyped_int_to_uint32
  UntypedIntSemantics.convert_untyped_int_to_uint16 UntypedIntSemantics.convert_untyped_int_to_uint8
  UntypedIntSemantics.shift_count_untyped_int
export UntypedIntSemantics (underlying_untyped_int neg_untyped_int convert_untyped_int_to_int
  convert_untyped_int_to_int64 convert_untyped_int_to_int32 convert_untyped_int_to_int16
  convert_untyped_int_to_int8 convert_untyped_int_to_uint convert_untyped_int_to_uint64
  convert_untyped_int_to_uint32 convert_untyped_int_to_uint16 convert_untyped_int_to_uint8
  shift_count_untyped_int)

class IntSemantics [GoSemanticsFunctions] : Prop where
  go_zero_val_int : TypeReprUnderlying go.int w64
  comparable_int : ⟦CheckComparable go.int, #()⟧ ⤳[under] #()
  underlying_int : go.int ↓u go.int
  go_eq_int : IsStrictlyComparable go.int w64
  le_int (v1 v2 : w64) : ⟦GoOp GoLe go.int, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v1 ≤ sint.Z v2))
  lt_int (v1 v2 : w64) : ⟦GoOp GoLt go.int, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v1 < sint.Z v2))
  ge_int (v1 v2 : w64) : ⟦GoOp GoGe go.int, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v2 ≤ sint.Z v1))
  gt_int (v1 v2 : w64) : ⟦GoOp GoGt go.int, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v2 < sint.Z v1))
  plus_int (v1 v2 : w64) : ⟦GoOp GoPlus go.int, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_int (v1 v2 : w64) : ⟦GoOp GoSub go.int, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_int (v1 v2 : w64) : ⟦GoOp GoMul go.int, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_int (v1 v2 : w64) : ⟦GoOp GoDiv go.int, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.sdiv v1 v2))
  remainder_int (v1 v2 : w64) : ⟦GoOp GoRemainder go.int, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.srem v1 v2))
  and_int (v1 v2 : w64) : ⟦GoOp GoAnd go.int, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_int (v1 v2 : w64) : ⟦GoOp GoBitClear go.int, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_int (v1 v2 : w64) : ⟦GoOp GoOr go.int, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int (v1 v2 : w64) : ⟦GoOp GoXor go.int, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int (v1 v2 : w64) : ⟦GoShift GoShiftl go.int go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int (v1 v2 : w64) : ⟦GoShift GoShiftr go.int go.uint64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)
  shift_count_int (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w64) :
    ⟦GoShift o t go.int, (v1, #y)⟧ ⤳[under] (if sint.Z y < 0 then Panic "negative shift amount"
      else GoShift o t go.uint64 (Pair v1 #y))

  neg_int (v : w64) : ⟦GoUnOp GoNeg go.int, #v⟧ ⤳[under] #(-v)
  complement_int (v : w64) : ⟦GoUnOp GoComplement go.int, #v⟧ ⤳[under] #(~~~v)

  convert_int_to_int (v : w64) : ⟦Convert go.int go.int, #v⟧ ⤳[under] #v
  convert_int64_to_int (v : w64) : ⟦Convert go.int64 go.int, #v⟧ ⤳[under] #v
  convert_int32_to_int (v : w32) : ⟦Convert go.int32 go.int, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int16_to_int (v : w16) : ⟦Convert go.int16 go.int, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int8_to_int (v : w8) : ⟦Convert go.int8 go.int, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_uint_to_int (v : w64) : ⟦Convert go.uint go.int, #v⟧ ⤳[under] #v
  convert_uint64_to_int (v : w64) : ⟦Convert go.uint64 go.int, #v⟧ ⤳[under] #v
  convert_uint32_to_int (v : w32) : ⟦Convert go.uint32 go.int, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint16_to_int (v : w16) : ⟦Convert go.uint16 go.int, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint8_to_int (v : w8) : ⟦Convert go.uint8 go.int, #v⟧ ⤳[under] #(W64 (uint.Z v))

attribute [instance] IntSemantics.go_zero_val_int IntSemantics.comparable_int
  IntSemantics.underlying_int IntSemantics.go_eq_int IntSemantics.le_int IntSemantics.lt_int
  IntSemantics.ge_int IntSemantics.gt_int IntSemantics.plus_int IntSemantics.sub_int
  IntSemantics.mul_int IntSemantics.div_int IntSemantics.remainder_int IntSemantics.and_int IntSemantics.bitclear_int
  IntSemantics.or_int IntSemantics.xor_int IntSemantics.shiftl_int IntSemantics.shiftr_int
  IntSemantics.shift_count_int
  IntSemantics.neg_int IntSemantics.complement_int IntSemantics.convert_int_to_int
  IntSemantics.convert_int64_to_int IntSemantics.convert_int32_to_int
  IntSemantics.convert_int16_to_int IntSemantics.convert_int8_to_int
  IntSemantics.convert_uint_to_int IntSemantics.convert_uint64_to_int
  IntSemantics.convert_uint32_to_int IntSemantics.convert_uint16_to_int
  IntSemantics.convert_uint8_to_int
export IntSemantics (go_zero_val_int comparable_int underlying_int go_eq_int le_int lt_int ge_int
  gt_int plus_int sub_int mul_int div_int remainder_int and_int bitclear_int or_int xor_int shiftl_int shiftr_int shift_count_int
  neg_int complement_int convert_int_to_int convert_int64_to_int convert_int32_to_int
  convert_int16_to_int convert_int8_to_int convert_uint_to_int convert_uint64_to_int
  convert_uint32_to_int convert_uint16_to_int convert_uint8_to_int)

class Int64Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_int64 : TypeReprUnderlying go.int64 w64
  comparable_int64 : ⟦CheckComparable go.int64, #()⟧ ⤳[under] #()
  underlying_int64 : go.int64 ↓u go.int64
  go_eq_int64 : IsStrictlyComparable go.int64 w64
  le_int64 (v1 v2 : w64) : ⟦GoOp GoLe go.int64, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 ≤ sint.Z v2))
  lt_int64 (v1 v2 : w64) : ⟦GoOp GoLt go.int64, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 < sint.Z v2))
  ge_int64 (v1 v2 : w64) : ⟦GoOp GoGe go.int64, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 ≤ sint.Z v1))
  gt_int64 (v1 v2 : w64) : ⟦GoOp GoGt go.int64, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 < sint.Z v1))
  plus_int64 (v1 v2 : w64) : ⟦GoOp GoPlus go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_int64 (v1 v2 : w64) : ⟦GoOp GoSub go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_int64 (v1 v2 : w64) : ⟦GoOp GoMul go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_int64 (v1 v2 : w64) : ⟦GoOp GoDiv go.int64, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.sdiv v1 v2))
  remainder_int64 (v1 v2 : w64) : ⟦GoOp GoRemainder go.int64, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.srem v1 v2))
  and_int64 (v1 v2 : w64) : ⟦GoOp GoAnd go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_int64 (v1 v2 : w64) : ⟦GoOp GoBitClear go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_int64 (v1 v2 : w64) : ⟦GoOp GoOr go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int64 (v1 v2 : w64) : ⟦GoOp GoXor go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int64 (v1 v2 : w64) : ⟦GoShift GoShiftl go.int64 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_int64 (v1 v2 : w64) : ⟦GoShift GoShiftr go.int64 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)
  shift_count_int64 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w64) :
    ⟦GoShift o t go.int64, (v1, #y)⟧ ⤳[under] (if sint.Z y < 0 then Panic "negative shift amount"
      else GoShift o t go.uint64 (Pair v1 #y))

  neg_int64 (v : w64) : ⟦GoUnOp GoNeg go.int64, #v⟧ ⤳[under] #(-v)
  complement_int64 (v : w64) : ⟦GoUnOp GoComplement go.int64, #v⟧ ⤳[under] #(~~~v)

  convert_int_to_int64 (v : w64) : ⟦Convert go.int go.int64, #v⟧ ⤳[under] #v
  convert_int64_to_int64 (v : w64) : ⟦Convert go.int64 go.int64, #v⟧ ⤳[under] #v
  convert_int32_to_int64 (v : w32) : ⟦Convert go.int32 go.int64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int16_to_int64 (v : w16) : ⟦Convert go.int16 go.int64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int8_to_int64 (v : w8) : ⟦Convert go.int8 go.int64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_uint_to_int64 (v : w64) : ⟦Convert go.uint go.int64, #v⟧ ⤳[under] #v
  convert_uint64_to_int64 (v : w64) : ⟦Convert go.uint64 go.int64, #v⟧ ⤳[under] #v
  convert_uint32_to_int64 (v : w32) : ⟦Convert go.uint32 go.int64, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint16_to_int64 (v : w16) : ⟦Convert go.uint16 go.int64, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint8_to_int64 (v : w8) : ⟦Convert go.uint8 go.int64, #v⟧ ⤳[under] #(W64 (uint.Z v))

attribute [instance] Int64Semantics.go_zero_val_int64 Int64Semantics.comparable_int64
  Int64Semantics.underlying_int64 Int64Semantics.go_eq_int64 Int64Semantics.le_int64
  Int64Semantics.lt_int64 Int64Semantics.ge_int64 Int64Semantics.gt_int64 Int64Semantics.plus_int64
  Int64Semantics.sub_int64 Int64Semantics.mul_int64 Int64Semantics.div_int64
  Int64Semantics.remainder_int64 Int64Semantics.and_int64 Int64Semantics.bitclear_int64 Int64Semantics.or_int64
  Int64Semantics.xor_int64 Int64Semantics.shiftl_int64 Int64Semantics.shiftr_int64
  Int64Semantics.shift_count_int64
  Int64Semantics.neg_int64 Int64Semantics.complement_int64 Int64Semantics.convert_int_to_int64
  Int64Semantics.convert_int64_to_int64 Int64Semantics.convert_int32_to_int64
  Int64Semantics.convert_int16_to_int64 Int64Semantics.convert_int8_to_int64
  Int64Semantics.convert_uint_to_int64 Int64Semantics.convert_uint64_to_int64
  Int64Semantics.convert_uint32_to_int64 Int64Semantics.convert_uint16_to_int64
  Int64Semantics.convert_uint8_to_int64
export Int64Semantics (go_zero_val_int64 comparable_int64 underlying_int64 go_eq_int64 le_int64
  lt_int64 ge_int64 gt_int64 plus_int64 sub_int64 mul_int64 div_int64 remainder_int64 and_int64 bitclear_int64
  or_int64 xor_int64 shiftl_int64 shiftr_int64 shift_count_int64 neg_int64 complement_int64 convert_int_to_int64
  convert_int64_to_int64 convert_int32_to_int64 convert_int16_to_int64 convert_int8_to_int64
  convert_uint_to_int64 convert_uint64_to_int64 convert_uint32_to_int64 convert_uint16_to_int64
  convert_uint8_to_int64)

class Int32Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_int32 : TypeReprUnderlying go.int32 w32
  comparable_int32 : ⟦CheckComparable go.int32, #()⟧ ⤳[under] #()
  underlying_int32 : go.int32 ↓u go.int32
  go_eq_int32 : IsStrictlyComparable go.int32 w32
  le_int32 (v1 v2 : w32) : ⟦GoOp GoLe go.int32, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 ≤ sint.Z v2))
  lt_int32 (v1 v2 : w32) : ⟦GoOp GoLt go.int32, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 < sint.Z v2))
  ge_int32 (v1 v2 : w32) : ⟦GoOp GoGe go.int32, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 ≤ sint.Z v1))
  gt_int32 (v1 v2 : w32) : ⟦GoOp GoGt go.int32, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 < sint.Z v1))
  plus_int32 (v1 v2 : w32) : ⟦GoOp GoPlus go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_int32 (v1 v2 : w32) : ⟦GoOp GoSub go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_int32 (v1 v2 : w32) : ⟦GoOp GoMul go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_int32 (v1 v2 : w32) : ⟦GoOp GoDiv go.int32, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.sdiv v1 v2))
  remainder_int32 (v1 v2 : w32) : ⟦GoOp GoRemainder go.int32, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.srem v1 v2))
  and_int32 (v1 v2 : w32) : ⟦GoOp GoAnd go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_int32 (v1 v2 : w32) : ⟦GoOp GoBitClear go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_int32 (v1 v2 : w32) : ⟦GoOp GoOr go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int32 (v1 v2 : w32) : ⟦GoOp GoXor go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int32 (v1 : w32) (v2 : w64) : ⟦GoShift GoShiftl go.int32 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_int32 (v1 : w32) (v2 : w64) : ⟦GoShift GoShiftr go.int32 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)
  shift_count_int32 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w32) :
    ⟦GoShift o t go.int32, (v1, #y)⟧ ⤳[under] (if sint.Z y < 0 then Panic "negative shift amount"
      else GoShift o t go.uint64 (Pair v1 #(W64 (sint.Z y))))

  neg_int32 (v : w32) : ⟦GoUnOp GoNeg go.int32, #v⟧ ⤳[under] #(-v)
  complement_int32 (v : w32) : ⟦GoUnOp GoComplement go.int32, #v⟧ ⤳[under] #(~~~v)

  convert_int_to_int32 (v : w64) : ⟦Convert go.int go.int32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int64_to_int32 (v : w64) : ⟦Convert go.int64 go.int32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int32_to_int32 (v : w32) : ⟦Convert go.int32 go.int32, #v⟧ ⤳[under] #v
  convert_int16_to_int32 (v : w16) : ⟦Convert go.int16 go.int32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int8_to_int32 (v : w8) : ⟦Convert go.int8 go.int32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_uint_to_int32 (v : w64) : ⟦Convert go.uint go.int32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint64_to_int32 (v : w64) : ⟦Convert go.uint64 go.int32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint32_to_int32 (v : w32) : ⟦Convert go.uint32 go.int32, #v⟧ ⤳[under] #v
  convert_uint16_to_int32 (v : w16) : ⟦Convert go.uint16 go.int32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint8_to_int32 (v : w8) : ⟦Convert go.uint8 go.int32, #v⟧ ⤳[under] #(W32 (uint.Z v))

attribute [instance] Int32Semantics.go_zero_val_int32 Int32Semantics.comparable_int32
  Int32Semantics.underlying_int32 Int32Semantics.go_eq_int32 Int32Semantics.le_int32
  Int32Semantics.lt_int32 Int32Semantics.ge_int32 Int32Semantics.gt_int32 Int32Semantics.plus_int32
  Int32Semantics.sub_int32 Int32Semantics.mul_int32 Int32Semantics.div_int32
  Int32Semantics.remainder_int32 Int32Semantics.and_int32 Int32Semantics.bitclear_int32 Int32Semantics.or_int32
  Int32Semantics.xor_int32 Int32Semantics.shiftl_int32 Int32Semantics.shiftr_int32
  Int32Semantics.shift_count_int32
  Int32Semantics.neg_int32 Int32Semantics.complement_int32 Int32Semantics.convert_int_to_int32
  Int32Semantics.convert_int64_to_int32 Int32Semantics.convert_int32_to_int32
  Int32Semantics.convert_int16_to_int32 Int32Semantics.convert_int8_to_int32
  Int32Semantics.convert_uint_to_int32 Int32Semantics.convert_uint64_to_int32
  Int32Semantics.convert_uint32_to_int32 Int32Semantics.convert_uint16_to_int32
  Int32Semantics.convert_uint8_to_int32
export Int32Semantics (go_zero_val_int32 comparable_int32 underlying_int32 go_eq_int32 le_int32
  lt_int32 ge_int32 gt_int32 plus_int32 sub_int32 mul_int32 div_int32 remainder_int32 and_int32 bitclear_int32
  or_int32 xor_int32 shiftl_int32 shiftr_int32 shift_count_int32 neg_int32 complement_int32 convert_int_to_int32
  convert_int64_to_int32 convert_int32_to_int32 convert_int16_to_int32 convert_int8_to_int32
  convert_uint_to_int32 convert_uint64_to_int32 convert_uint32_to_int32 convert_uint16_to_int32
  convert_uint8_to_int32)

class Int16Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_int16 : TypeReprUnderlying go.int16 w16
  comparable_int16 : ⟦CheckComparable go.int16, #()⟧ ⤳[under] #()
  underlying_int16 : go.int16 ↓u go.int16
  go_eq_int16 : IsStrictlyComparable go.int16 w16
  le_int16 (v1 v2 : w16) : ⟦GoOp GoLe go.int16, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 ≤ sint.Z v2))
  lt_int16 (v1 v2 : w16) : ⟦GoOp GoLt go.int16, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v1 < sint.Z v2))
  ge_int16 (v1 v2 : w16) : ⟦GoOp GoGe go.int16, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 ≤ sint.Z v1))
  gt_int16 (v1 v2 : w16) : ⟦GoOp GoGt go.int16, (#v1, #v2)⟧
    ⤳[under] #(decide (sint.Z v2 < sint.Z v1))
  plus_int16 (v1 v2 : w16) : ⟦GoOp GoPlus go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_int16 (v1 v2 : w16) : ⟦GoOp GoSub go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_int16 (v1 v2 : w16) : ⟦GoOp GoMul go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_int16 (v1 v2 : w16) : ⟦GoOp GoDiv go.int16, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.sdiv v1 v2))
  remainder_int16 (v1 v2 : w16) : ⟦GoOp GoRemainder go.int16, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.srem v1 v2))
  and_int16 (v1 v2 : w16) : ⟦GoOp GoAnd go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_int16 (v1 v2 : w16) : ⟦GoOp GoBitClear go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_int16 (v1 v2 : w16) : ⟦GoOp GoOr go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int16 (v1 v2 : w16) : ⟦GoOp GoXor go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int16 (v1 : w16) (v2 : w64) : ⟦GoShift GoShiftl go.int16 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_int16 (v1 : w16) (v2 : w64) : ⟦GoShift GoShiftr go.int16 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)
  shift_count_int16 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w16) :
    ⟦GoShift o t go.int16, (v1, #y)⟧ ⤳[under] (if sint.Z y < 0 then Panic "negative shift amount"
      else GoShift o t go.uint64 (Pair v1 #(W64 (sint.Z y))))

  neg_int16 (v : w16) : ⟦GoUnOp GoNeg go.int16, #v⟧ ⤳[under] #(-v)
  complement_int16 (v : w16) : ⟦GoUnOp GoComplement go.int16, #v⟧ ⤳[under] #(~~~v)

  convert_int_to_int16 (v : w64) : ⟦Convert go.int go.int16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int64_to_int16 (v : w64) : ⟦Convert go.int64 go.int16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int32_to_int16 (v : w32) : ⟦Convert go.int32 go.int16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int16_to_int16 (v : w16) : ⟦Convert go.int16 go.int16, #v⟧ ⤳[under] #v
  convert_int8_to_int16 (v : w8) : ⟦Convert go.int8 go.int16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_uint_to_int16 (v : w64) : ⟦Convert go.uint go.int16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint64_to_int16 (v : w64) : ⟦Convert go.uint64 go.int16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint32_to_int16 (v : w32) : ⟦Convert go.uint32 go.int16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint16_to_int16 (v : w16) : ⟦Convert go.uint16 go.int16, #v⟧ ⤳[under] #v
  convert_uint8_to_int16 (v : w8) : ⟦Convert go.uint8 go.int16, #v⟧ ⤳[under] #(W16 (uint.Z v))

attribute [instance] Int16Semantics.go_zero_val_int16 Int16Semantics.comparable_int16
  Int16Semantics.underlying_int16 Int16Semantics.go_eq_int16 Int16Semantics.le_int16
  Int16Semantics.lt_int16 Int16Semantics.ge_int16 Int16Semantics.gt_int16 Int16Semantics.plus_int16
  Int16Semantics.sub_int16 Int16Semantics.mul_int16 Int16Semantics.div_int16
  Int16Semantics.remainder_int16 Int16Semantics.and_int16 Int16Semantics.bitclear_int16 Int16Semantics.or_int16
  Int16Semantics.xor_int16 Int16Semantics.shiftl_int16 Int16Semantics.shiftr_int16
  Int16Semantics.shift_count_int16
  Int16Semantics.neg_int16 Int16Semantics.complement_int16 Int16Semantics.convert_int_to_int16
  Int16Semantics.convert_int64_to_int16 Int16Semantics.convert_int32_to_int16
  Int16Semantics.convert_int16_to_int16 Int16Semantics.convert_int8_to_int16
  Int16Semantics.convert_uint_to_int16 Int16Semantics.convert_uint64_to_int16
  Int16Semantics.convert_uint32_to_int16 Int16Semantics.convert_uint16_to_int16
  Int16Semantics.convert_uint8_to_int16
export Int16Semantics (go_zero_val_int16 comparable_int16 underlying_int16 go_eq_int16 le_int16
  lt_int16 ge_int16 gt_int16 plus_int16 sub_int16 mul_int16 div_int16 remainder_int16 and_int16 bitclear_int16
  or_int16 xor_int16 shiftl_int16 shiftr_int16 shift_count_int16 neg_int16 complement_int16 convert_int_to_int16
  convert_int64_to_int16 convert_int32_to_int16 convert_int16_to_int16 convert_int8_to_int16
  convert_uint_to_int16 convert_uint64_to_int16 convert_uint32_to_int16 convert_uint16_to_int16
  convert_uint8_to_int16)

class Int8Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_int8 : TypeReprUnderlying go.int8 w8
  comparable_int8 : ⟦CheckComparable go.int8, #()⟧ ⤳[under] #()
  underlying_int8 : go.int8 ↓u go.int8
  go_eq_int8 : IsStrictlyComparable go.int8 w8
  le_int8 (v1 v2 : w8) : ⟦GoOp GoLe go.int8, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v1 ≤ sint.Z v2))
  lt_int8 (v1 v2 : w8) : ⟦GoOp GoLt go.int8, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v1 < sint.Z v2))
  ge_int8 (v1 v2 : w8) : ⟦GoOp GoGe go.int8, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v2 ≤ sint.Z v1))
  gt_int8 (v1 v2 : w8) : ⟦GoOp GoGt go.int8, (#v1, #v2)⟧ ⤳[under] #(decide (sint.Z v2 < sint.Z v1))
  plus_int8 (v1 v2 : w8) : ⟦GoOp GoPlus go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_int8 (v1 v2 : w8) : ⟦GoOp GoSub go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_int8 (v1 v2 : w8) : ⟦GoOp GoMul go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_int8 (v1 v2 : w8) : ⟦GoOp GoDiv go.int8, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.sdiv v1 v2))
  remainder_int8 (v1 v2 : w8) : ⟦GoOp GoRemainder go.int8, (#v1, #v2)⟧
    ⤳[under] (if sint.Z v2 = 0 then Panic "integer divide by zero" else #(BitVec.srem v1 v2))
  and_int8 (v1 v2 : w8) : ⟦GoOp GoAnd go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_int8 (v1 v2 : w8) : ⟦GoOp GoBitClear go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_int8 (v1 v2 : w8) : ⟦GoOp GoOr go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int8 (v1 v2 : w8) : ⟦GoOp GoXor go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int8 (v1 : w8) (v2 : w64) : ⟦GoShift GoShiftl go.int8 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_int8 (v1 : w8) (v2 : w64) : ⟦GoShift GoShiftr go.int8 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)
  shift_count_int8 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w8) :
    ⟦GoShift o t go.int8, (v1, #y)⟧ ⤳[under] (if sint.Z y < 0 then Panic "negative shift amount"
      else GoShift o t go.uint64 (Pair v1 #(W64 (sint.Z y))))

  neg_int8 (v : w8) : ⟦GoUnOp GoNeg go.int8, #v⟧ ⤳[under] #(-v)
  complement_int8 (v : w8) : ⟦GoUnOp GoComplement go.int8, #v⟧ ⤳[under] #(~~~v)

  convert_int_to_int8 (v : w64) : ⟦Convert go.int go.int8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int64_to_int8 (v : w64) : ⟦Convert go.int64 go.int8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int32_to_int8 (v : w32) : ⟦Convert go.int32 go.int8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int16_to_int8 (v : w16) : ⟦Convert go.int16 go.int8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int8_to_int8 (v : w8) : ⟦Convert go.int8 go.int8, #v⟧ ⤳[under] #v
  convert_uint_to_int8 (v : w64) : ⟦Convert go.uint go.int8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint64_to_int8 (v : w64) : ⟦Convert go.uint64 go.int8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint32_to_int8 (v : w32) : ⟦Convert go.uint32 go.int8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint16_to_int8 (v : w16) : ⟦Convert go.uint16 go.int8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint8_to_int8 (v : w8) : ⟦Convert go.uint8 go.int8, #v⟧ ⤳[under] #v

attribute [instance] Int8Semantics.go_zero_val_int8 Int8Semantics.comparable_int8
  Int8Semantics.underlying_int8 Int8Semantics.go_eq_int8 Int8Semantics.le_int8 Int8Semantics.lt_int8
  Int8Semantics.ge_int8 Int8Semantics.gt_int8 Int8Semantics.plus_int8 Int8Semantics.sub_int8
  Int8Semantics.mul_int8 Int8Semantics.div_int8 Int8Semantics.remainder_int8 Int8Semantics.and_int8 Int8Semantics.bitclear_int8
  Int8Semantics.or_int8 Int8Semantics.xor_int8 Int8Semantics.shiftl_int8 Int8Semantics.shiftr_int8
  Int8Semantics.shift_count_int8
  Int8Semantics.neg_int8 Int8Semantics.complement_int8 Int8Semantics.convert_int_to_int8
  Int8Semantics.convert_int64_to_int8 Int8Semantics.convert_int32_to_int8
  Int8Semantics.convert_int16_to_int8 Int8Semantics.convert_int8_to_int8
  Int8Semantics.convert_uint_to_int8 Int8Semantics.convert_uint64_to_int8
  Int8Semantics.convert_uint32_to_int8 Int8Semantics.convert_uint16_to_int8
  Int8Semantics.convert_uint8_to_int8
export Int8Semantics (go_zero_val_int8 comparable_int8 underlying_int8 go_eq_int8 le_int8 lt_int8
  ge_int8 gt_int8 plus_int8 sub_int8 mul_int8 div_int8 remainder_int8 and_int8 bitclear_int8 or_int8 xor_int8
  shiftl_int8 shiftr_int8 shift_count_int8 neg_int8 complement_int8 convert_int_to_int8 convert_int64_to_int8
  convert_int32_to_int8 convert_int16_to_int8 convert_int8_to_int8 convert_uint_to_int8
  convert_uint64_to_int8 convert_uint32_to_int8 convert_uint16_to_int8 convert_uint8_to_int8)

class UintSemantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uint : TypeReprUnderlying go.uint w64
  comparable_uint : ⟦CheckComparable go.uint, #()⟧ ⤳[under] #()
  underlying_uint : go.uint ↓u go.uint
  go_eq_uint : IsStrictlyComparable go.uint w64
  le_uint (v1 v2 : w64) : ⟦GoOp GoLe go.uint, (#v1, #v2)⟧ ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uint (v1 v2 : w64) : ⟦GoOp GoLt go.uint, (#v1, #v2)⟧ ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uint (v1 v2 : w64) : ⟦GoOp GoGe go.uint, (#v1, #v2)⟧ ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uint (v1 v2 : w64) : ⟦GoOp GoGt go.uint, (#v1, #v2)⟧ ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uint (v1 v2 : w64) : ⟦GoOp GoPlus go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uint (v1 v2 : w64) : ⟦GoOp GoSub go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uint (v1 v2 : w64) : ⟦GoOp GoMul go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uint (v1 v2 : w64) : ⟦GoOp GoDiv go.uint, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uint (v1 v2 : w64) : ⟦GoOp GoRemainder go.uint, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uint (v1 v2 : w64) : ⟦GoOp GoAnd go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uint (v1 v2 : w64) : ⟦GoOp GoBitClear go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uint (v1 v2 : w64) : ⟦GoOp GoOr go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint (v1 v2 : w64) : ⟦GoOp GoXor go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint (v1 v2 : w64) : ⟦GoShift GoShiftl go.uint go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint (v1 v2 : w64) : ⟦GoShift GoShiftr go.uint go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)
  shift_count_uint (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w64) :
    ⟦GoShift o t go.uint, (v1, #y)⟧ ⤳[under] GoShift o t go.uint64 (Pair v1 #y)

  complement_uint (v : w64) : ⟦GoUnOp GoComplement go.uint, #v⟧ ⤳[under] #(~~~v)
  neg_uint (v : w64) : ⟦GoUnOp GoNeg go.uint, #v⟧ ⤳[under] #(-v)

  convert_int_to_uint (v : w64) : ⟦Convert go.int go.uint, #v⟧ ⤳[under] #v
  convert_int64_to_uint (v : w64) : ⟦Convert go.int64 go.uint, #v⟧ ⤳[under] #v
  convert_int32_to_uint (v : w32) : ⟦Convert go.int32 go.uint, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int16_to_uint (v : w16) : ⟦Convert go.int16 go.uint, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int8_to_uint (v : w8) : ⟦Convert go.int8 go.uint, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_uint_to_uint (v : w64) : ⟦Convert go.uint go.uint, #v⟧ ⤳[under] #v
  convert_uint64_to_uint (v : w64) : ⟦Convert go.uint64 go.uint, #v⟧ ⤳[under] #v
  convert_uint32_to_uint (v : w32) : ⟦Convert go.uint32 go.uint, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint16_to_uint (v : w16) : ⟦Convert go.uint16 go.uint, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint8_to_uint (v : w8) : ⟦Convert go.uint8 go.uint, #v⟧ ⤳[under] #(W64 (uint.Z v))

attribute [instance] UintSemantics.go_zero_val_uint UintSemantics.comparable_uint
  UintSemantics.underlying_uint UintSemantics.go_eq_uint UintSemantics.le_uint UintSemantics.lt_uint
  UintSemantics.ge_uint UintSemantics.gt_uint UintSemantics.plus_uint UintSemantics.sub_uint
  UintSemantics.mul_uint UintSemantics.div_uint UintSemantics.remainder_uint UintSemantics.and_uint UintSemantics.bitclear_uint
  UintSemantics.or_uint UintSemantics.xor_uint UintSemantics.shiftl_uint UintSemantics.shiftr_uint
  UintSemantics.shift_count_uint
  UintSemantics.complement_uint UintSemantics.neg_uint UintSemantics.convert_int_to_uint
  UintSemantics.convert_int64_to_uint UintSemantics.convert_int32_to_uint
  UintSemantics.convert_int16_to_uint UintSemantics.convert_int8_to_uint
  UintSemantics.convert_uint_to_uint UintSemantics.convert_uint64_to_uint
  UintSemantics.convert_uint32_to_uint UintSemantics.convert_uint16_to_uint
  UintSemantics.convert_uint8_to_uint
export UintSemantics (go_zero_val_uint comparable_uint underlying_uint go_eq_uint le_uint lt_uint
  ge_uint gt_uint plus_uint sub_uint mul_uint div_uint remainder_uint and_uint bitclear_uint or_uint xor_uint
  shiftl_uint shiftr_uint shift_count_uint complement_uint neg_uint convert_int_to_uint convert_int64_to_uint
  convert_int32_to_uint convert_int16_to_uint convert_int8_to_uint convert_uint_to_uint
  convert_uint64_to_uint convert_uint32_to_uint convert_uint16_to_uint convert_uint8_to_uint)

class Uint64Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uint64 : TypeReprUnderlying go.uint64 w64
  comparable_uint64 : ⟦CheckComparable go.uint64, #()⟧ ⤳[under] #()
  underlying_uint64 : go.uint64 ↓u go.uint64
  go_eq_uint64 : IsStrictlyComparable go.uint64 w64
  le_uint64 (v1 v2 : w64) : ⟦GoOp GoLe go.uint64, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uint64 (v1 v2 : w64) : ⟦GoOp GoLt go.uint64, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uint64 (v1 v2 : w64) : ⟦GoOp GoGe go.uint64, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uint64 (v1 v2 : w64) : ⟦GoOp GoGt go.uint64, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uint64 (v1 v2 : w64) : ⟦GoOp GoPlus go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uint64 (v1 v2 : w64) : ⟦GoOp GoSub go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uint64 (v1 v2 : w64) : ⟦GoOp GoMul go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uint64 (v1 v2 : w64) : ⟦GoOp GoDiv go.uint64, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uint64 (v1 v2 : w64) : ⟦GoOp GoRemainder go.uint64, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uint64 (v1 v2 : w64) : ⟦GoOp GoAnd go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uint64 (v1 v2 : w64) : ⟦GoOp GoBitClear go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uint64 (v1 v2 : w64) : ⟦GoOp GoOr go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint64 (v1 v2 : w64) : ⟦GoOp GoXor go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint64 (v1 v2 : w64) : ⟦GoShift GoShiftl go.uint64 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_uint64 (v1 v2 : w64) : ⟦GoShift GoShiftr go.uint64 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 >>> v2)

  complement_uint64 (v : w64) : ⟦GoUnOp GoComplement go.uint64, #v⟧ ⤳[under] #(~~~v)
  neg_uint64 (v : w64) : ⟦GoUnOp GoNeg go.uint64, #v⟧ ⤳[under] #(-v)

  convert_int_to_uint64 (v : w64) : ⟦Convert go.int go.uint64, #v⟧ ⤳[under] #v
  convert_int64_to_uint64 (v : w64) : ⟦Convert go.int64 go.uint64, #v⟧ ⤳[under] #v
  convert_int32_to_uint64 (v : w32) : ⟦Convert go.int32 go.uint64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int16_to_uint64 (v : w16) : ⟦Convert go.int16 go.uint64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int8_to_uint64 (v : w8) : ⟦Convert go.int8 go.uint64, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_uint_to_uint64 (v : w64) : ⟦Convert go.uint go.uint64, #v⟧ ⤳[under] #v
  convert_uint64_to_uint64 (v : w64) : ⟦Convert go.uint64 go.uint64, #v⟧ ⤳[under] #v
  convert_uint32_to_uint64 (v : w32) : ⟦Convert go.uint32 go.uint64, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint16_to_uint64 (v : w16) : ⟦Convert go.uint16 go.uint64, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uint8_to_uint64 (v : w8) : ⟦Convert go.uint8 go.uint64, #v⟧ ⤳[under] #(W64 (uint.Z v))

attribute [instance] Uint64Semantics.go_zero_val_uint64 Uint64Semantics.comparable_uint64
  Uint64Semantics.underlying_uint64 Uint64Semantics.go_eq_uint64 Uint64Semantics.le_uint64
  Uint64Semantics.lt_uint64 Uint64Semantics.ge_uint64 Uint64Semantics.gt_uint64
  Uint64Semantics.plus_uint64 Uint64Semantics.sub_uint64 Uint64Semantics.mul_uint64
  Uint64Semantics.div_uint64 Uint64Semantics.remainder_uint64 Uint64Semantics.and_uint64 Uint64Semantics.bitclear_uint64
  Uint64Semantics.or_uint64 Uint64Semantics.xor_uint64 Uint64Semantics.shiftl_uint64
  Uint64Semantics.shiftr_uint64 Uint64Semantics.complement_uint64 Uint64Semantics.neg_uint64
  Uint64Semantics.convert_int_to_uint64 Uint64Semantics.convert_int64_to_uint64
  Uint64Semantics.convert_int32_to_uint64 Uint64Semantics.convert_int16_to_uint64
  Uint64Semantics.convert_int8_to_uint64 Uint64Semantics.convert_uint_to_uint64
  Uint64Semantics.convert_uint64_to_uint64 Uint64Semantics.convert_uint32_to_uint64
  Uint64Semantics.convert_uint16_to_uint64 Uint64Semantics.convert_uint8_to_uint64
export Uint64Semantics (go_zero_val_uint64 comparable_uint64 underlying_uint64 go_eq_uint64
  le_uint64 lt_uint64 ge_uint64 gt_uint64 plus_uint64 sub_uint64 mul_uint64 div_uint64
  remainder_uint64 and_uint64 bitclear_uint64 or_uint64 xor_uint64 shiftl_uint64 shiftr_uint64 complement_uint64 neg_uint64
  convert_int_to_uint64 convert_int64_to_uint64 convert_int32_to_uint64 convert_int16_to_uint64
  convert_int8_to_uint64 convert_uint_to_uint64 convert_uint64_to_uint64 convert_uint32_to_uint64
  convert_uint16_to_uint64 convert_uint8_to_uint64)

class Uint32Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uint32 : TypeReprUnderlying go.uint32 w32
  comparable_uint32 : ⟦CheckComparable go.uint32, #()⟧ ⤳[under] #()
  underlying_uint32 : go.uint32 ↓u go.uint32
  go_eq_uint32 : IsStrictlyComparable go.uint32 w32
  le_uint32 (v1 v2 : w32) : ⟦GoOp GoLe go.uint32, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uint32 (v1 v2 : w32) : ⟦GoOp GoLt go.uint32, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uint32 (v1 v2 : w32) : ⟦GoOp GoGe go.uint32, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uint32 (v1 v2 : w32) : ⟦GoOp GoGt go.uint32, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uint32 (v1 v2 : w32) : ⟦GoOp GoPlus go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uint32 (v1 v2 : w32) : ⟦GoOp GoSub go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uint32 (v1 v2 : w32) : ⟦GoOp GoMul go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uint32 (v1 v2 : w32) : ⟦GoOp GoDiv go.uint32, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uint32 (v1 v2 : w32) : ⟦GoOp GoRemainder go.uint32, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uint32 (v1 v2 : w32) : ⟦GoOp GoAnd go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uint32 (v1 v2 : w32) : ⟦GoOp GoBitClear go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uint32 (v1 v2 : w32) : ⟦GoOp GoOr go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint32 (v1 v2 : w32) : ⟦GoOp GoXor go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint32 (v1 : w32) (v2 : w64) : ⟦GoShift GoShiftl go.uint32 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_uint32 (v1 : w32) (v2 : w64) : ⟦GoShift GoShiftr go.uint32 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 >>> v2)
  shift_count_uint32 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w32) :
    ⟦GoShift o t go.uint32, (v1, #y)⟧ ⤳[under] GoShift o t go.uint64 (Pair v1 #(W64 (uint.Z y)))

  complement_uint32 (v : w32) : ⟦GoUnOp GoComplement go.uint32, #v⟧ ⤳[under] #(~~~v)
  neg_uint32 (v : w32) : ⟦GoUnOp GoNeg go.uint32, #v⟧ ⤳[under] #(-v)

  convert_int_to_uint32 (v : w64) : ⟦Convert go.int go.uint32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int64_to_uint32 (v : w64) : ⟦Convert go.int64 go.uint32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int32_to_uint32 (v : w32) : ⟦Convert go.int32 go.uint32, #v⟧ ⤳[under] #v
  convert_int16_to_uint32 (v : w16) : ⟦Convert go.int16 go.uint32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_int8_to_uint32 (v : w8) : ⟦Convert go.int8 go.uint32, #v⟧ ⤳[under] #(W32 (sint.Z v))
  convert_uint_to_uint32 (v : w64) : ⟦Convert go.uint go.uint32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint64_to_uint32 (v : w64) : ⟦Convert go.uint64 go.uint32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint32_to_uint32 (v : w32) : ⟦Convert go.uint32 go.uint32, #v⟧ ⤳[under] #v
  convert_uint16_to_uint32 (v : w16) : ⟦Convert go.uint16 go.uint32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uint8_to_uint32 (v : w8) : ⟦Convert go.uint8 go.uint32, #v⟧ ⤳[under] #(W32 (uint.Z v))

attribute [instance] Uint32Semantics.go_zero_val_uint32 Uint32Semantics.comparable_uint32
  Uint32Semantics.underlying_uint32 Uint32Semantics.go_eq_uint32 Uint32Semantics.le_uint32
  Uint32Semantics.lt_uint32 Uint32Semantics.ge_uint32 Uint32Semantics.gt_uint32
  Uint32Semantics.plus_uint32 Uint32Semantics.sub_uint32 Uint32Semantics.mul_uint32
  Uint32Semantics.div_uint32 Uint32Semantics.remainder_uint32 Uint32Semantics.and_uint32 Uint32Semantics.bitclear_uint32
  Uint32Semantics.or_uint32 Uint32Semantics.xor_uint32 Uint32Semantics.shiftl_uint32
  Uint32Semantics.shiftr_uint32
  Uint32Semantics.shift_count_uint32 Uint32Semantics.complement_uint32 Uint32Semantics.neg_uint32
  Uint32Semantics.convert_int_to_uint32 Uint32Semantics.convert_int64_to_uint32
  Uint32Semantics.convert_int32_to_uint32 Uint32Semantics.convert_int16_to_uint32
  Uint32Semantics.convert_int8_to_uint32 Uint32Semantics.convert_uint_to_uint32
  Uint32Semantics.convert_uint64_to_uint32 Uint32Semantics.convert_uint32_to_uint32
  Uint32Semantics.convert_uint16_to_uint32 Uint32Semantics.convert_uint8_to_uint32
export Uint32Semantics (go_zero_val_uint32 comparable_uint32 underlying_uint32 go_eq_uint32
  le_uint32 lt_uint32 ge_uint32 gt_uint32 plus_uint32 sub_uint32 mul_uint32 div_uint32
  remainder_uint32 and_uint32 bitclear_uint32 or_uint32 xor_uint32 shiftl_uint32 shiftr_uint32 shift_count_uint32 complement_uint32 neg_uint32
  convert_int_to_uint32 convert_int64_to_uint32 convert_int32_to_uint32 convert_int16_to_uint32
  convert_int8_to_uint32 convert_uint_to_uint32 convert_uint64_to_uint32 convert_uint32_to_uint32
  convert_uint16_to_uint32 convert_uint8_to_uint32)

class Uint16Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uint16 : TypeReprUnderlying go.uint16 w16
  comparable_uint16 : ⟦CheckComparable go.uint16, #()⟧ ⤳[under] #()
  underlying_uint16 : go.uint16 ↓u go.uint16
  go_eq_uint16 : IsStrictlyComparable go.uint16 w16
  le_uint16 (v1 v2 : w16) : ⟦GoOp GoLe go.uint16, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uint16 (v1 v2 : w16) : ⟦GoOp GoLt go.uint16, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uint16 (v1 v2 : w16) : ⟦GoOp GoGe go.uint16, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uint16 (v1 v2 : w16) : ⟦GoOp GoGt go.uint16, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uint16 (v1 v2 : w16) : ⟦GoOp GoPlus go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uint16 (v1 v2 : w16) : ⟦GoOp GoSub go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uint16 (v1 v2 : w16) : ⟦GoOp GoMul go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uint16 (v1 v2 : w16) : ⟦GoOp GoDiv go.uint16, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uint16 (v1 v2 : w16) : ⟦GoOp GoRemainder go.uint16, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uint16 (v1 v2 : w16) : ⟦GoOp GoAnd go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uint16 (v1 v2 : w16) : ⟦GoOp GoBitClear go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uint16 (v1 v2 : w16) : ⟦GoOp GoOr go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint16 (v1 v2 : w16) : ⟦GoOp GoXor go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint16 (v1 : w16) (v2 : w64) : ⟦GoShift GoShiftl go.uint16 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_uint16 (v1 : w16) (v2 : w64) : ⟦GoShift GoShiftr go.uint16 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 >>> v2)
  shift_count_uint16 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w16) :
    ⟦GoShift o t go.uint16, (v1, #y)⟧ ⤳[under] GoShift o t go.uint64 (Pair v1 #(W64 (uint.Z y)))

  complement_uint16 (v : w16) : ⟦GoUnOp GoComplement go.uint16, #v⟧ ⤳[under] #(~~~v)
  neg_uint16 (v : w16) : ⟦GoUnOp GoNeg go.uint16, #v⟧ ⤳[under] #(-v)

  convert_int_to_uint16 (v : w64) : ⟦Convert go.int go.uint16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int64_to_uint16 (v : w64) : ⟦Convert go.int64 go.uint16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int32_to_uint16 (v : w32) : ⟦Convert go.int32 go.uint16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_int16_to_uint16 (v : w16) : ⟦Convert go.int16 go.uint16, #v⟧ ⤳[under] #v
  convert_int8_to_uint16 (v : w8) : ⟦Convert go.int8 go.uint16, #v⟧ ⤳[under] #(W16 (sint.Z v))
  convert_uint_to_uint16 (v : w64) : ⟦Convert go.uint go.uint16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint64_to_uint16 (v : w64) : ⟦Convert go.uint64 go.uint16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint32_to_uint16 (v : w32) : ⟦Convert go.uint32 go.uint16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uint16_to_uint16 (v : w16) : ⟦Convert go.uint16 go.uint16, #v⟧ ⤳[under] #v
  convert_uint8_to_uint16 (v : w8) : ⟦Convert go.uint8 go.uint16, #v⟧ ⤳[under] #(W16 (uint.Z v))

attribute [instance] Uint16Semantics.go_zero_val_uint16 Uint16Semantics.comparable_uint16
  Uint16Semantics.underlying_uint16 Uint16Semantics.go_eq_uint16 Uint16Semantics.le_uint16
  Uint16Semantics.lt_uint16 Uint16Semantics.ge_uint16 Uint16Semantics.gt_uint16
  Uint16Semantics.plus_uint16 Uint16Semantics.sub_uint16 Uint16Semantics.mul_uint16
  Uint16Semantics.div_uint16 Uint16Semantics.remainder_uint16 Uint16Semantics.and_uint16 Uint16Semantics.bitclear_uint16
  Uint16Semantics.or_uint16 Uint16Semantics.xor_uint16 Uint16Semantics.shiftl_uint16
  Uint16Semantics.shiftr_uint16
  Uint16Semantics.shift_count_uint16 Uint16Semantics.complement_uint16 Uint16Semantics.neg_uint16
  Uint16Semantics.convert_int_to_uint16 Uint16Semantics.convert_int64_to_uint16
  Uint16Semantics.convert_int32_to_uint16 Uint16Semantics.convert_int16_to_uint16
  Uint16Semantics.convert_int8_to_uint16 Uint16Semantics.convert_uint_to_uint16
  Uint16Semantics.convert_uint64_to_uint16 Uint16Semantics.convert_uint32_to_uint16
  Uint16Semantics.convert_uint16_to_uint16 Uint16Semantics.convert_uint8_to_uint16
export Uint16Semantics (go_zero_val_uint16 comparable_uint16 underlying_uint16 go_eq_uint16
  le_uint16 lt_uint16 ge_uint16 gt_uint16 plus_uint16 sub_uint16 mul_uint16 div_uint16
  remainder_uint16 and_uint16 bitclear_uint16 or_uint16 xor_uint16 shiftl_uint16 shiftr_uint16 shift_count_uint16 complement_uint16 neg_uint16
  convert_int_to_uint16 convert_int64_to_uint16 convert_int32_to_uint16 convert_int16_to_uint16
  convert_int8_to_uint16 convert_uint_to_uint16 convert_uint64_to_uint16 convert_uint32_to_uint16
  convert_uint16_to_uint16 convert_uint8_to_uint16)

class Uint8Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uint8 : TypeReprUnderlying go.uint8 w8
  comparable_uint8 : ⟦CheckComparable go.uint8, #()⟧ ⤳[under] #()
  underlying_uint8 : go.uint8 ↓u go.uint8
  go_eq_uint8 : IsStrictlyComparable go.uint8 w8
  le_uint8 (v1 v2 : w8) : ⟦GoOp GoLe go.uint8, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uint8 (v1 v2 : w8) : ⟦GoOp GoLt go.uint8, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uint8 (v1 v2 : w8) : ⟦GoOp GoGe go.uint8, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uint8 (v1 v2 : w8) : ⟦GoOp GoGt go.uint8, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uint8 (v1 v2 : w8) : ⟦GoOp GoPlus go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uint8 (v1 v2 : w8) : ⟦GoOp GoSub go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uint8 (v1 v2 : w8) : ⟦GoOp GoMul go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uint8 (v1 v2 : w8) : ⟦GoOp GoDiv go.uint8, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uint8 (v1 v2 : w8) : ⟦GoOp GoRemainder go.uint8, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uint8 (v1 v2 : w8) : ⟦GoOp GoAnd go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uint8 (v1 v2 : w8) : ⟦GoOp GoBitClear go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uint8 (v1 v2 : w8) : ⟦GoOp GoOr go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint8 (v1 v2 : w8) : ⟦GoOp GoXor go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint8 (v1 : w8) (v2 : w64) : ⟦GoShift GoShiftl go.uint8 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_uint8 (v1 : w8) (v2 : w64) : ⟦GoShift GoShiftr go.uint8 go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 >>> v2)
  shift_count_uint8 (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w8) :
    ⟦GoShift o t go.uint8, (v1, #y)⟧ ⤳[under] GoShift o t go.uint64 (Pair v1 #(W64 (uint.Z y)))

  complement_uint8 (v : w8) : ⟦GoUnOp GoComplement go.uint8, #v⟧ ⤳[under] #(~~~v)
  neg_uint8 (v : w8) : ⟦GoUnOp GoNeg go.uint8, #v⟧ ⤳[under] #(-v)

  convert_int_to_uint8 (v : w64) : ⟦Convert go.int go.uint8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int64_to_uint8 (v : w64) : ⟦Convert go.int64 go.uint8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int32_to_uint8 (v : w32) : ⟦Convert go.int32 go.uint8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int16_to_uint8 (v : w16) : ⟦Convert go.int16 go.uint8, #v⟧ ⤳[under] #(W8 (sint.Z v))
  convert_int8_to_uint8 (v : w8) : ⟦Convert go.int8 go.uint8, #v⟧ ⤳[under] #v
  convert_uint_to_uint8 (v : w64) : ⟦Convert go.uint go.uint8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint64_to_uint8 (v : w64) : ⟦Convert go.uint64 go.uint8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint32_to_uint8 (v : w32) : ⟦Convert go.uint32 go.uint8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint16_to_uint8 (v : w16) : ⟦Convert go.uint16 go.uint8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uint8_to_uint8 (v : w8) : ⟦Convert go.uint8 go.uint8, #v⟧ ⤳[under] #v

attribute [instance] Uint8Semantics.go_zero_val_uint8 Uint8Semantics.comparable_uint8
  Uint8Semantics.underlying_uint8 Uint8Semantics.go_eq_uint8 Uint8Semantics.le_uint8
  Uint8Semantics.lt_uint8 Uint8Semantics.ge_uint8 Uint8Semantics.gt_uint8 Uint8Semantics.plus_uint8
  Uint8Semantics.sub_uint8 Uint8Semantics.mul_uint8 Uint8Semantics.div_uint8
  Uint8Semantics.remainder_uint8 Uint8Semantics.and_uint8 Uint8Semantics.bitclear_uint8 Uint8Semantics.or_uint8
  Uint8Semantics.xor_uint8 Uint8Semantics.shiftl_uint8 Uint8Semantics.shiftr_uint8
  Uint8Semantics.shift_count_uint8
  Uint8Semantics.complement_uint8 Uint8Semantics.neg_uint8 Uint8Semantics.convert_int_to_uint8
  Uint8Semantics.convert_int64_to_uint8 Uint8Semantics.convert_int32_to_uint8
  Uint8Semantics.convert_int16_to_uint8 Uint8Semantics.convert_int8_to_uint8
  Uint8Semantics.convert_uint_to_uint8 Uint8Semantics.convert_uint64_to_uint8
  Uint8Semantics.convert_uint32_to_uint8 Uint8Semantics.convert_uint16_to_uint8
  Uint8Semantics.convert_uint8_to_uint8
export Uint8Semantics (go_zero_val_uint8 comparable_uint8 underlying_uint8 go_eq_uint8 le_uint8
  lt_uint8 ge_uint8 gt_uint8 plus_uint8 sub_uint8 mul_uint8 div_uint8 remainder_uint8 and_uint8 bitclear_uint8
  or_uint8 xor_uint8 shiftl_uint8 shiftr_uint8 shift_count_uint8 complement_uint8 neg_uint8 convert_int_to_uint8
  convert_int64_to_uint8 convert_int32_to_uint8 convert_int16_to_uint8 convert_int8_to_uint8
  convert_uint_to_uint8 convert_uint64_to_uint8 convert_uint32_to_uint8 convert_uint16_to_uint8
  convert_uint8_to_uint8)

/-- Semantics of `go.uintptr`. Trusted.

Go's predeclared `uintptr` is "an unsigned integer type large enough to store the uninterpreted
bits of a pointer value" (Go spec, Numeric types). It is word-sized: 64 bits on a 64-bit platform.
Perennial's semantics already assumes a 64-bit platform (`go.int` and `go.uint` are `w64`, e.g.
`convert_int_to_int64` is the identity), and `uintptr` being 64 bits is part of that same
assumption, not a separate choice. So `uintptr` is modelled exactly like `uint`/`uint64`:

* values are `w64` (it shares the `TypeReprUnderlying _ w64` representation with
  `uint`/`uint64`/`int`/`int64`), the zero value is `W64 0`, and it is strictly comparable;
* it occupies 8 byte cells, as `uint64` (`PredeclaredEncoding.enc_uintptr`);
* arithmetic, bitwise operations and shifts are the unsigned `w64` ones (wrapping mod 2^64,
  `>>` logical), comparisons are unsigned (`uint.Z`), as for `uint64`;
* conversions to and from the other integer types (and from untyped integer constants) are
  those of `uint64`: identity to/from 64-bit types, truncation to narrower types, sign/zero
  extension from narrower signed/unsigned types.

The conversion `uintptr(p)` of an `unsafe.Pointer` gives an unspecified address
(`UnsafeSemantics.convert_pointer_to_uintptr`); the conversion back, `unsafe.Pointer(u)`, is
not modelled (stuck), except as `unsafe.Pointer(uintptr(p) + n)`, which Goose translates as
`unsafe.Add(p, n)`. A `uintptr` is thus never turned back into a pointer. -/
class UintptrSemantics [GoSemanticsFunctions] : Prop where
  go_zero_val_uintptr : TypeReprUnderlying go.uintptr w64
  comparable_uintptr : ⟦CheckComparable go.uintptr, #()⟧ ⤳[under] #()
  underlying_uintptr : go.uintptr ↓u go.uintptr
  go_eq_uintptr : IsStrictlyComparable go.uintptr w64
  le_uintptr (v1 v2 : w64) : ⟦GoOp GoLe go.uintptr, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 ≤ uint.Z v2))
  lt_uintptr (v1 v2 : w64) : ⟦GoOp GoLt go.uintptr, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v1 < uint.Z v2))
  ge_uintptr (v1 v2 : w64) : ⟦GoOp GoGe go.uintptr, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 ≤ uint.Z v1))
  gt_uintptr (v1 v2 : w64) : ⟦GoOp GoGt go.uintptr, (#v1, #v2)⟧
    ⤳[under] #(decide (uint.Z v2 < uint.Z v1))
  plus_uintptr (v1 v2 : w64) : ⟦GoOp GoPlus go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 + v2)
  sub_uintptr (v1 v2 : w64) : ⟦GoOp GoSub go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 - v2)
  mul_uintptr (v1 v2 : w64) : ⟦GoOp GoMul go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 * v2)
  div_uintptr (v1 v2 : w64) : ⟦GoOp GoDiv go.uintptr, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 / v2))
  remainder_uintptr (v1 v2 : w64) : ⟦GoOp GoRemainder go.uintptr, (#v1, #v2)⟧
    ⤳[under] (if uint.Z v2 = 0 then Panic "integer divide by zero" else #(v1 % v2))
  and_uintptr (v1 v2 : w64) : ⟦GoOp GoAnd go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  bitclear_uintptr (v1 v2 : w64) : ⟦GoOp GoBitClear go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)
  or_uintptr (v1 v2 : w64) : ⟦GoOp GoOr go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uintptr (v1 v2 : w64) : ⟦GoOp GoXor go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uintptr (v1 v2 : w64) : ⟦GoShift GoShiftl go.uintptr go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 <<< v2)
  shiftr_uintptr (v1 v2 : w64) : ⟦GoShift GoShiftr go.uintptr go.uint64, (#v1, #v2)⟧
    ⤳[under] #(v1 >>> v2)
  shift_count_uintptr (o : GoShiftOperator) (t : go.GoType) (v1 : val) (y : w64) :
    ⟦GoShift o t go.uintptr, (v1, #y)⟧ ⤳[under] GoShift o t go.uint64 (Pair v1 #y)

  complement_uintptr (v : w64) : ⟦GoUnOp GoComplement go.uintptr, #v⟧ ⤳[under] #(~~~v)
  neg_uintptr (v : w64) : ⟦GoUnOp GoNeg go.uintptr, #v⟧ ⤳[under] #(-v)

  convert_untyped_int_to_uintptr (v : Int) : ⟦Convert go.untypedInt go.uintptr, #v⟧
    ⤳[under] #(W64 v)
  convert_int_to_uintptr (v : w64) : ⟦Convert go.int go.uintptr, #v⟧ ⤳[under] #v
  convert_int64_to_uintptr (v : w64) : ⟦Convert go.int64 go.uintptr, #v⟧ ⤳[under] #v
  convert_int32_to_uintptr (v : w32) : ⟦Convert go.int32 go.uintptr, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int16_to_uintptr (v : w16) : ⟦Convert go.int16 go.uintptr, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_int8_to_uintptr (v : w8) : ⟦Convert go.int8 go.uintptr, #v⟧ ⤳[under] #(W64 (sint.Z v))
  convert_uint_to_uintptr (v : w64) : ⟦Convert go.uint go.uintptr, #v⟧ ⤳[under] #v
  convert_uint64_to_uintptr (v : w64) : ⟦Convert go.uint64 go.uintptr, #v⟧ ⤳[under] #v
  convert_uint32_to_uintptr (v : w32) : ⟦Convert go.uint32 go.uintptr, #v⟧
    ⤳[under] #(W64 (uint.Z v))
  convert_uint16_to_uintptr (v : w16) : ⟦Convert go.uint16 go.uintptr, #v⟧
    ⤳[under] #(W64 (uint.Z v))
  convert_uint8_to_uintptr (v : w8) : ⟦Convert go.uint8 go.uintptr, #v⟧ ⤳[under] #(W64 (uint.Z v))
  convert_uintptr_to_uintptr (v : w64) : ⟦Convert go.uintptr go.uintptr, #v⟧ ⤳[under] #v
  convert_uintptr_to_int (v : w64) : ⟦Convert go.uintptr go.int, #v⟧ ⤳[under] #v
  convert_uintptr_to_int64 (v : w64) : ⟦Convert go.uintptr go.int64, #v⟧ ⤳[under] #v
  convert_uintptr_to_int32 (v : w64) : ⟦Convert go.uintptr go.int32, #v⟧ ⤳[under] #(W32 (uint.Z v))
  convert_uintptr_to_int16 (v : w64) : ⟦Convert go.uintptr go.int16, #v⟧ ⤳[under] #(W16 (uint.Z v))
  convert_uintptr_to_int8 (v : w64) : ⟦Convert go.uintptr go.int8, #v⟧ ⤳[under] #(W8 (uint.Z v))
  convert_uintptr_to_uint (v : w64) : ⟦Convert go.uintptr go.uint, #v⟧ ⤳[under] #v
  convert_uintptr_to_uint64 (v : w64) : ⟦Convert go.uintptr go.uint64, #v⟧ ⤳[under] #v
  convert_uintptr_to_uint32 (v : w64) : ⟦Convert go.uintptr go.uint32, #v⟧
    ⤳[under] #(W32 (uint.Z v))
  convert_uintptr_to_uint16 (v : w64) : ⟦Convert go.uintptr go.uint16, #v⟧
    ⤳[under] #(W16 (uint.Z v))
  convert_uintptr_to_uint8 (v : w64) : ⟦Convert go.uintptr go.uint8, #v⟧ ⤳[under] #(W8 (uint.Z v))

attribute [instance] UintptrSemantics.go_zero_val_uintptr UintptrSemantics.comparable_uintptr
  UintptrSemantics.underlying_uintptr UintptrSemantics.go_eq_uintptr UintptrSemantics.le_uintptr
  UintptrSemantics.lt_uintptr UintptrSemantics.ge_uintptr UintptrSemantics.gt_uintptr
  UintptrSemantics.plus_uintptr UintptrSemantics.sub_uintptr UintptrSemantics.mul_uintptr
  UintptrSemantics.div_uintptr UintptrSemantics.remainder_uintptr UintptrSemantics.and_uintptr UintptrSemantics.bitclear_uintptr
  UintptrSemantics.or_uintptr UintptrSemantics.xor_uintptr UintptrSemantics.shiftl_uintptr
  UintptrSemantics.shiftr_uintptr
  UintptrSemantics.shift_count_uintptr UintptrSemantics.complement_uintptr UintptrSemantics.neg_uintptr
  UintptrSemantics.convert_untyped_int_to_uintptr UintptrSemantics.convert_int_to_uintptr
  UintptrSemantics.convert_int64_to_uintptr UintptrSemantics.convert_int32_to_uintptr
  UintptrSemantics.convert_int16_to_uintptr UintptrSemantics.convert_int8_to_uintptr
  UintptrSemantics.convert_uint_to_uintptr UintptrSemantics.convert_uint64_to_uintptr
  UintptrSemantics.convert_uint32_to_uintptr UintptrSemantics.convert_uint16_to_uintptr
  UintptrSemantics.convert_uint8_to_uintptr UintptrSemantics.convert_uintptr_to_uintptr
  UintptrSemantics.convert_uintptr_to_int UintptrSemantics.convert_uintptr_to_int64
  UintptrSemantics.convert_uintptr_to_int32 UintptrSemantics.convert_uintptr_to_int16
  UintptrSemantics.convert_uintptr_to_int8 UintptrSemantics.convert_uintptr_to_uint
  UintptrSemantics.convert_uintptr_to_uint64 UintptrSemantics.convert_uintptr_to_uint32
  UintptrSemantics.convert_uintptr_to_uint16 UintptrSemantics.convert_uintptr_to_uint8
export UintptrSemantics (go_zero_val_uintptr comparable_uintptr underlying_uintptr go_eq_uintptr
  le_uintptr lt_uintptr ge_uintptr gt_uintptr plus_uintptr sub_uintptr mul_uintptr div_uintptr
  remainder_uintptr and_uintptr bitclear_uintptr or_uintptr xor_uintptr shiftl_uintptr shiftr_uintptr shift_count_uintptr
  complement_uintptr neg_uintptr convert_untyped_int_to_uintptr convert_int_to_uintptr convert_int64_to_uintptr
  convert_int32_to_uintptr convert_int16_to_uintptr convert_int8_to_uintptr convert_uint_to_uintptr
  convert_uint64_to_uintptr convert_uint32_to_uintptr convert_uint16_to_uintptr
  convert_uint8_to_uintptr convert_uintptr_to_uintptr convert_uintptr_to_int
  convert_uintptr_to_int64 convert_uintptr_to_int32 convert_uintptr_to_int16 convert_uintptr_to_int8
  convert_uintptr_to_uint convert_uintptr_to_uint64 convert_uintptr_to_uint32
  convert_uintptr_to_uint16 convert_uintptr_to_uint8)

class UntypedFloatSemantics [GoSemanticsFunctions] : Prop where
  underlying_untyped_float : go.untypedFloat ↓u go.untypedFloat
  convert_untyped_float64 (v : w64) : ⟦Convert go.untypedFloat go.float64, #v⟧ ⤳[under] #v
  convert_untyped_float32 (v : w64) : ⟦Convert go.untypedFloat go.float32, #v⟧
    ⤳[under] #(float64ToFloat32 v)

attribute [instance] UntypedFloatSemantics.underlying_untyped_float
  UntypedFloatSemantics.convert_untyped_float64 UntypedFloatSemantics.convert_untyped_float32
export UntypedFloatSemantics (underlying_untyped_float convert_untyped_float64
  convert_untyped_float32)

/-- Whether a `float64`'s bits are a NaN: all exponent bits set, a non-zero mantissa. -/
def isNaN64 (r : w64) : Bool :=
  decide ((uint.Z r / 2 ^ 52) % 2 ^ 11 = 2 ^ 11 - 1 ∧ uint.Z r % 2 ^ 52 ≠ 0)

/-- Whether a `float32`'s bits are a NaN. -/
def isNaN32 (r : w32) : Bool :=
  decide ((uint.Z r / 2 ^ 23) % 2 ^ 8 = 2 ^ 8 - 1 ∧ uint.Z r % 2 ^ 23 ≠ 0)

/-- `==` on `float64`s given by their bits (IEEE 754): false if either is a NaN, true for
`+0` and `-0`, and otherwise the bits are equal. -/
def float64Eqb (a b : w64) : Bool :=
  !isNaN64 a && !isNaN64 b &&
    (decide (a = b) || decide ((a ||| b) &&& 0x7FFFFFFFFFFFFFFF = 0))

/-- `==` on `float32`s given by their bits (IEEE 754). -/
def float32Eqb (a b : w32) : Bool :=
  !isNaN32 a && !isNaN32 b && (decide (a = b) || decide ((a ||| b) &&& 0x7FFFFFFF = 0))

/-- Any NaN `float64`: either sign, any non-zero mantissa. -/
def arbitraryNaN64 : Expr :=
  gl((((ArbitraryInt %⟨go.uint64⟩ #(W64 2)) *⟨go.uint64⟩ #(W64 (2 ^ 63))) +⟨go.uint64⟩
      #(W64 0x7FF0000000000000)) +⟨go.uint64⟩
      ((ArbitraryInt %⟨go.uint64⟩ #(W64 (2 ^ 52 - 1))) +⟨go.uint64⟩ #(W64 1)))

/-- Any NaN `float32`. -/
def arbitraryNaN32 : Expr :=
  App (Val (GoInstruction (Convert go.uint64 go.uint32)))
    gl((((ArbitraryInt %⟨go.uint64⟩ #(W64 2)) *⟨go.uint64⟩ #(W64 (2 ^ 31))) +⟨go.uint64⟩
      #(W64 0x7F800000)) +⟨go.uint64⟩
      ((ArbitraryInt %⟨go.uint64⟩ #(W64 (2 ^ 23 - 1))) +⟨go.uint64⟩ #(W64 1)))

/-- The result `r` of a `float64` operation, a fixed function of its operands (`FloatOps`)
unless it is a NaN: which NaN an operation on NaNs gives depends on how gc compiled it
(the order of a commutative operation's operands, constant folding), and its bits are
observable through package `unsafe`, so a NaN result is any NaN. A float function that gc
compiles to an instruction rather than its Go body (`math.Sqrt`, `Floor`, `FMA`, ...) gives
the instruction's NaN, so it must stay trusted with any-NaN results, not be translated. -/
def floatResult64 (r : w64) : Expr := if isNaN64 r then arbitraryNaN64 else Val #r

/-- `floatResult64` for `float32`. -/
def floatResult32 (r : w32) : Expr := if isNaN32 r then arbitraryNaN32 else Val #r

/-- `MinByLt t`: Go's `min`/`max` on `t` is `<`'s choice (`min.impl`): integers,
`uintptr`, strings, and named types of them. Not floats, whose `min` of a NaN is a NaN and
`min(-0, +0)` is `-0` (`minFloat.impl`). -/
inductive MinByLt [GoSemanticsFunctions] : go.GoType → Prop
  | int : MinByLt go.int
  | int8 : MinByLt go.int8
  | int16 : MinByLt go.int16
  | int32 : MinByLt go.int32
  | int64 : MinByLt go.int64
  | uint : MinByLt go.uint
  | uint8 : MinByLt go.uint8
  | uint16 : MinByLt go.uint16
  | uint32 : MinByLt go.uint32
  | uint64 : MinByLt go.uint64
  | uintptr : MinByLt go.uintptr
  | string : MinByLt go.string
  | named (t u : go.GoType) (hu : t ↓u u) (h : MinByLt u) : MinByLt t

attribute [class] MinByLt
attribute [instance] MinByLt.int MinByLt.int8 MinByLt.int16 MinByLt.int32 MinByLt.int64
  MinByLt.uint MinByLt.uint8 MinByLt.uint16 MinByLt.uint32 MinByLt.uint64 MinByLt.uintptr
  MinByLt.string

instance (priority := low) [GoSemanticsFunctions] (t u : go.GoType) [hu : t ↓u u]
    [h : MinByLt u] : MinByLt t := .named t u hu h

/-- `min(x, y)` of floats of type `t` (the Go spec; gc on amd64 compiles it to an
instruction, `ssa.OpMin64F`): a NaN if either is a NaN (any NaN: which one depends on the
instruction), else the smaller, and of two equal values (`x == y`) the one with the sign bit
set if either has it (`min(-0, +0) = -0`): the OR of their bits (`runtime.forbits`), at the
unsigned type `bits` of the same width. `nan` is the expression for any NaN of the width. -/
def minFloat.impl (t bits : go.GoType) (nan : Expr) (n : Nat) : val :=
  match n with
  | 2 => LamV "x" (Lam "y"
      (If (App (Val (GoInstruction (GoOp GoEquals t))) (Pair (Var "x") (Var "x")))
        (If (App (Val (GoInstruction (GoOp GoEquals t))) (Pair (Var "y") (Var "y")))
          (If (App (Val (GoInstruction (GoOp GoLt t))) (Pair (Var "x") (Var "y"))) (Var "x")
            (If (App (Val (GoInstruction (GoOp GoLt t))) (Pair (Var "y") (Var "x"))) (Var "y")
              (App (Val (GoInstruction (GoOp GoOr bits)))
                (Pair (Var "x") (Var "y")))))
          nan)
        nan))
  | _ => LitV LitPoison

/-- `max(x, y)` of floats: as `minFloat.impl`, the larger, and of two equal values the AND of
their bits (`max(-0, +0) = +0`, `runtime.fandbits`). -/
def maxFloat.impl (t bits : go.GoType) (nan : Expr) (n : Nat) : val :=
  match n with
  | 2 => LamV "x" (Lam "y"
      (If (App (Val (GoInstruction (GoOp GoEquals t))) (Pair (Var "x") (Var "x")))
        (If (App (Val (GoInstruction (GoOp GoEquals t))) (Pair (Var "y") (Var "y")))
          (If (App (Val (GoInstruction (GoOp GoGt t))) (Pair (Var "x") (Var "y"))) (Var "x")
            (If (App (Val (GoInstruction (GoOp GoGt t))) (Pair (Var "y") (Var "x"))) (Var "y")
              (App (Val (GoInstruction (GoOp GoAnd bits)))
                (Pair (Var "x") (Var "y")))))
          nan)
        nan))
  | _ => LitV LitPoison

class Float64Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_float64 : TypeReprUnderlying go.float64 w64
  comparable_float64 : ⟦CheckComparable go.float64, #()⟧ ⤳[under] #()
  underlying_float64 : go.float64 ↓u go.float64
  /-- IEEE equality, not equality of the bits: a NaN is not `==` to itself, `-0 == +0`. -/
  go_eq_float64 (v1 v2 : w64) : ⟦GoOp GoEquals go.float64, (#v1, #v2)⟧ ⤳[under]
    #(float64Eqb v1 v2)
  le_float64 (v1 v2 : w64) : ⟦GoOp GoLe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Leb v1 v2)
  /-- `<` is `≤` and not `==` (which IEEE's order satisfies: `-0 < +0` is false), with `≤`
  an uninterpreted function. -/
  lt_float64 (v1 v2 : w64) : ⟦GoOp GoLt go.float64, (#v1, #v2)⟧
    ⤳[under] #(float64Leb v1 v2 && !float64Eqb v1 v2)
  ge_float64 (v1 v2 : w64) : ⟦GoOp GoGe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Leb v2 v1)
  gt_float64 (v1 v2 : w64) : ⟦GoOp GoGt go.float64, (#v1, #v2)⟧
    ⤳[under] #(float64Leb v2 v1 && !float64Eqb v1 v2)
  plus_float64 (v1 v2 : w64) : ⟦GoOp GoPlus go.float64, (#v1, #v2)⟧ ⤳[under]
    floatResult64 (float64Add v1 v2)
  sub_float64 (v1 v2 : w64) : ⟦GoOp GoSub go.float64, (#v1, #v2)⟧ ⤳[under]
    floatResult64 (float64Sub v1 v2)
  mul_float64 (v1 v2 : w64) : ⟦GoOp GoMul go.float64, (#v1, #v2)⟧ ⤳[under]
    floatResult64 (float64Mul v1 v2)
  div_float64 (v1 v2 : w64) : ⟦GoOp GoDiv go.float64, (#v1, #v2)⟧ ⤳[under]
    floatResult64 (float64Div v1 v2)
  -- `float64(n)` of an integer: an uninterpreted function of the integer (`FloatOps`)
  convert_int_to_float64 (v : w64) : ⟦Convert go.int go.float64, #v⟧ ⤳[under] #(int64ToFloat64 v)
  convert_int64_to_float64 (v : w64) :
    ⟦Convert go.int64 go.float64, #v⟧ ⤳[under] #(int64ToFloat64 v)
  convert_uint_to_float64 (v : w64) : ⟦Convert go.uint go.float64, #v⟧ ⤳[under] #(uint64ToFloat64 v)
  convert_uint64_to_float64 (v : w64) :
    ⟦Convert go.uint64 go.float64, #v⟧ ⤳[under] #(uint64ToFloat64 v)
  convert_int32_to_float64 (v : w32) :
    ⟦Convert go.int32 go.float64, #v⟧ ⤳[under] #(int32ToFloat64 v)
  convert_uint32_to_float64 (v : w32) :
    ⟦Convert go.uint32 go.float64, #v⟧ ⤳[under] #(uint32ToFloat64 v)

attribute [instance] Float64Semantics.go_zero_val_float64 Float64Semantics.comparable_float64
  Float64Semantics.underlying_float64 Float64Semantics.go_eq_float64 Float64Semantics.le_float64
  Float64Semantics.lt_float64 Float64Semantics.ge_float64 Float64Semantics.gt_float64
  Float64Semantics.plus_float64 Float64Semantics.sub_float64 Float64Semantics.mul_float64
  Float64Semantics.div_float64 Float64Semantics.convert_int_to_float64
  Float64Semantics.convert_int64_to_float64 Float64Semantics.convert_uint_to_float64
  Float64Semantics.convert_uint64_to_float64 Float64Semantics.convert_int32_to_float64
  Float64Semantics.convert_uint32_to_float64
export Float64Semantics (go_zero_val_float64 comparable_float64 underlying_float64 go_eq_float64
  le_float64 lt_float64 ge_float64 gt_float64 plus_float64 sub_float64 mul_float64 div_float64
  convert_int_to_float64 convert_int64_to_float64 convert_uint_to_float64
  convert_uint64_to_float64 convert_int32_to_float64 convert_uint32_to_float64)

class Float32Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_float32 : TypeReprUnderlying go.float32 w32
  comparable_float32 : ⟦CheckComparable go.float32, #()⟧ ⤳[under] #()
  underlying_float32 : go.float32 ↓u go.float32
  /-- IEEE equality, not equality of the bits: a NaN is not `==` to itself, `-0 == +0`. -/
  go_eq_float32 (v1 v2 : w32) : ⟦GoOp GoEquals go.float32, (#v1, #v2)⟧ ⤳[under]
    #(float32Eqb v1 v2)
  le_float32 (v1 v2 : w32) : ⟦GoOp GoLe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Leb v1 v2)
  /-- `<` is `≤` and not `==` (which IEEE's order satisfies: `-0 < +0` is false), with `≤`
  an uninterpreted function. -/
  lt_float32 (v1 v2 : w32) : ⟦GoOp GoLt go.float32, (#v1, #v2)⟧
    ⤳[under] #(float32Leb v1 v2 && !float32Eqb v1 v2)
  ge_float32 (v1 v2 : w32) : ⟦GoOp GoGe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Leb v2 v1)
  gt_float32 (v1 v2 : w32) : ⟦GoOp GoGt go.float32, (#v1, #v2)⟧
    ⤳[under] #(float32Leb v2 v1 && !float32Eqb v1 v2)
  plus_float32 (v1 v2 : w32) : ⟦GoOp GoPlus go.float32, (#v1, #v2)⟧ ⤳[under]
    floatResult32 (float32Add v1 v2)
  sub_float32 (v1 v2 : w32) : ⟦GoOp GoSub go.float32, (#v1, #v2)⟧ ⤳[under]
    floatResult32 (float32Sub v1 v2)
  mul_float32 (v1 v2 : w32) : ⟦GoOp GoMul go.float32, (#v1, #v2)⟧ ⤳[under]
    floatResult32 (float32Mul v1 v2)
  div_float32 (v1 v2 : w32) : ⟦GoOp GoDiv go.float32, (#v1, #v2)⟧ ⤳[under]
    floatResult32 (float32Div v1 v2)

attribute [instance] Float32Semantics.go_zero_val_float32 Float32Semantics.comparable_float32
  Float32Semantics.underlying_float32 Float32Semantics.go_eq_float32 Float32Semantics.le_float32
  Float32Semantics.lt_float32 Float32Semantics.ge_float32 Float32Semantics.gt_float32
  Float32Semantics.plus_float32 Float32Semantics.sub_float32 Float32Semantics.mul_float32
  Float32Semantics.div_float32
export Float32Semantics (go_zero_val_float32 comparable_float32 underlying_float32 go_eq_float32
  le_float32 lt_float32 ge_float32 gt_float32 plus_float32 sub_float32 mul_float32 div_float32)

/-- `uintptr(p)` for a non-null `p` at offset `off` of its block: any address in
`[8, 2^48)` congruent to `off` modulo 8, chosen anew at each conversion.

Platform facts (linux/amd64): user-space addresses are below `2^48` (the kernel's user
space; gc's `heapAddrBits`), and no object is at an address below 8 (page 0 is never
mapped). By the convention of `IsFreshAligned`, offset 0 of a block is 8-aligned, so
`off % 8` is the address modulo 8: what Go's alignment guarantee gives. Nothing else is
promised: Go moves goroutine stacks, and "a `uintptr` … will not be updated if the object
moves" (package `unsafe`), so two conversions of the same pointer may differ. -/
def pointerAddr (off : Int) : Expr :=
  gl((((ArbitraryInt %⟨go.uint64⟩ #(W64 (2 ^ 45 - 1))) +⟨go.uint64⟩ #(W64 1)) *⟨go.uint64⟩
      #(W64 8)) +⟨go.uint64⟩ #(W64 (off % 8)))

/-- `NoOverlappingViews t`: two locations of type `t` are equal or disjoint, since `t` is
never reinterpreted (it is not `Reinterpretable`: a `*t` comes only from an allocation, a
field or an element of a typed object): slices, and named types of them. (Other types
that are not `Reinterpretable`, such as a large struct with a pointer field, are not
listed: their copies need `NoPartialOverlap`.) -/
inductive NoOverlappingViews [GoSemanticsFunctions] : go.GoType → Prop
  | slice (t : go.GoType) : NoOverlappingViews (go.SliceType t)
  | named (t u : go.GoType) (hu : t ↓u u) (h : NoOverlappingViews u) : NoOverlappingViews t

attribute [class] NoOverlappingViews
attribute [instance] NoOverlappingViews.slice

instance (priority := low) [GoSemanticsFunctions] (t u : go.GoType) [hu : t ↓u u]
    [h : NoOverlappingViews u] : NoOverlappingViews t := .named t u hu h

/-- A copy of `n` bytes from `src` to `dst` that gc's code cannot corrupt: the same
location, at most 16 bytes (gc loads them all before storing), different allocations, or
disjoint ranges. -/
def NoPartialOverlap (n : Int) (dst src : Loc) : Prop :=
  dst = src ∨ n ≤ 16 ∨ dst.locCar ≠ src.locCar ∨ n ≤ dst.locOff - src.locOff ∨ n ≤ src.locOff - dst.locOff

/-- The rest of package `unsafe` on linux/amd64: `uintptr(p)`, the difference of two such
conversions in one expression, `unsafe.Add` and `unsafe.Slice`. The conversion of a
`uintptr` to an `unsafe.Pointer` is not modeled (stuck), except in the form
`unsafe.Pointer(uintptr(p) + n)`, which Goose emits as `unsafe.Add(p, n)`. -/
class UnsafeSemantics [GoSemanticsFunctions] : Prop where
  /-- `(*t)(p)` keeps the location, for a type whose memory may be reinterpreted
  (`Reinterpretable`) and if the `t`'s cells from `p` are bytes (`CheckBytes`); any other is
  stuck. -/
  convert_unsafe_to_pointer (elem : go.GoType) [Reinterpretable elem] {V : Type} [ZeroVal V]
      [TypeRepr elem V] (l : Loc) :
    ⟦Convert unsafe.Pointer (go.PointerType elem), #l⟧ ⤳[under]
      (if l = null then #null
       else Seq (CheckBytes (Val (PairV #l (LitV (LitInt (W64 (typeSize V))))))) (Val #l))
  /-- `CheckCopy t (dst, src)` before `dst = src` (goose emits it when `src` is in memory):
  gc copies a struct or array of more than 16 bytes from memory to memory in forward chunks
  (`OpMove`; a `memmove` only for `*p = *q` of an array type), so when the two ranges
  overlap partially, which only `unsafe` views of the same bytes can arrange, it reads
  bytes it has already overwritten, while the model loads the value whole and stores it.
  Such a copy is stuck (there is no step). -/
  check_copy (t : go.GoType) {V : Type} [ZeroVal V] [TypeRepr t V] (dst src : Loc)
      (h : NoPartialOverlap (typeSize V) dst src) :
    ⟦CheckCopy t, (#dst, #src)⟧ ⤳ #()
  /-- A copy of a type that is never reinterpreted (`NoOverlappingViews`) cannot overlap
  partially. -/
  check_copy_no_views (t : go.GoType) [NoOverlappingViews t] (dst src : Loc) :
    ⟦CheckCopy t, (#dst, #src)⟧ ⤳ #()
  /-- `(*t)(nil)` is `nil`, for any `t` (nothing is reinterpreted). -/
  convert_unsafe_nil_to_pointer (elem : go.GoType) :
    ⟦Convert unsafe.Pointer (go.PointerType elem), #null⟧ ⤳[under] #null
  /-- `uintptr(p)`: `0` for `nil`, else an unspecified address (`pointerAddr`). -/
  convert_pointer_to_uintptr (l : Loc) :
    ⟦Convert «unsafe».Pointer go.uintptr, #l⟧ ⤳[under]
      (if l = null then #(W64 0) else pointerAddr l.locOff)
  /-- `uintptr(p) - uintptr(q)` within one expression, with no call or receive in `p` and
  `q` (Goose emits it as this subtraction of `unsafe.Pointer`s, which Go does not have):
  nothing moves between the two conversions, so for two pointers into the same
  allocation it is their distance; otherwise it is only known modulo 8 (`pointerAddr`). -/
  ptr_diff (l1 l2 : Loc) :
    ⟦GoOp GoSub «unsafe».Pointer, (#l1, #l2)⟧ ⤳[under]
      (if l1.locCar = l2.locCar then #(W64 (l1.locOff - l2.locOff))
       else gl((ArbitraryInt *⟨go.uint64⟩ #(W64 8)) +⟨go.uint64⟩
         #(W64 ((l1.locOff - l2.locOff) % 8))))
  /-- `unsafe.Add(ptr, len)`: `ptr` moved `len` bytes, which must stay in `ptr`'s
  allocation (package `unsafe`'s rules; one past the end is not in it). Beyond that, a
  non-zero `len` is stuck unless the cells from `ptr` to the result, both included, are
  bytes (`CheckBytes`): memory is only reached through `unsafe` where it is bytes, as in Go,
  so the model's representation of other values (and of padding) is never reinterpreted. -/
  add_unfold : FuncUnfold «unsafe».Add [] (λ: "p" "n",
    if: "n" =⟨go.int⟩ #(W64 0) then "p"
    else
      let: "q" := GoOp GoPlus (go.PointerType go.uint8) ("p", "n") in
      (if: "n" >⟨go.int⟩ #(W64 0) then CheckBytes ("p", "n" +⟨go.int⟩ #(W64 1))
       else CheckBytes ("q", #(W64 1) -⟨go.int⟩ "n")) ;;
      "q")
  /-- `unsafe.Slice(ptr, len)` (`len` an `int`) checks what `runtime.unsafeslice` checks: a
  negative `len`; for a zero-size element, a `nil` `ptr` with a positive `len`; otherwise
  `len × size` overflowing or running past the end of the address space
  (`mem > -uintptr(ptr)`, with `uintptr(ptr)` as `convert_pointer_to_uintptr`, so `0` for
  `nil`). A panic is stuck. Beyond Go's checks, the element type must be `Reinterpretable`
  and the slice's cells bytes (`CheckBytes`), which also puts it in `ptr`'s allocation
  (package `unsafe`'s rules; Go's `-d=checkptr` checks that). -/
  slice_unfold (t : go.GoType) [Reinterpretable t] {V : Type} [ZeroVal V] [TypeRepr t V] :
    FuncUnfold «unsafe».Slice [t] (λ: "p" "n",
      if: "n" <⟨go.int⟩ #(W64 0) then Panic "unsafe.Slice: len out of range"
      else (if typeSize V = 0 then
        gl(if: "p" =⟨go.PointerType t⟩ #null then
             (if: "n" =⟨go.int⟩ #(W64 0) then InternalMakeSlice ("p", "n", "n")
              else Panic "unsafe.Slice: ptr is nil and len is not zero")
           else InternalMakeSlice ("p", "n", "n"))
      else gl(
        let: "a" := Convert «unsafe».Pointer go.uintptr
          (Convert (go.PointerType t) «unsafe».Pointer "p") in
        if: ("n" >⟨go.uint64⟩ #(W64 ((2 ^ 64 - 1) / typeSize V))) then
          (if: "p" =⟨go.PointerType t⟩ #null then Panic "unsafe.Slice: ptr is nil and len is not zero"
           else Panic "unsafe.Slice: len out of range")
        else if: ("n" *⟨go.uint64⟩ #(W64 (typeSize V))) >⟨go.uint64⟩ (#(W64 0) -⟨go.uint64⟩ "a") then
          (if: "p" =⟨go.PointerType t⟩ #null then Panic "unsafe.Slice: ptr is nil and len is not zero"
           else Panic "unsafe.Slice: len out of range")
        else
          (if: "n" =⟨go.int⟩ #(W64 0) then #()
           else
             CheckBytes (Convert (go.PointerType t) «unsafe».Pointer "p",
               "n" *⟨go.int⟩ #(W64 (typeSize V)))) ;;
          InternalMakeSlice ("p", "n", "n"))) : val)
  /-- `(*[n]t)(p)[lo:hi:max]` (`p` an `unsafe.Pointer`; the bounds `int`s): the bounds and
  `nil` checks of slicing a pointer to an array of `n` elements (pure, as
  `fullSlice_array_step_pure`), and the `max` elements' cells bytes (`CheckBytes`), as gc's
  `-d=checkptr` checks only them for this form. The array `[n]t` may be larger than the
  allocation (bbolt's `(*[maxAllocSize]byte)(p)[i:j:j]`): `(*[n]t)(p)` alone checks all `n`
  elements. -/
  array_slice_unfold (n : Int) (t : go.GoType) [Reinterpretable t] {V : Type} [ZeroVal V]
      [TypeRepr t V] :
    FuncUnfold «unsafe».ArraySlice [go.ArrayType n t] (λ: "p" "lo" "hi" "max",
      let: "s" := FullSlice (go.ArrayType n t) ("p", "lo", "hi", "max") in
      (if: "max" =⟨go.int⟩ #(W64 0) then #()
       else CheckBytes ("p", "max" *⟨go.int⟩ #(W64 (typeSize V)))) ;;
      "s")

attribute [instance] UnsafeSemantics.convert_unsafe_to_pointer
  UnsafeSemantics.convert_unsafe_nil_to_pointer
  UnsafeSemantics.convert_pointer_to_uintptr UnsafeSemantics.ptr_diff
  UnsafeSemantics.add_unfold UnsafeSemantics.slice_unfold UnsafeSemantics.array_slice_unfold
  UnsafeSemantics.check_copy_no_views
export UnsafeSemantics (convert_unsafe_to_pointer convert_unsafe_nil_to_pointer
  convert_pointer_to_uintptr ptr_diff add_unfold
  slice_unfold array_slice_unfold check_copy check_copy_no_views)

class PredeclaredSemantics [GoSemanticsFunctions] : Prop where
  /-- A value of a predeclared type is allocated as a block of its size (`allocEncoded`),
  loaded and stored non-atomically on all its cells (`ReadN`, `StoreN`: a race with an
  access of any of its cells is stuck). -/
  alloc_predeclared (u : go.GoType) {enc : Encoding} [H : PredeclaredEncoding u enc] (v : val) :
    ⟦GoAlloc u, v⟧ ⤳[internalUnder] allocEncoded enc v
  load_predeclared (u : go.GoType) {enc : Encoding} [H : PredeclaredEncoding u enc] (l : val) :
    ⟦GoLoad u, l⟧ ⤳[internalUnder] App (Val (ReadN enc)) (Val l)
  store_predeclared (u : go.GoType) {enc : Encoding} [H : PredeclaredEncoding u enc] (l v : val) :
    ⟦GoStore u, (l, v)⟧ ⤳[internalUnder] App (App (Val (StoreN enc)) (Val l)) (Val v)

  predeclared_underlying (t : go.GoType) (H : IsPredeclared t) : underlying t = t

  len_underlying (t : go.GoType) : functions len [t] = functions len [underlying t]
  cap_underlying (t : go.GoType) : functions cap [t] = functions cap [underlying t]
  clear_underlying (t : go.GoType) : functions clear [t] = functions clear [underlying t]
  copy_underlying (t : go.GoType) : functions copy [t] = functions copy [underlying t]
  delete_underlying (t : go.GoType) : functions delete [t] = functions delete [underlying t]
  make3_underlying (t : go.GoType) : functions make3 [t] = functions make3 [underlying t]
  make2_underlying (t : go.GoType) : functions make2 [t] = functions make2 [underlying t]
  make1_underlying (t : go.GoType) : functions make1 [t] = functions make1 [underlying t]

  min_unfold (n : Nat) (t : go.GoType) [MinByLt t] :
    FuncUnfold min (List.replicate n t) (min.impl t n)
  max_unfold (n : Nat) (t : go.GoType) [MinByLt t] :
    FuncUnfold max (List.replicate n t) (max.impl t n)
  /-- `min`/`max` of floats (`minFloat.impl`): of a type whose underlying type is `float64`
  or `float32`, at that float type (the bit operation is on its width). -/
  min_unfold_float64 (n : Nat) (t : go.GoType) [t ↓u go.float64] :
    FuncUnfold min (List.replicate n t) (minFloat.impl go.float64 go.uint64 arbitraryNaN64 n)
  max_unfold_float64 (n : Nat) (t : go.GoType) [t ↓u go.float64] :
    FuncUnfold max (List.replicate n t) (maxFloat.impl go.float64 go.uint64 arbitraryNaN64 n)
  min_unfold_float32 (n : Nat) (t : go.GoType) [t ↓u go.float32] :
    FuncUnfold min (List.replicate n t) (minFloat.impl go.float32 go.uint32 arbitraryNaN32 n)
  max_unfold_float32 (n : Nat) (t : go.GoType) [t ↓u go.float32] :
    FuncUnfold max (List.replicate n t) (maxFloat.impl go.float32 go.uint32 arbitraryNaN32 n)
  panic_unfold : FuncUnfold panic [] panic.impl

  [unsafe_sem : unsafe.Semantics]
  [unsafe_ext_sem : UnsafeSemantics]

  comparable_bool : ⟦CheckComparable go.bool, #()⟧ ⤳[under] #()
  go_eq_bool : IsStrictlyComparable go.bool Bool
  underlying_bool : go.bool ↓u go.bool
  go_zero_val_bool : TypeReprUnderlying go.bool Bool
  go_unop_not_bool (b : Bool) : ⟦GoUnOp GoNot go.bool, #b⟧ ⤳[under] #(!b)

  [untypedInt_semantics : UntypedIntSemantics]
  [int_semantics : IntSemantics]
  [int64_semantics : Int64Semantics]
  [int32_semantics : Int32Semantics]
  [int16_semantics : Int16Semantics]
  [int8_semantics : Int8Semantics]
  [uint_semantics : UintSemantics]
  [uint64_semantics : Uint64Semantics]
  [uint32_semantics : Uint32Semantics]
  [uint16_semantics : Uint16Semantics]
  [uint8_semantics : Uint8Semantics]
  [uintptr_semantics : UintptrSemantics] -- see `UintptrSemantics`
  [untypedFloat_semantics : UntypedFloatSemantics]
  [float64_semantics : Float64Semantics]
  [float32_semantics : Float32Semantics]
  [prophid_semantics : ProphIdSemantics]

  comparable_string : ⟦CheckComparable go.string, #()⟧ ⤳[under] #()
  go_eq_string : IsStrictlyComparable go.string GoString
  underlying_string : go.string ↓u go.string
  plus_string (v1 v2 : GoString) : ⟦GoOp GoPlus go.string, (#v1, #v2)⟧ ⤳[under] #(v1 ++ v2)
  go_zero_val_string : TypeReprUnderlying go.string GoString

  underlying_untyped_nil : go.untypedNil ↓u go.untypedNil
  convert_nil_pointer (elem : go.GoType) :
    ⟦Convert go.untypedNil (go.PointerType elem), UntypedNil⟧ ⤳[under] #null
  convert_nil_function (sig : go.signature) :
    ⟦Convert go.untypedNil (go.FunctionType sig), UntypedNil⟧ ⤳[under] #func.nil
  convert_nil_slice (elem : go.GoType) :
    ⟦Convert go.untypedNil (go.SliceType elem), UntypedNil⟧ ⤳[under] #slice.nil
  convert_nil_chan (dir : go.ChanDir) (elem : go.GoType) :
    ⟦Convert go.untypedNil (go.ChannelType dir elem), UntypedNil⟧ ⤳[under] #chan.nil
  convert_nil_map (key elem : go.GoType) :
    ⟦Convert go.untypedNil (go.MapType key elem), UntypedNil⟧ ⤳[under] #map.nil
  convert_nil_interface (elems : List go.InterfaceElem) :
    ⟦Convert go.untypedNil (go.InterfaceType elems), UntypedNil⟧ ⤳[under] #interface.nil
  convert_nil_unsafe_pointer :
    ⟦Convert go.untypedNil «unsafe».Pointer, UntypedNil⟧ ⤳[under] #null

  type_repr_empty_struct : TypeReprUnderlying (go.StructType []) Unit

attribute [instance] PredeclaredSemantics.alloc_predeclared PredeclaredSemantics.load_predeclared
  PredeclaredSemantics.store_predeclared PredeclaredSemantics.min_unfold
  PredeclaredSemantics.max_unfold PredeclaredSemantics.min_unfold_float64
  PredeclaredSemantics.max_unfold_float64 PredeclaredSemantics.min_unfold_float32
  PredeclaredSemantics.max_unfold_float32 PredeclaredSemantics.panic_unfold PredeclaredSemantics.unsafe_sem
  PredeclaredSemantics.unsafe_ext_sem
  PredeclaredSemantics.comparable_bool PredeclaredSemantics.go_eq_bool
  PredeclaredSemantics.underlying_bool PredeclaredSemantics.go_zero_val_bool
  PredeclaredSemantics.go_unop_not_bool PredeclaredSemantics.untypedInt_semantics
  PredeclaredSemantics.int_semantics PredeclaredSemantics.int64_semantics
  PredeclaredSemantics.int32_semantics PredeclaredSemantics.int16_semantics
  PredeclaredSemantics.int8_semantics PredeclaredSemantics.uint_semantics
  PredeclaredSemantics.uint64_semantics PredeclaredSemantics.uint32_semantics
  PredeclaredSemantics.uint16_semantics PredeclaredSemantics.uint8_semantics
  PredeclaredSemantics.uintptr_semantics
  PredeclaredSemantics.untypedFloat_semantics PredeclaredSemantics.float64_semantics
  PredeclaredSemantics.float32_semantics PredeclaredSemantics.prophid_semantics
  PredeclaredSemantics.comparable_string PredeclaredSemantics.go_eq_string
  PredeclaredSemantics.underlying_string PredeclaredSemantics.plus_string
  PredeclaredSemantics.go_zero_val_string PredeclaredSemantics.underlying_untyped_nil
  PredeclaredSemantics.convert_nil_pointer PredeclaredSemantics.convert_nil_function
  PredeclaredSemantics.convert_nil_slice PredeclaredSemantics.convert_nil_chan
  PredeclaredSemantics.convert_nil_map PredeclaredSemantics.convert_nil_interface
  PredeclaredSemantics.convert_nil_unsafe_pointer
  PredeclaredSemantics.type_repr_empty_struct
export PredeclaredSemantics (alloc_predeclared load_predeclared store_predeclared
  predeclared_underlying len_underlying cap_underlying clear_underlying copy_underlying
  delete_underlying make3_underlying make2_underlying make1_underlying min_unfold max_unfold min_unfold_float64 max_unfold_float64
  min_unfold_float32 max_unfold_float32 panic_unfold
  unsafe_sem comparable_bool go_eq_bool underlying_bool go_zero_val_bool go_unop_not_bool
  untypedInt_semantics int_semantics int64_semantics int32_semantics int16_semantics
  int8_semantics uint_semantics uint64_semantics uint32_semantics uint16_semantics
  uint8_semantics uintptr_semantics untypedFloat_semantics float64_semantics float32_semantics
  prophid_semantics
  comparable_string go_eq_string underlying_string plus_string go_zero_val_string
  underlying_untyped_nil convert_nil_pointer convert_nil_function convert_nil_slice
  convert_nil_chan convert_nil_map convert_nil_interface convert_nil_unsafe_pointer
  type_repr_empty_struct)

end defs
end go

end Perennial
