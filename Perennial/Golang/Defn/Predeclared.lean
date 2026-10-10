/-
Go's predeclared identifiers and the
semantics of the predeclared types.

Word operations: add/sub/mul are `+ - *`, unsigned div/mod are `/ %`, signed
div/mod are `BitVec.sdiv/srem`, and/or/xor are `&&& ||| ^^^`, left and logical
right shift are `<<< >>>`, arithmetic right shift is `BitVec.sshiftRight'`,
negation is `-` and bitwise not is `~~~`.
-/
module

public import Perennial.Golang.Defn.PostLang

@[expose] public section

namespace Perennial

namespace error
abbrev _root_.Perennial.GoError [FfiSyntax] : Type := GoInterface
end error

section helpers
variable [FfiSyntax] [GoGlobalContext]

def min.impl (t : go.GoType) (n : Nat) : val :=
  match n with
  | 2 => λ: "x" "y", if: ("x" <⟨t⟩ "y") then "x" else "y"
  | _ => LitV LitPoison

def max.impl (t : go.GoType) (n : Nat) : val :=
  match n with
  | 2 => λ: "x" "y", if: "x" >⟨t⟩ "y" then "x" else "y"
  | _ => LitV LitPoison

/-- `panic(v)` starts a panic with the value `v` (`Raise`), which unwinds the
evaluation context up to a `Catch` (a function with `defer`s, `wrapDefer`). -/
def panic.impl : val := λ: "v", Raise "v"

end helpers

namespace «unsafe»
def Pointer : go.GoType := go.Named go!"unsafe.Pointer" []

class Semantics [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  go_zero_val_Pointer : go.TypeReprUnderlying Pointer Loc
  go_eq_Pointer : go.IsStrictlyComparable Pointer Loc
  underlying_pointer : unsafe.Pointer ↓u unsafe.Pointer
  convert_unsafe_to_pointer (elem : go.GoType) (l : Loc) :
    ⟦Convert unsafe.Pointer (go.PointerType elem), #l⟧ ⤳[under] #l
  convert_pointer_to_unsafe (elem : go.GoType) (l : Loc) :
    ⟦Convert (go.PointerType elem) unsafe.Pointer, #l⟧ ⤳[under] #l

attribute [instance] Semantics.go_zero_val_Pointer Semantics.go_eq_Pointer
  Semantics.underlying_pointer Semantics.convert_unsafe_to_pointer
  Semantics.convert_pointer_to_unsafe
export Semantics (go_zero_val_Pointer go_eq_Pointer underlying_pointer convert_unsafe_to_pointer
  convert_pointer_to_unsafe)
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

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext]

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

attribute [instance] UntypedIntSemantics.underlying_untyped_int UntypedIntSemantics.neg_untyped_int
  UntypedIntSemantics.convert_untyped_int_to_int UntypedIntSemantics.convert_untyped_int_to_int64
  UntypedIntSemantics.convert_untyped_int_to_int32 UntypedIntSemantics.convert_untyped_int_to_int16
  UntypedIntSemantics.convert_untyped_int_to_int8 UntypedIntSemantics.convert_untyped_int_to_uint
  UntypedIntSemantics.convert_untyped_int_to_uint64
  UntypedIntSemantics.convert_untyped_int_to_uint32
  UntypedIntSemantics.convert_untyped_int_to_uint16 UntypedIntSemantics.convert_untyped_int_to_uint8
export UntypedIntSemantics (underlying_untyped_int neg_untyped_int convert_untyped_int_to_int
  convert_untyped_int_to_int64 convert_untyped_int_to_int32 convert_untyped_int_to_int16
  convert_untyped_int_to_int8 convert_untyped_int_to_uint convert_untyped_int_to_uint64
  convert_untyped_int_to_uint32 convert_untyped_int_to_uint16 convert_untyped_int_to_uint8)

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
  div_int (v1 v2 : w64) : ⟦GoOp GoDiv go.int, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_int (v1 v2 : w64) : ⟦GoOp GoRemainder go.int, (#v1, #v2)⟧ ⤳[under] #(BitVec.srem v1 v2)
  and_int (v1 v2 : w64) : ⟦GoOp GoAnd go.int, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_int (v1 v2 : w64) : ⟦GoOp GoOr go.int, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int (v1 v2 : w64) : ⟦GoOp GoXor go.int, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int (v1 v2 : w64) : ⟦GoOp GoShiftl go.int, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int (v1 v2 : w64) : ⟦GoOp GoShiftr go.int, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)

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
  IntSemantics.mul_int IntSemantics.div_int IntSemantics.remainder_int IntSemantics.and_int
  IntSemantics.or_int IntSemantics.xor_int IntSemantics.shiftl_int IntSemantics.shiftr_int
  IntSemantics.neg_int IntSemantics.complement_int IntSemantics.convert_int_to_int
  IntSemantics.convert_int64_to_int IntSemantics.convert_int32_to_int
  IntSemantics.convert_int16_to_int IntSemantics.convert_int8_to_int
  IntSemantics.convert_uint_to_int IntSemantics.convert_uint64_to_int
  IntSemantics.convert_uint32_to_int IntSemantics.convert_uint16_to_int
  IntSemantics.convert_uint8_to_int
export IntSemantics (go_zero_val_int comparable_int underlying_int go_eq_int le_int lt_int ge_int
  gt_int plus_int sub_int mul_int div_int remainder_int and_int or_int xor_int shiftl_int shiftr_int
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
  div_int64 (v1 v2 : w64) : ⟦GoOp GoDiv go.int64, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_int64 (v1 v2 : w64) : ⟦GoOp GoRemainder go.int64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.srem v1 v2)
  and_int64 (v1 v2 : w64) : ⟦GoOp GoAnd go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_int64 (v1 v2 : w64) : ⟦GoOp GoOr go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int64 (v1 v2 : w64) : ⟦GoOp GoXor go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int64 (v1 v2 : w64) : ⟦GoOp GoShiftl go.int64, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int64 (v1 v2 : w64) : ⟦GoOp GoShiftr go.int64, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)

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
  Int64Semantics.remainder_int64 Int64Semantics.and_int64 Int64Semantics.or_int64
  Int64Semantics.xor_int64 Int64Semantics.shiftl_int64 Int64Semantics.shiftr_int64
  Int64Semantics.neg_int64 Int64Semantics.complement_int64 Int64Semantics.convert_int_to_int64
  Int64Semantics.convert_int64_to_int64 Int64Semantics.convert_int32_to_int64
  Int64Semantics.convert_int16_to_int64 Int64Semantics.convert_int8_to_int64
  Int64Semantics.convert_uint_to_int64 Int64Semantics.convert_uint64_to_int64
  Int64Semantics.convert_uint32_to_int64 Int64Semantics.convert_uint16_to_int64
  Int64Semantics.convert_uint8_to_int64
export Int64Semantics (go_zero_val_int64 comparable_int64 underlying_int64 go_eq_int64 le_int64
  lt_int64 ge_int64 gt_int64 plus_int64 sub_int64 mul_int64 div_int64 remainder_int64 and_int64
  or_int64 xor_int64 shiftl_int64 shiftr_int64 neg_int64 complement_int64 convert_int_to_int64
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
  div_int32 (v1 v2 : w32) : ⟦GoOp GoDiv go.int32, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_int32 (v1 v2 : w32) : ⟦GoOp GoRemainder go.int32, (#v1, #v2)⟧
    ⤳[under] #(BitVec.srem v1 v2)
  and_int32 (v1 v2 : w32) : ⟦GoOp GoAnd go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_int32 (v1 v2 : w32) : ⟦GoOp GoOr go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int32 (v1 v2 : w32) : ⟦GoOp GoXor go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int32 (v1 v2 : w32) : ⟦GoOp GoShiftl go.int32, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int32 (v1 v2 : w32) : ⟦GoOp GoShiftr go.int32, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)

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
  Int32Semantics.remainder_int32 Int32Semantics.and_int32 Int32Semantics.or_int32
  Int32Semantics.xor_int32 Int32Semantics.shiftl_int32 Int32Semantics.shiftr_int32
  Int32Semantics.neg_int32 Int32Semantics.complement_int32 Int32Semantics.convert_int_to_int32
  Int32Semantics.convert_int64_to_int32 Int32Semantics.convert_int32_to_int32
  Int32Semantics.convert_int16_to_int32 Int32Semantics.convert_int8_to_int32
  Int32Semantics.convert_uint_to_int32 Int32Semantics.convert_uint64_to_int32
  Int32Semantics.convert_uint32_to_int32 Int32Semantics.convert_uint16_to_int32
  Int32Semantics.convert_uint8_to_int32
export Int32Semantics (go_zero_val_int32 comparable_int32 underlying_int32 go_eq_int32 le_int32
  lt_int32 ge_int32 gt_int32 plus_int32 sub_int32 mul_int32 div_int32 remainder_int32 and_int32
  or_int32 xor_int32 shiftl_int32 shiftr_int32 neg_int32 complement_int32 convert_int_to_int32
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
  div_int16 (v1 v2 : w16) : ⟦GoOp GoDiv go.int16, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_int16 (v1 v2 : w16) : ⟦GoOp GoRemainder go.int16, (#v1, #v2)⟧
    ⤳[under] #(BitVec.srem v1 v2)
  and_int16 (v1 v2 : w16) : ⟦GoOp GoAnd go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_int16 (v1 v2 : w16) : ⟦GoOp GoOr go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int16 (v1 v2 : w16) : ⟦GoOp GoXor go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int16 (v1 v2 : w16) : ⟦GoOp GoShiftl go.int16, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int16 (v1 v2 : w16) : ⟦GoOp GoShiftr go.int16, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)

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
  Int16Semantics.remainder_int16 Int16Semantics.and_int16 Int16Semantics.or_int16
  Int16Semantics.xor_int16 Int16Semantics.shiftl_int16 Int16Semantics.shiftr_int16
  Int16Semantics.neg_int16 Int16Semantics.complement_int16 Int16Semantics.convert_int_to_int16
  Int16Semantics.convert_int64_to_int16 Int16Semantics.convert_int32_to_int16
  Int16Semantics.convert_int16_to_int16 Int16Semantics.convert_int8_to_int16
  Int16Semantics.convert_uint_to_int16 Int16Semantics.convert_uint64_to_int16
  Int16Semantics.convert_uint32_to_int16 Int16Semantics.convert_uint16_to_int16
  Int16Semantics.convert_uint8_to_int16
export Int16Semantics (go_zero_val_int16 comparable_int16 underlying_int16 go_eq_int16 le_int16
  lt_int16 ge_int16 gt_int16 plus_int16 sub_int16 mul_int16 div_int16 remainder_int16 and_int16
  or_int16 xor_int16 shiftl_int16 shiftr_int16 neg_int16 complement_int16 convert_int_to_int16
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
  div_int8 (v1 v2 : w8) : ⟦GoOp GoDiv go.int8, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_int8 (v1 v2 : w8) : ⟦GoOp GoRemainder go.int8, (#v1, #v2)⟧ ⤳[under] #(BitVec.srem v1 v2)
  and_int8 (v1 v2 : w8) : ⟦GoOp GoAnd go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_int8 (v1 v2 : w8) : ⟦GoOp GoOr go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_int8 (v1 v2 : w8) : ⟦GoOp GoXor go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_int8 (v1 v2 : w8) : ⟦GoOp GoShiftl go.int8, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_int8 (v1 v2 : w8) : ⟦GoOp GoShiftr go.int8, (#v1, #v2)⟧
    ⤳[under] #(BitVec.sshiftRight' v1 v2)

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
  Int8Semantics.mul_int8 Int8Semantics.div_int8 Int8Semantics.remainder_int8 Int8Semantics.and_int8
  Int8Semantics.or_int8 Int8Semantics.xor_int8 Int8Semantics.shiftl_int8 Int8Semantics.shiftr_int8
  Int8Semantics.neg_int8 Int8Semantics.complement_int8 Int8Semantics.convert_int_to_int8
  Int8Semantics.convert_int64_to_int8 Int8Semantics.convert_int32_to_int8
  Int8Semantics.convert_int16_to_int8 Int8Semantics.convert_int8_to_int8
  Int8Semantics.convert_uint_to_int8 Int8Semantics.convert_uint64_to_int8
  Int8Semantics.convert_uint32_to_int8 Int8Semantics.convert_uint16_to_int8
  Int8Semantics.convert_uint8_to_int8
export Int8Semantics (go_zero_val_int8 comparable_int8 underlying_int8 go_eq_int8 le_int8 lt_int8
  ge_int8 gt_int8 plus_int8 sub_int8 mul_int8 div_int8 remainder_int8 and_int8 or_int8 xor_int8
  shiftl_int8 shiftr_int8 neg_int8 complement_int8 convert_int_to_int8 convert_int64_to_int8
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
  div_uint (v1 v2 : w64) : ⟦GoOp GoDiv go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 / v2)
  remainder_uint (v1 v2 : w64) : ⟦GoOp GoRemainder go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 % v2)
  and_uint (v1 v2 : w64) : ⟦GoOp GoAnd go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uint (v1 v2 : w64) : ⟦GoOp GoOr go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint (v1 v2 : w64) : ⟦GoOp GoXor go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint (v1 v2 : w64) : ⟦GoOp GoShiftl go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint (v1 v2 : w64) : ⟦GoOp GoShiftr go.uint, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  UintSemantics.mul_uint UintSemantics.div_uint UintSemantics.remainder_uint UintSemantics.and_uint
  UintSemantics.or_uint UintSemantics.xor_uint UintSemantics.shiftl_uint UintSemantics.shiftr_uint
  UintSemantics.complement_uint UintSemantics.neg_uint UintSemantics.convert_int_to_uint
  UintSemantics.convert_int64_to_uint UintSemantics.convert_int32_to_uint
  UintSemantics.convert_int16_to_uint UintSemantics.convert_int8_to_uint
  UintSemantics.convert_uint_to_uint UintSemantics.convert_uint64_to_uint
  UintSemantics.convert_uint32_to_uint UintSemantics.convert_uint16_to_uint
  UintSemantics.convert_uint8_to_uint
export UintSemantics (go_zero_val_uint comparable_uint underlying_uint go_eq_uint le_uint lt_uint
  ge_uint gt_uint plus_uint sub_uint mul_uint div_uint remainder_uint and_uint or_uint xor_uint
  shiftl_uint shiftr_uint complement_uint neg_uint convert_int_to_uint convert_int64_to_uint
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
  div_uint64 (v1 v2 : w64) : ⟦GoOp GoDiv go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 / v2)
  remainder_uint64 (v1 v2 : w64) : ⟦GoOp GoRemainder go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 % v2)
  and_uint64 (v1 v2 : w64) : ⟦GoOp GoAnd go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uint64 (v1 v2 : w64) : ⟦GoOp GoOr go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint64 (v1 v2 : w64) : ⟦GoOp GoXor go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint64 (v1 v2 : w64) : ⟦GoOp GoShiftl go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint64 (v1 v2 : w64) : ⟦GoOp GoShiftr go.uint64, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  Uint64Semantics.div_uint64 Uint64Semantics.remainder_uint64 Uint64Semantics.and_uint64
  Uint64Semantics.or_uint64 Uint64Semantics.xor_uint64 Uint64Semantics.shiftl_uint64
  Uint64Semantics.shiftr_uint64 Uint64Semantics.complement_uint64 Uint64Semantics.neg_uint64
  Uint64Semantics.convert_int_to_uint64 Uint64Semantics.convert_int64_to_uint64
  Uint64Semantics.convert_int32_to_uint64 Uint64Semantics.convert_int16_to_uint64
  Uint64Semantics.convert_int8_to_uint64 Uint64Semantics.convert_uint_to_uint64
  Uint64Semantics.convert_uint64_to_uint64 Uint64Semantics.convert_uint32_to_uint64
  Uint64Semantics.convert_uint16_to_uint64 Uint64Semantics.convert_uint8_to_uint64
export Uint64Semantics (go_zero_val_uint64 comparable_uint64 underlying_uint64 go_eq_uint64
  le_uint64 lt_uint64 ge_uint64 gt_uint64 plus_uint64 sub_uint64 mul_uint64 div_uint64
  remainder_uint64 and_uint64 or_uint64 xor_uint64 shiftl_uint64 shiftr_uint64 complement_uint64 neg_uint64
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
  div_uint32 (v1 v2 : w32) : ⟦GoOp GoDiv go.uint32, (#v1, #v2)⟧ ⤳[under] #(BitVec.sdiv v1 v2)
  remainder_uint32 (v1 v2 : w32) : ⟦GoOp GoRemainder go.uint32, (#v1, #v2)⟧
    ⤳[under] #(BitVec.srem v1 v2)
  and_uint32 (v1 v2 : w32) : ⟦GoOp GoAnd go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uint32 (v1 v2 : w32) : ⟦GoOp GoOr go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint32 (v1 v2 : w32) : ⟦GoOp GoXor go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint32 (v1 v2 : w32) : ⟦GoOp GoShiftl go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint32 (v1 v2 : w32) : ⟦GoOp GoShiftr go.uint32, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  Uint32Semantics.div_uint32 Uint32Semantics.remainder_uint32 Uint32Semantics.and_uint32
  Uint32Semantics.or_uint32 Uint32Semantics.xor_uint32 Uint32Semantics.shiftl_uint32
  Uint32Semantics.shiftr_uint32 Uint32Semantics.complement_uint32 Uint32Semantics.neg_uint32
  Uint32Semantics.convert_int_to_uint32 Uint32Semantics.convert_int64_to_uint32
  Uint32Semantics.convert_int32_to_uint32 Uint32Semantics.convert_int16_to_uint32
  Uint32Semantics.convert_int8_to_uint32 Uint32Semantics.convert_uint_to_uint32
  Uint32Semantics.convert_uint64_to_uint32 Uint32Semantics.convert_uint32_to_uint32
  Uint32Semantics.convert_uint16_to_uint32 Uint32Semantics.convert_uint8_to_uint32
export Uint32Semantics (go_zero_val_uint32 comparable_uint32 underlying_uint32 go_eq_uint32
  le_uint32 lt_uint32 ge_uint32 gt_uint32 plus_uint32 sub_uint32 mul_uint32 div_uint32
  remainder_uint32 and_uint32 or_uint32 xor_uint32 shiftl_uint32 shiftr_uint32 complement_uint32 neg_uint32
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
  div_uint16 (v1 v2 : w16) : ⟦GoOp GoDiv go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 / v2)
  remainder_uint16 (v1 v2 : w16) : ⟦GoOp GoRemainder go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 % v2)
  and_uint16 (v1 v2 : w16) : ⟦GoOp GoAnd go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uint16 (v1 v2 : w16) : ⟦GoOp GoOr go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint16 (v1 v2 : w16) : ⟦GoOp GoXor go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint16 (v1 v2 : w16) : ⟦GoOp GoShiftl go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint16 (v1 v2 : w16) : ⟦GoOp GoShiftr go.uint16, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  Uint16Semantics.div_uint16 Uint16Semantics.remainder_uint16 Uint16Semantics.and_uint16
  Uint16Semantics.or_uint16 Uint16Semantics.xor_uint16 Uint16Semantics.shiftl_uint16
  Uint16Semantics.shiftr_uint16 Uint16Semantics.complement_uint16 Uint16Semantics.neg_uint16
  Uint16Semantics.convert_int_to_uint16 Uint16Semantics.convert_int64_to_uint16
  Uint16Semantics.convert_int32_to_uint16 Uint16Semantics.convert_int16_to_uint16
  Uint16Semantics.convert_int8_to_uint16 Uint16Semantics.convert_uint_to_uint16
  Uint16Semantics.convert_uint64_to_uint16 Uint16Semantics.convert_uint32_to_uint16
  Uint16Semantics.convert_uint16_to_uint16 Uint16Semantics.convert_uint8_to_uint16
export Uint16Semantics (go_zero_val_uint16 comparable_uint16 underlying_uint16 go_eq_uint16
  le_uint16 lt_uint16 ge_uint16 gt_uint16 plus_uint16 sub_uint16 mul_uint16 div_uint16
  remainder_uint16 and_uint16 or_uint16 xor_uint16 shiftl_uint16 shiftr_uint16 complement_uint16 neg_uint16
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
  div_uint8 (v1 v2 : w8) : ⟦GoOp GoDiv go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 / v2)
  remainder_uint8 (v1 v2 : w8) : ⟦GoOp GoRemainder go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 % v2)
  and_uint8 (v1 v2 : w8) : ⟦GoOp GoAnd go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uint8 (v1 v2 : w8) : ⟦GoOp GoOr go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uint8 (v1 v2 : w8) : ⟦GoOp GoXor go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uint8 (v1 v2 : w8) : ⟦GoOp GoShiftl go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uint8 (v1 v2 : w8) : ⟦GoOp GoShiftr go.uint8, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  Uint8Semantics.remainder_uint8 Uint8Semantics.and_uint8 Uint8Semantics.or_uint8
  Uint8Semantics.xor_uint8 Uint8Semantics.shiftl_uint8 Uint8Semantics.shiftr_uint8
  Uint8Semantics.complement_uint8 Uint8Semantics.neg_uint8 Uint8Semantics.convert_int_to_uint8
  Uint8Semantics.convert_int64_to_uint8 Uint8Semantics.convert_int32_to_uint8
  Uint8Semantics.convert_int16_to_uint8 Uint8Semantics.convert_int8_to_uint8
  Uint8Semantics.convert_uint_to_uint8 Uint8Semantics.convert_uint64_to_uint8
  Uint8Semantics.convert_uint32_to_uint8 Uint8Semantics.convert_uint16_to_uint8
  Uint8Semantics.convert_uint8_to_uint8
export Uint8Semantics (go_zero_val_uint8 comparable_uint8 underlying_uint8 go_eq_uint8 le_uint8
  lt_uint8 ge_uint8 gt_uint8 plus_uint8 sub_uint8 mul_uint8 div_uint8 remainder_uint8 and_uint8
  or_uint8 xor_uint8 shiftl_uint8 shiftr_uint8 complement_uint8 neg_uint8 convert_int_to_uint8
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
* it occupies one heap location (`isPredeclared_uintptr`);
* arithmetic, bitwise operations and shifts are the unsigned `w64` ones (wrapping mod 2^64,
  `>>` logical), comparisons are unsigned (`uint.Z`), as for `uint64`;
* conversions to and from the other integer types (and from untyped integer constants) are
  those of `uint64`: identity to/from 64-bit types, truncation to narrower types, sign/zero
  extension from narrower signed/unsigned types.

Conversions between pointers (or `unsafe.Pointer`) and `uintptr` are deliberately *not*
modelled: there is no `Convert unsafe.Pointer go.uintptr` or `Convert go.uintptr unsafe.Pointer`
fact, so such a conversion is stuck (a program using one cannot be verified). A `uintptr` value
is thus only ever an integer, never the address of an object. -/
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
  div_uintptr (v1 v2 : w64) : ⟦GoOp GoDiv go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 / v2)
  remainder_uintptr (v1 v2 : w64) : ⟦GoOp GoRemainder go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 % v2)
  and_uintptr (v1 v2 : w64) : ⟦GoOp GoAnd go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 &&& v2)
  or_uintptr (v1 v2 : w64) : ⟦GoOp GoOr go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 ||| v2)
  xor_uintptr (v1 v2 : w64) : ⟦GoOp GoXor go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 ^^^ v2)
  shiftl_uintptr (v1 v2 : w64) : ⟦GoOp GoShiftl go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 <<< v2)
  shiftr_uintptr (v1 v2 : w64) : ⟦GoOp GoShiftr go.uintptr, (#v1, #v2)⟧ ⤳[under] #(v1 >>> v2)

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
  UintptrSemantics.div_uintptr UintptrSemantics.remainder_uintptr UintptrSemantics.and_uintptr
  UintptrSemantics.or_uintptr UintptrSemantics.xor_uintptr UintptrSemantics.shiftl_uintptr
  UintptrSemantics.shiftr_uintptr UintptrSemantics.complement_uintptr UintptrSemantics.neg_uintptr
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
  remainder_uintptr and_uintptr or_uintptr xor_uintptr shiftl_uintptr shiftr_uintptr
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

class Float64Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_float64 : TypeReprUnderlying go.float64 w64
  comparable_float64 : ⟦CheckComparable go.float64, #()⟧ ⤳[under] #()
  underlying_float64 : go.float64 ↓u go.float64
  go_eq_float64 : IsStrictlyComparable go.float64 w64
  le_float64 (v1 v2 : w64) : ⟦GoOp GoLe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Leb v1 v2)
  lt_float64 (v1 v2 : w64) : ⟦GoOp GoLt go.float64, (#v1, #v2)⟧
    ⤳[under] #(float64Leb v1 v2 && decide (v1 ≠ v2))
  ge_float64 (v1 v2 : w64) : ⟦GoOp GoGe go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Leb v2 v1)
  gt_float64 (v1 v2 : w64) : ⟦GoOp GoGt go.float64, (#v1, #v2)⟧
    ⤳[under] #(float64Leb v2 v1 && decide (v1 ≠ v2))
  plus_float64 (v1 v2 : w64) : ⟦GoOp GoPlus go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Add v1 v2)
  sub_float64 (v1 v2 : w64) : ⟦GoOp GoSub go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Sub v1 v2)
  mul_float64 (v1 v2 : w64) : ⟦GoOp GoMul go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Mul v1 v2)
  div_float64 (v1 v2 : w64) : ⟦GoOp GoDiv go.float64, (#v1, #v2)⟧ ⤳[under] #(float64Div v1 v2)

attribute [instance] Float64Semantics.go_zero_val_float64 Float64Semantics.comparable_float64
  Float64Semantics.underlying_float64 Float64Semantics.go_eq_float64 Float64Semantics.le_float64
  Float64Semantics.lt_float64 Float64Semantics.ge_float64 Float64Semantics.gt_float64
  Float64Semantics.plus_float64 Float64Semantics.sub_float64 Float64Semantics.mul_float64
  Float64Semantics.div_float64
export Float64Semantics (go_zero_val_float64 comparable_float64 underlying_float64 go_eq_float64
  le_float64 lt_float64 ge_float64 gt_float64 plus_float64 sub_float64 mul_float64 div_float64)

class Float32Semantics [GoSemanticsFunctions] : Prop where
  go_zero_val_float32 : TypeReprUnderlying go.float32 w32
  comparable_float32 : ⟦CheckComparable go.float32, #()⟧ ⤳[under] #()
  underlying_float32 : go.float32 ↓u go.float32
  go_eq_float32 : IsStrictlyComparable go.float32 w32
  le_float32 (v1 v2 : w32) : ⟦GoOp GoLe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Leb v1 v2)
  lt_float32 (v1 v2 : w32) : ⟦GoOp GoLt go.float32, (#v1, #v2)⟧
    ⤳[under] #(float32Leb v1 v2 && decide (v1 ≠ v2))
  ge_float32 (v1 v2 : w32) : ⟦GoOp GoGe go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Leb v2 v1)
  gt_float32 (v1 v2 : w32) : ⟦GoOp GoGt go.float32, (#v1, #v2)⟧
    ⤳[under] #(float32Leb v2 v1 && decide (v1 ≠ v2))
  plus_float32 (v1 v2 : w32) : ⟦GoOp GoPlus go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Add v1 v2)
  sub_float32 (v1 v2 : w32) : ⟦GoOp GoSub go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Sub v1 v2)
  mul_float32 (v1 v2 : w32) : ⟦GoOp GoMul go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Mul v1 v2)
  div_float32 (v1 v2 : w32) : ⟦GoOp GoDiv go.float32, (#v1, #v2)⟧ ⤳[under] #(float32Div v1 v2)

attribute [instance] Float32Semantics.go_zero_val_float32 Float32Semantics.comparable_float32
  Float32Semantics.underlying_float32 Float32Semantics.go_eq_float32 Float32Semantics.le_float32
  Float32Semantics.lt_float32 Float32Semantics.ge_float32 Float32Semantics.gt_float32
  Float32Semantics.plus_float32 Float32Semantics.sub_float32 Float32Semantics.mul_float32
  Float32Semantics.div_float32
export Float32Semantics (go_zero_val_float32 comparable_float32 underlying_float32 go_eq_float32
  le_float32 lt_float32 ge_float32 gt_float32 plus_float32 sub_float32 mul_float32 div_float32)

class PredeclaredSemantics [GoSemanticsFunctions] : Prop where
  alloc_predeclared (u : go.GoType) [H : IsPredeclared u] (v : val) :
    ⟦GoAlloc u, v⟧ ⤳[internalUnder] Alloc v
  load_predeclared (u : go.GoType) [H : IsPredeclared u] (l : val) :
    ⟦GoLoad u, l⟧ ⤳[internalUnder] Read l
  store_predeclared (u : go.GoType) [H : IsPredeclared u] (l v : val) :
    ⟦GoStore u, (l, v)⟧ ⤳[internalUnder] Store l v

  predeclared_underlying (t : go.GoType) (H : IsPredeclared t) : underlying t = t

  len_underlying (t : go.GoType) : functions len [t] = functions len [underlying t]
  cap_underlying (t : go.GoType) : functions cap [t] = functions cap [underlying t]
  clear_underlying (t : go.GoType) : functions clear [t] = functions clear [underlying t]
  copy_underlying (t : go.GoType) : functions copy [t] = functions copy [underlying t]
  delete_underlying (t : go.GoType) : functions delete [t] = functions delete [underlying t]
  make3_underlying (t : go.GoType) : functions make3 [t] = functions make3 [underlying t]
  make2_underlying (t : go.GoType) : functions make2 [t] = functions make2 [underlying t]
  make1_underlying (t : go.GoType) : functions make1 [t] = functions make1 [underlying t]

  min_unfold (n : Nat) (t : go.GoType) : FuncUnfold min (List.replicate n t) (min.impl t n)
  max_unfold (n : Nat) (t : go.GoType) : FuncUnfold max (List.replicate n t) (max.impl t n)
  panic_unfold : FuncUnfold panic [] panic.impl

  [unsafe_sem : unsafe.Semantics]

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

  type_repr_empty_struct : TypeReprUnderlying (go.StructType []) Unit

attribute [instance] PredeclaredSemantics.alloc_predeclared PredeclaredSemantics.load_predeclared
  PredeclaredSemantics.store_predeclared PredeclaredSemantics.min_unfold
  PredeclaredSemantics.max_unfold PredeclaredSemantics.panic_unfold PredeclaredSemantics.unsafe_sem
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
  PredeclaredSemantics.type_repr_empty_struct
export PredeclaredSemantics (alloc_predeclared load_predeclared store_predeclared
  predeclared_underlying len_underlying cap_underlying clear_underlying copy_underlying
  delete_underlying make3_underlying make2_underlying make1_underlying min_unfold max_unfold panic_unfold
  unsafe_sem comparable_bool go_eq_bool underlying_bool go_zero_val_bool go_unop_not_bool
  untypedInt_semantics int_semantics int64_semantics int32_semantics int16_semantics
  int8_semantics uint_semantics uint64_semantics uint32_semantics uint16_semantics
  uint8_semantics uintptr_semantics untypedFloat_semantics float64_semantics float32_semantics
  prophid_semantics
  comparable_string go_eq_string underlying_string plus_string go_zero_val_string
  underlying_untyped_nil convert_nil_pointer convert_nil_function convert_nil_slice
  convert_nil_chan convert_nil_map convert_nil_interface type_repr_empty_struct)

end defs
end go

end Perennial
