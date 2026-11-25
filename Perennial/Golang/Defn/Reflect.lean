/-
The reflection primitives: the instructions that `internal/reflectcore`'s primitive stubs use
(`FuncResolveAt`, `ConvertAt`, `FieldRefAt`, `ArraySliceAt`, `EqNilAt`, `PointerOfAt`,
`TypeQuery`). Each is an existing operation with its types read from interface values' dynamic
types. A type `T` is passed as its token `any((*T)(nil))` (`tok`); a primitive that reads only
the type of its argument also accepts any `any((*T)(p))`. A primitive is stuck at the arguments
that no rule covers.
-/
module

public import Perennial.Golang.Defn.Interface
public import Perennial.Golang.Defn.Plain

@[expose] public section

namespace Perennial

namespace go
section defs
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]

/-- The token of `t`: the Go value `any((*t)(nil))`. -/
def tok (t : go.GoType) : GoInterface := interface.mkOk (go.PointerType t) #null

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

/-- `FuncResolveAt`'s argument for the dispatch interfaces `is`: `#i` for one, right-nested pairs
for several. -/
def dispatchArgs : List GoInterfaceOk → val
  | [] => #()
  | [i] => #(GoInterface.ok i)
  | i :: is => PairV #(GoInterface.ok i) (dispatchArgs is)

/-- `reflect.Kind` of an underlying type. -/
noncomputable def kindOf (u : go.GoType) : Option Nat :=
  match u with
  | go.ArrayType _ _ => some 17
  | go.ChannelType _ _ => some 18
  | go.FunctionType _ => some 19
  | go.InterfaceType _ => some 20
  | go.MapType _ _ => some 21
  | go.PointerType _ => some 22
  | go.SliceType _ => some 23
  | go.StructType _ => some 25
  | _ => ([(go.bool, 1), (go.int, 2), (go.int8, 3), (go.int16, 4), (go.int32, 5), (go.int64, 6),
      (go.uint, 7), (go.uint8, 8), (go.uint16, 9), (go.uint32, 10), (go.uint64, 11),
      (go.uintptr, 12), (go.float32, 13), (go.float64, 14), (go.complex64, 15),
      (go.complex128, 16), (go.string, 24), («unsafe».Pointer, 26)].find?
        fun p => decide (p.1 = u)).map (·.2)

/-- `reflect.ChanDir`: `RecvDir` 1, `SendDir` 2, `BothDir` 3. -/
def chanDirOf : go.ChanDir → Nat
  | .recvonly => 1
  | .sendonly => 2
  | .sendrecv => 3

/-- `l[i]` for `0 ≤ i`. -/
def listAt {α : Type} (l : List α) (i : Int) : Option α :=
  if 0 ≤ i then l[i.toNat]? else none

/-- `reflect.StructField.Name`: goose names the blank fields `_#k`. -/
def fieldNameOf (fd : go.field_decl) : GoString :=
  if isBlankField (fieldDeclName fd) then go!"_" else fieldDeclName fd

def isEmbeddedField : go.field_decl → Bool
  | go.field_decl.Field _ _ _ => false
  | go.field_decl.Embedded _ _ _ => true

/-- `TypeQuery q`'s result for the type `t` and the index `i`. Ints are Go `int`s, types tokens. -/
noncomputable def typeQuery (q : TypeQ) (t : go.GoType) (i : Int) : Option val :=
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
  | .arrayOf, _ =>
    open Classical in
    if 0 ≤ i ∧ (i ≤ 1 ∨ ∃ s, IsPlain t s ∧ i * s < 2 ^ 64) then some #(tok (go.ArrayType i t))
    else none
  | .underlying, u => some #(tok u)
  | .identByName, _ => some #(identByName t)
  | _, _ => none

/-- The underlying types at which `EqNilAt` compares with `nil`. -/
class inductive IsNilable : go.GoType → Prop
  | pointer (e : go.GoType) : IsNilable (go.PointerType e)
  | slice (e : go.GoType) : IsNilable (go.SliceType e)
  | map (k v : go.GoType) : IsNilable (go.MapType k v)
  | chan (d : go.ChanDir) (e : go.GoType) : IsNilable (go.ChannelType d e)
  | func (sig : go.signature) : IsNilable (go.FunctionType sig)
  | unsafePointer : IsNilable «unsafe».Pointer

attribute [instance] IsNilable.pointer IsNilable.slice IsNilable.map IsNilable.chan IsNilable.func
  IsNilable.unsafePointer

class ReflectSemantics : Prop where
  /-- `FuncResolve f ts` for the type arguments `ts` that the shapes `shs` give for the dispatch
  interfaces `is`. Not an instance: its premise is not found by instance search. -/
  func_resolve_at_step (shs : List Shape) (f : GoString) (is : List GoInterfaceOk)
      (ts : List go.GoType) (h : shapesArgs shs (is.map (·.ty)) = some ts) :
    ⟦FuncResolveAt shs f, dispatchArgs is⟧ ⤳ #(functions f ts)
  /-- `any(U(x))` for `x : t` and a token of `U`. -/
  convert_at_step {t u : go.GoType} (v : val) (l : Loc) :
    ⟦ConvertAt, (#(interface.mkOk t v), #(interface.mkOk (go.PointerType u) #l))⟧ ⤳
      (if isInterfaceType (underlying u) then
        (if typeSetContains t u then #(interface.mkOk t v) else Panic "not modelled")
      else Convert u go.any (Convert t u (Val v)))
  /-- `any(&(*p).f)` for the `i`th field `f` of `*p`. Not an instance: its premises are not
  found by instance search.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S2: `Value.Field`/`FieldByName`. -/
  field_ref_at_step {s : go.GoType} {fs : List go.field_decl} [s ↓u go.StructType fs] (l : Loc)
      (i : w64) (fd : go.field_decl) (hl : l ≠ null) (hi : 0 ≤ sint.Z i)
      (hfd : fs[sint.nat i]? = some fd) (hblank : isBlankField (fieldDeclName fd) = false) :
    ⟦FieldRefAt, (#(interface.mkOk (go.PointerType s) #l), #i)⟧ ⤳
      Convert (go.PointerType (fieldDeclType fd)) go.any
        (StructFieldRef s (fieldDeclName fd) (Val #l))
  /-- `any((*p)[:])` for a pointer `p` to an array. Not an instance: its premise is not found by
  instance search.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S2: `Value.Index` on arrays. -/
  array_slice_at_step {a e : go.GoType} {n : Int} [a ↓u go.ArrayType n e] (l : Loc)
      (hl : l ≠ null) :
    ⟦ArraySliceAt, #(interface.mkOk (go.PointerType a) #l)⟧ ⤳
      Convert (go.SliceType e) go.any (Slice (go.ArrayType n e) (#l, #(W64 0), #(W64 n)))
  /-- `x == nil` at `x`'s dynamic type. -/
  eq_nil_at_step {t u : go.GoType} [t ↓u u] [IsNilable u] (v : val) {z : val}
      [⟦GoZeroVal t, #()⟧ ⤳ Val z] :
    ⟦EqNilAt, #(interface.mkOk t v)⟧ ⤳ GoOp GoEquals t (Val v, Val z)
  /-- `unsafe.Pointer` of a pointer.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S5: `DeepEqual`. -/
  pointer_of_at_ptr {t e : go.GoType} [t ↓u go.PointerType e] (l : Loc) :
    ⟦PointerOfAt, #(interface.mkOk t #l)⟧ ⤳ #l
  /-- An `unsafe.Pointer` itself.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S5: `DeepEqual`. -/
  pointer_of_at_unsafe {t : go.GoType} [t ↓u «unsafe».Pointer] (l : Loc) :
    ⟦PointerOfAt, #(interface.mkOk t #l)⟧ ⤳ #l
  /-- A map's identity, its cell.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S5: `DeepEqual`. -/
  pointer_of_at_map {t k v : go.GoType} [t ↓u go.MapType k v] (m : GoMap) :
    ⟦PointerOfAt, #(interface.mkOk t #m)⟧ ⤳ #m
  /-- A channel's identity.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S5: `DeepEqual`. -/
  pointer_of_at_chan {t e : go.GoType} {d : go.ChanDir} [t ↓u go.ChannelType d e] (c : GoChan) :
    ⟦PointerOfAt, #(interface.mkOk t #c)⟧ ⤳ #c
  /-- A nil slice's data pointer.
  Not yet used by the reflect Go model (`goose/model/overlay`);
  planned for S5: `DeepEqual`. -/
  pointer_of_at_slice_nil {t e : go.GoType} [t ↓u go.SliceType e] :
    ⟦PointerOfAt, #(interface.mkOk t #slice.nil)⟧ ⤳ #null
  /-- The data pointer of a slice of positive capacity. Not an instance: its premise is not found
  by instance search.
  Not yet used by the reflect Go model (`goose/model/overlay`); planned for S5: `DeepEqual`. -/
  pointer_of_at_slice {t e : go.GoType} [t ↓u go.SliceType e] (s : GoSlice)
      (h : 0 < uint.Z s.cap) :
    ⟦PointerOfAt, #(interface.mkOk t #s)⟧ ⤳ #s.ptr
  /-- The fact `q` about the type `t` of a token. Not an instance: its premise is not found by
  instance search. -/
  type_query_step (q : TypeQ) (t : go.GoType) (l : Loc) (i : w64) (v : val)
      (h : typeQuery q t (sint.Z i) = some v) :
    ⟦TypeQuery q, (#(interface.mkOk (go.PointerType t) #l), #i)⟧ ⤳ Val v

attribute [instance] ReflectSemantics.convert_at_step ReflectSemantics.eq_nil_at_step
  ReflectSemantics.pointer_of_at_ptr ReflectSemantics.pointer_of_at_unsafe
  ReflectSemantics.pointer_of_at_map ReflectSemantics.pointer_of_at_chan
  ReflectSemantics.pointer_of_at_slice_nil
export ReflectSemantics (func_resolve_at_step convert_at_step field_ref_at_step
  array_slice_at_step eq_nil_at_step pointer_of_at_ptr pointer_of_at_unsafe pointer_of_at_map
  pointer_of_at_chan pointer_of_at_slice_nil pointer_of_at_slice type_query_step)

end defs
end go

end Perennial
