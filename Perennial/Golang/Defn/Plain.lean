/-
Plain types and their layout (`docs/design/unsafe-memory.md`, R1, and
`docs/design/unsafe-memory-rules-plan.md`, option (C)).

A plain type is one whose values are only bytes: the integer and float types
(`IsPlainScalar`), arrays of at least one plain element, and non-empty structs of plain,
non-blank fields laid out with no padding, and named types of these. `PlainLayout t size align`
gives its size and alignment in gc's layout on linux/amd64; `PlainFieldOffset` a field's offset.

For a plain type, element and field addresses are concrete at positive addresses
(`PlainSemantics`): `arrayIndexRef V i l = l + i·size` and `structFieldRef V f l = l + offset`.
Element and field addresses are keyed by the Lean representation `V`; the axioms are consistent
because every plain Go type with representation `V` has the same layout (`V` fixes each scalar's
width, an array's length and element representation, and a struct's fields), and because a
function that moves a non-null address by `i·size` places along the non-zero integers, skipping
`0`, satisfies `arrayIndexRef_null_inv`, `arrayIndexRef_add` and `arrayIndexRef_0` and is
`l + i·size` for `0 < l` and `0 ≤ i`.
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

namespace go
section defs
variable [GooseExts] [GoSemanticsFunctions]

/-- The name of a field. -/
def fieldDeclName : go.field_decl → GoString
  | go.FieldDecl n _ => n
  | go.EmbeddedField n _ => n

/-- The type of a field. -/
def fieldDeclType : go.field_decl → go.GoType
  | go.FieldDecl _ t => t
  | go.EmbeddedField _ t => t

mutual
/-- `PlainLayout t size align`: `t` is plain, of `size` bytes and alignment `align`. -/
inductive PlainLayout : go.GoType → Nat → Nat → Prop
  | scalar (t : go.GoType) (w : Nat) : IsPlainScalar t w → PlainLayout t w w
  | array (n : Int) (e : go.GoType) (s a : Nat) :
      PlainLayout e s a → 1 ≤ n → PlainLayout (go.ArrayType n e) (n.toNat * s) a
  | struct (fds : List go.field_decl) (s a : Nat) :
      fds ≠ [] → PlainFields fds 0 s a → a ∣ s → PlainLayout (go.StructType fds) s a
  | named (t u : go.GoType) (s a : Nat) :
      underlying t = u → t ≠ u → PlainLayout u s a → PlainLayout t s a

/-- `PlainFields fds off stop align`: the fields `fds`, laid out from offset `off` with no
padding (each field's alignment divides its offset), end at `stop`; `align` is the largest
alignment among them, `1` for none. -/
inductive PlainFields : List go.field_decl → Nat → Nat → Nat → Prop
  | nil (off : Nat) : PlainFields [] off off 1
  | cons (fd : go.field_decl) (fds : List go.field_decl) (off s a stop a' : Nat) :
      PlainLayout (fieldDeclType fd) s a → isBlankField (fieldDeclName fd) = false → a ∣ off →
      PlainFields fds (off + s) stop a' → PlainFields (fd :: fds) off stop (Nat.max a a')
end

/-- `PlainFieldOffset fds base f off`: laying out `fds` from `base` with no padding, the first
field named `f` is at `off`. -/
inductive PlainFieldOffset : List go.field_decl → Nat → GoString → Nat → Prop
  | here (fd : go.field_decl) (fds : List go.field_decl) (base : Nat) :
      PlainFieldOffset (fd :: fds) base (fieldDeclName fd) base
  | there (fd : go.field_decl) (fds : List go.field_decl) (base s a : Nat) (f : GoString)
      (off : Nat) :
      fieldDeclName fd ≠ f → PlainLayout (fieldDeclType fd) s a →
      PlainFieldOffset fds (base + s) f off → PlainFieldOffset (fd :: fds) base f off

/-- `IsPlain t size`: `t` is plain, of `size` bytes. A `class` so that `[IsPlain t s]` premises
are found by typeclass search; a proof about a plain type provides the instance from a
`PlainLayout`. -/
class IsPlain (t : go.GoType) (size : outParam Nat) : Prop where
  is_plain : ∃ align, PlainLayout t size align

end defs

class PlainSemantics [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] :
    Prop where
  /-- A view of memory as a plain `*T`: its loads and stores check the cells. A conversion to a
  pointer to a non-plain type has no rule (stuck). -/
  convert_unsafe_to_pointer (elem : go.GoType) (s : Nat) [IsPlain elem s] (l : Loc) :
    ⟦Convert «unsafe».Pointer (go.PointerType elem), #l⟧ ⤳[under] #l
  /-- `unsafe.Add(p, n)`: no check that the result is in an allocation
  (`docs/KNOWN_LIMITATIONS.md`). -/
  add_unfold (it : go.GoType) [IsInteger it] :
    FuncUnfold «unsafe».Add [it]
      (λ: "p" "n", "p" +⟨go.PointerType go.uint8⟩ Convert it go.int64 "n" : val)
  slice_unfold (elem it : go.GoType) [IsInteger it] :
    FuncUnfold «unsafe».Slice [elem, it]
      (λ: "p" "n", InternalUnsafeSlice elem ("p", Convert it go.int64 "n") : val)
  /-- `runtime.unsafeslice`: no check that the slice is in an allocation
  (`docs/KNOWN_LIMITATIONS.md`). -/
  internal_unsafe_slice (elem : go.GoType) (s : Nat) [IsPlain elem s] (l : Loc) (n : w64) :
    ⟦InternalUnsafeSlice elem, (#l, #n)⟧ ⤳
      (if sint.Z n < 0 then Panic "unsafe.Slice: len out of range"
       else if l = null then
         (if sint.Z n = 0 then #slice.nil else Panic "unsafe.Slice: ptr is nil and len is not zero")
       else if 2 ^ 64 < l.addr + sint.Z n * s then Panic "unsafe.Slice: len out of range"
       else #(slice.mk l n n))
  arrayIndexRef_plain (e : go.GoType) (V : Type) [ZeroVal V] [TypeRepr e V] (s a : Nat) (i : Int)
      (l : Loc) :
    PlainLayout e s a → 0 < l.addr → 0 ≤ i → arrayIndexRef V i l = l +ₗ i * s
  structFieldRef_plain (fds : List go.field_decl) (V : Type) [ZeroVal V]
      [TypeRepr (go.StructType fds) V] (s a : Nat) (f : GoString) (off : Nat) (l : Loc) :
    PlainLayout (go.StructType fds) s a → PlainFieldOffset fds 0 f off → 0 < l.addr →
      structFieldRef V f l = l +ₗ off

attribute [instance] PlainSemantics.convert_unsafe_to_pointer PlainSemantics.add_unfold
  PlainSemantics.slice_unfold PlainSemantics.internal_unsafe_slice

export PlainSemantics (arrayIndexRef_plain structFieldRef_plain convert_unsafe_to_pointer
  add_unfold slice_unfold internal_unsafe_slice)

end go

end Perennial
