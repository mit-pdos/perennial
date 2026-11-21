/-
Go types.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace go

abbrev Identifier := GoString
abbrev TypeName := GoString

mutual
/-- https://go.dev/ref/spec#Types.
Parameter/result names are omitted from signatures so that `=` is Go type
identity. -/
inductive GoType where
  | Named : TypeName → List GoType → GoType
  | ArrayType : Int → GoType → GoType
  | StructType : List field_decl → GoType
  | PointerType : GoType → GoType
  | FunctionType : signature → GoType
  | InterfaceType : List InterfaceElem → GoType
  | SliceType : GoType → GoType
  | MapType : GoType → GoType → GoType
  | ChannelType : ChanDir → GoType → GoType
  | UntypedType : TypeName → GoType

inductive ChanDir where
  | sendrecv
  | sendonly
  | recvonly

/-- A field of a struct type: its name, its type and, for a field with a non-empty tag
(spec, "Struct types": "A field declaration may be followed by an optional string literal
tag"), the tag. Tags are part of an unnamed struct type's identity (spec, "Type identity":
"Two struct types are identical if they have the same sequence of fields, and if
corresponding fields have the same names, and identical types, and identical tags"), so
``struct{A int `json:"a"`}`` and `struct{A int}` are different `GoType`s, as they are in Go.
A field without a tag is `FieldDecl`/`EmbeddedField`, one with a tag
`TaggedField`/`TaggedEmbeddedField` (never with the empty tag: goose emits those only for a
non-empty one). The semantics of field access, zero values, allocation, loads, stores and
comparison look fields up by name and ignore the tag, as Go's do. The underlying type of a
defined struct type is written without its tags: a defined type's identity is its name, and
what the model does with its underlying type (field steps, conversions, which in Go ignore
tags) does not depend on them. -/
inductive field_decl where
  | FieldDecl : GoString → GoType → field_decl
  | EmbeddedField : GoString → GoType → field_decl
  | TaggedField : GoString → GoType → GoString → field_decl
  | TaggedEmbeddedField : GoString → GoType → GoString → field_decl

inductive signature where
  | Signature : List GoType → Bool → List GoType → signature

inductive InterfaceElem where
  | MethodElem : Identifier → signature → InterfaceElem
  | TypeElem : List type_term → InterfaceElem

inductive type_term where
  | TypeTerm (type : GoType)
  | TypeTermUnderlying (type : GoType)
end

-- The deriving handler does not support nested
-- mutual inductives, so we use classical decidability.
noncomputable instance : DecidableEq GoType := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq signature := fun a b => Classical.propDecidable (a = b)


instance : Inhabited GoType := ⟨.Named go!"any" []⟩

-- Constructors are available directly in `go` (`go.Named`, `go.FieldDecl`, ...).
export GoType (Named ArrayType StructType PointerType FunctionType InterfaceType SliceType MapType
  ChannelType UntypedType)
export ChanDir (sendrecv sendonly recvonly)
export field_decl (FieldDecl EmbeddedField TaggedField TaggedEmbeddedField)
export signature (Signature)
export InterfaceElem (MethodElem TypeElem)
export type_term (TypeTerm TypeTermUnderlying)

def stringToGoString (s : String) : GoString := Perennial.stringToGoString s

/-- A string name of a type, used for comparisons and method lookups. -/
def typeToString : GoType → GoString
  | .Named n _ => n
  | .ArrayType n elem => go!"[" ++ stringToGoString (toString n) ++ go!"]" ++ typeToString elem
  | _ => []

def bool : GoType := .Named go!"bool" []

end go
end Perennial
