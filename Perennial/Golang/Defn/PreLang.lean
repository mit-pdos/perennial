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

/-- A field declaration of a struct type (spec, "Struct types": `FieldDecl = (IdentifierList
Type | EmbeddedField) [ Tag ]`): `Field name type tag` or `Embedded name type tag`, a field
without a tag having the empty tag (Go does not tell an absent tag from `""`: the spec's
"Struct types" makes the tag the field's string literal, and `go/types` reports `""` for both,
so `struct{A int ""}` and `struct{A int}` are one type; an `Option` would give it two
representations). `FieldDecl name type` and `EmbeddedField name type` (below) are the
untagged ones, which goose writes for every field without a tag.

Tags are part of a struct type's identity (spec, "Type identity": "Two struct types are
identical if they have the same sequence of fields, and if corresponding fields have the same
names, and identical types, and identical tags"), so ``struct{A int `json:"a"`}``,
`struct{A int}` and ``struct{A int `json:"b"`}`` are three different `GoType`s, as in Go. The
semantics of field access, zero values, allocation, loads, stores and comparison look fields up
by name and ignore the tag, as Go's do.

goose writes the tags of an unnamed struct type's fields only. A defined struct type's
underlying type is written without them: a defined type's identity is its name, and its field
steps do not depend on them. So a conversion between struct types that Go allows only by
ignoring tags (spec, "Conversions": "ignoring struct tags"), such as `T(x)` from a tagged
unnamed struct to a defined type `T`, has no rule and is stuck: the model is less defined than
Go there, never more (`KNOWN_LIMITATIONS.md`). -/
inductive field_decl where
  | Field (name : GoString) (type : GoType) (tag : GoString) : field_decl
  | Embedded (name : GoString) (type : GoType) (tag : GoString) : field_decl

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

/-- A field without a tag (its tag is empty): what goose writes for the usual field. -/
@[match_pattern] abbrev field_decl.FieldDecl (name : GoString) (type : GoType) : field_decl :=
  .Field name type []

/-- An embedded field without a tag (its tag is empty). -/
@[match_pattern] abbrev field_decl.EmbeddedField (name : GoString) (type : GoType) :
    field_decl :=
  .Embedded name type []

-- Constructors are available directly in `go` (`go.Named`, `go.FieldDecl`, ...).
export GoType (Named ArrayType StructType PointerType FunctionType InterfaceType SliceType MapType
  ChannelType UntypedType)
export ChanDir (sendrecv sendonly recvonly)
export field_decl (FieldDecl EmbeddedField)
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
