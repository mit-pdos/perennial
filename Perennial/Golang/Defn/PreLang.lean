/-
Go types. Port of `new/golang/defn/prelang.v`.
-/
import Perennial.Std.ByteString

namespace Perennial
namespace go

abbrev Identifier := go_string
abbrev TypeName := go_string

mutual
/-- https://go.dev/ref/spec#Types (see the Rocq source for the conventions).
Parameter/result names are omitted from signatures so that `=` is Go type
identity. -/
inductive type where
  | Named : TypeName → List type → type
  | ArrayType : Int → type → type
  | StructType : List field_decl → type
  | PointerType : type → type
  | FunctionType : signature → type
  | InterfaceType : List interface_elem → type
  | SliceType : type → type
  | MapType : type → type → type
  | ChannelType : chan_dir → type → type
  | UntypedType : TypeName → type

inductive chan_dir where
  | sendrecv
  | sendonly
  | recvonly

inductive field_decl where
  | FieldDecl : go_string → type → field_decl
  | EmbeddedField : go_string → type → field_decl

inductive signature where
  | Signature : List type → Bool → List type → signature

inductive interface_elem where
  | MethodElem : Identifier → signature → interface_elem
  | TypeElem : List type_term → interface_elem

inductive type_term where
  | TypeTerm (type : type)
  | TypeTermUnderlying (type : type)
end

-- Rocq admits these instances. The deriving handler does not support nested
-- mutual inductives, so we use classical decidability.
noncomputable instance : DecidableEq type := fun a b => Classical.propDecidable (a = b)
noncomputable instance : DecidableEq signature := fun a b => Classical.propDecidable (a = b)


instance : Inhabited type := ⟨.Named go!"any" []⟩

-- Rocq constructors live directly in `Module go` (`go.Named`, `go.FieldDecl`, ...).
export type (Named ArrayType StructType PointerType FunctionType InterfaceType SliceType MapType
  ChannelType UntypedType)
export chan_dir (sendrecv sendonly recvonly)
export field_decl (FieldDecl EmbeddedField)
export signature (Signature)
export interface_elem (MethodElem TypeElem)
export type_term (TypeTerm TypeTermUnderlying)

def stringToGoString (s : String) : go_string := Perennial.stringToGoString s

/-- Rocq `typeToString`, used for comparisons and method lookups. -/
def typeToString : type → go_string
  | .Named n _ => n
  | .ArrayType n elem => go!"[" ++ stringToGoString (toString n) ++ go!"]" ++ typeToString elem
  | _ => []

def bool : type := .Named go!"bool" []

end go
end Perennial
