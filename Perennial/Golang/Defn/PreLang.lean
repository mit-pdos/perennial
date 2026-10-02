/-
Go types. Port of `new/golang/defn/prelang.v`.
-/
import Perennial.Std.ByteString

namespace Perennial
namespace go

abbrev identifier := go_string
abbrev type_name := go_string

mutual
/-- https://go.dev/ref/spec#Types (see the Rocq source for the conventions).
Parameter/result names are omitted from signatures so that `=` is Go type
identity. -/
inductive type where
  | Named : type_name → List type → type
  | ArrayType : Int → type → type
  | StructType : List field_decl → type
  | PointerType : type → type
  | FunctionType : signature → type
  | InterfaceType : List interface_elem → type
  | SliceType : type → type
  | MapType : type → type → type
  | ChannelType : chan_dir → type → type
  | UntypedType : type_name → type

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
  | MethodElem : identifier → signature → interface_elem
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

def string_to_go_string (s : String) : go_string := Perennial.string_to_go_string s

/-- Rocq `type_to_string`, used for comparisons and method lookups. -/
def type_to_string : type → go_string
  | .Named n _ => n
  | .ArrayType n elem => go!"[" ++ string_to_go_string (toString n) ++ go!"]" ++ type_to_string elem
  | _ => []

def bool : type := .Named go!"bool" []

end go
end Perennial
