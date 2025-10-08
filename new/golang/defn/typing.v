From stdpp Require Export pretty.
From New.golang.defn Require Export intoval.
From Perennial Require Import base.

Module go.
Definition identifier := go_string.
Definition type_name := go_string.

(** https://go.dev/ref/spec#Types *)
Inductive type :=
| Named : type_name → type_args → _
| TypeLit : type_lit → _

with type_args := | TypeArgs : list type → _

with type_lit :=
| ArrayType : Z → type → _
| StructType : list field_decl → _
| PointerType : type → _
| FunctionType : signature → _
| InterfaceType : (list interface_elem) → _
| SliceType : type → _
| MapType : type → type → _
| ChannelType : option bool → type → _

with field_decl :=
| FieldDecl : (list go_string) → type → _
| EmbeddedField : bool → go_string → type_args → _

with signature := | Signature : parameters → result → _

with parameters := | ParameterList : (list parameter_decl) → _

with parameter_decl := | ParameterDecl : (list identifier) → (* variadic *) bool → _

with result :=
| ResultParameters : parameters → _
| ResultType : type → _

with interface_elem :=
| MethodElem : identifier → signature → _
| TypeElem : list type_term → _

with type_term := | TypeTerm (type : type) | TypeTermUnderlying (type : type).

Global Coercion TypeLit : type_lit >-> type.

Definition string_to_go_string (s : string) : go_string :=
  byte_to_w8 <$> String.list_byte_of_string s.

Definition go_string_to_string (gs : go_string) : string :=
  String.string_of_list_byte $ w8_to_byte <$> gs.

Definition pretty_go `{!Pretty A} (a : A) : go_string :=
  string_to_go_string (pretty a).

(* Convert to string for comparison purposes and method lookups. *)
Fixpoint type_to_string (t : type) : go_string :=
  match t with
  | Named n args => n
  | ArrayType n elem => ("[" ++ pretty_go n ++ "]" ++ type_to_string elem)%go
  | _ => ""%go
  end.
End go.

(** FIXME: document this. Convenient for stating assumptions. Allows for
    mutually recursive types in which e.g. the pointer element is not erased. *)
Class NamedUnderlyingTypes :=
  {
    named_to_underlying : go_string -> (list go.type) → go.type
  }.

Definition to_underlying `{!NamedUnderlyingTypes} (t : go.type) : go.type :=
  match t with
  | go.Named n (go.TypeArgs args) => (named_to_underlying n args)
  | _ => t
  end.

Global Coercion go.TypeLit : go.type_lit >-> go.type.
