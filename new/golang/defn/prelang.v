(* pre lang.v *)

From stdpp Require Export pretty countable.
From Perennial Require Export base ByteString.

Definition go_string := byte_string.
Delimit Scope byte_string_scope with go.
Bind Scope byte_string_scope with go_string.
(* NOTE: this causes W8 values to be printed using the byte notation set up in
ByteString.v *)
(* Delimit Scope byte_char_scope with go_byte. *)

Module go.
Definition identifier := go_string.
Definition type_name := go_string.

(** https://go.dev/ref/spec#Types
    When a type would otherwise have a single constructor with a single
    argument, the type is omitted and its single input is inlined. Also, places
    where Go syntax allows for `func (a, b uint64)` are required to be `func (a
    uint64, b uint64)` here (e.g. field or parameter decls).
 *)
Inductive type :=
| Named : type_name → list type (* type args *) → _
| TypeLit : type_lit → _

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
| FieldDecl : go_string → type → _
| EmbeddedField : go_string → type → _

with signature := | Signature : list parameter_decl → result → _

with parameter_decl := | ParameterDecl : identifier → type → (* variadic *) bool → _

with result :=
| ResultParameters : list parameter_decl → _
| ResultType : type → _

with interface_elem :=
| MethodElem : identifier → signature → _
| TypeElem : list type_term → _

with type_term := | TypeTerm (type : type) | TypeTermUnderlying (type : type).

Global Instance type_eq_dec : EqDecision type.
Proof. Admitted.

Global Instance type_countable : Countable type.
Proof. Admitted.

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

Global Coercion go.TypeLit : go.type_lit >-> go.type.

Inductive go_op : Type :=
| AngelicExit

| GoLoad (t : go.type)
| GoStore (t : go.type)
| GoAlloc (t : go.type)

| FuncCall (func_id : go_string)
| MethodCall (t : go.type) (m : go_string)

| PackageInitCheck (pkg_name : go_string)
| PackageInitMark (pkg_name : go_string)

| GlobalVarAddr (var_name : go_string)

| StructFieldRef (t : go.type) (f : go_string)
| StructFieldGet (f : go_string)
| StructFieldSet (f : go_string)

| Len
| Cap 
| SliceIndexRef (t : go.type) (* int *)
| Make (t : go.type) (* can do slice, map, etc. *)

| Slice

| ArrayElemRef (t : go.type) (* int *).

(*
TODO:
[ ] Go interfaces
[ ] Define semantics for other ops.
 *)
