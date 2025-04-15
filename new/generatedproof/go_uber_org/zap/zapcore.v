(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

Require Export New.code.go_uber_org.zap.zapcore.
Module zapcore.
Axiom falso : False.

Module FieldType.
Section def.
Context `{ffi_syntax}.
Definition t := w8.
End def.
End FieldType.
Module Field.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Key' : go_string;
  Type' : FieldType.t;
  Integer' : w64;
  String' : go_string;
  Interface' : interface.t;
}.
End def.
End Field.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Field `{ffi_syntax}: Settable _ :=
  settable! Field.mk < Field.Key'; Field.Type'; Field.Integer'; Field.String'; Field.Interface' >.
Global Instance into_val_Field `{ffi_syntax} : IntoVal Field.t.
Admitted.

Global Instance into_val_typed_Field `{ffi_syntax} : IntoValTyped Field.t zapcore.Field :=
{|
  default_val := Field.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Field_Key `{ffi_syntax} : IntoValStructField "Key" zapcore.Field Field.Key'.
Admitted.

Global Instance into_val_struct_field_Field_Type `{ffi_syntax} : IntoValStructField "Type" zapcore.Field Field.Type'.
Admitted.

Global Instance into_val_struct_field_Field_Integer `{ffi_syntax} : IntoValStructField "Integer" zapcore.Field Field.Integer'.
Admitted.

Global Instance into_val_struct_field_Field_String `{ffi_syntax} : IntoValStructField "String" zapcore.Field Field.String'.
Admitted.

Global Instance into_val_struct_field_Field_Interface `{ffi_syntax} : IntoValStructField "Interface" zapcore.Field Field.Interface'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Field `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Key' Type' Integer' String' Interface':
  PureWp True
    (struct.make #zapcore.Field (alist_val [
      "Key" ::= #Key';
      "Type" ::= #Type';
      "Integer" ::= #Integer';
      "String" ::= #String';
      "Interface" ::= #Interface'
    ]))%struct
    #(Field.mk Key' Type' Integer' String' Interface').
Admitted.


Global Instance Field_struct_fields_split dq l (v : Field.t) :
  StructFieldsSplit dq l v (
    "HKey" ∷ l ↦s[zapcore.Field :: "Key"]{dq} v.(Field.Key') ∗
    "HType" ∷ l ↦s[zapcore.Field :: "Type"]{dq} v.(Field.Type') ∗
    "HInteger" ∷ l ↦s[zapcore.Field :: "Integer"]{dq} v.(Field.Integer') ∗
    "HString" ∷ l ↦s[zapcore.Field :: "String"]{dq} v.(Field.String') ∗
    "HInterface" ∷ l ↦s[zapcore.Field :: "Interface"]{dq} v.(Field.Interface')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined zapcore :=
{|
  is_pkg_defined := is_global_definitions zapcore var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End zapcore.
