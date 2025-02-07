(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.go_etcd_io.etcd.api.v3.mvccpb.
Require Export New.golang.theory.

Module mvccpb.
Axiom falso : False.

Module Event_EventType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End Event_EventType.
Module KeyValue.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Key' : slice.t;
  CreateRevision' : w64;
  ModRevision' : w64;
  Version' : w64;
  Value' : slice.t;
  Lease' : w64;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End KeyValue.


Global Instance settable_KeyValue `{ffi_syntax}: Settable _ :=
  settable! KeyValue.mk < KeyValue.Key'; KeyValue.CreateRevision'; KeyValue.ModRevision'; KeyValue.Version'; KeyValue.Value'; KeyValue.Lease'; KeyValue.XXX_NoUnkeyedLiteral'; KeyValue.XXX_unrecognized'; KeyValue.XXX_sizecache' >.
Global Instance into_val_KeyValue `{ffi_syntax} : IntoVal KeyValue.t.
Admitted.

Global Instance into_val_typed_KeyValue `{ffi_syntax} : IntoValTyped KeyValue.t mvccpb.KeyValue :=
{|
  default_val := KeyValue.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_KeyValue_Key `{ffi_syntax} : IntoValStructField "Key" mvccpb.KeyValue KeyValue.Key'.
Admitted.

Global Instance into_val_struct_field_KeyValue_CreateRevision `{ffi_syntax} : IntoValStructField "CreateRevision" mvccpb.KeyValue KeyValue.CreateRevision'.
Admitted.

Global Instance into_val_struct_field_KeyValue_ModRevision `{ffi_syntax} : IntoValStructField "ModRevision" mvccpb.KeyValue KeyValue.ModRevision'.
Admitted.

Global Instance into_val_struct_field_KeyValue_Version `{ffi_syntax} : IntoValStructField "Version" mvccpb.KeyValue KeyValue.Version'.
Admitted.

Global Instance into_val_struct_field_KeyValue_Value `{ffi_syntax} : IntoValStructField "Value" mvccpb.KeyValue KeyValue.Value'.
Admitted.

Global Instance into_val_struct_field_KeyValue_Lease `{ffi_syntax} : IntoValStructField "Lease" mvccpb.KeyValue KeyValue.Lease'.
Admitted.

Global Instance into_val_struct_field_KeyValue_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" mvccpb.KeyValue KeyValue.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_KeyValue_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" mvccpb.KeyValue KeyValue.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_KeyValue_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" mvccpb.KeyValue KeyValue.XXX_sizecache'.
Admitted.

Global Instance wp_struct_make_KeyValue `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Key' CreateRevision' ModRevision' Version' Value' Lease' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make mvccpb.KeyValue (alist_val [
      "Key" ::= #Key';
      "CreateRevision" ::= #CreateRevision';
      "ModRevision" ::= #ModRevision';
      "Version" ::= #Version';
      "Value" ::= #Value';
      "Lease" ::= #Lease';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(KeyValue.mk Key' CreateRevision' ModRevision' Version' Value' Lease' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.

Module Event.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Type' : w32;
  Kv' : loc;
  PrevKv' : loc;
  XXX_NoUnkeyedLiteral' : unit;
  XXX_unrecognized' : slice.t;
  XXX_sizecache' : w32;
}.
End def.
End Event.


Global Instance settable_Event `{ffi_syntax}: Settable _ :=
  settable! Event.mk < Event.Type'; Event.Kv'; Event.PrevKv'; Event.XXX_NoUnkeyedLiteral'; Event.XXX_unrecognized'; Event.XXX_sizecache' >.
Global Instance into_val_Event `{ffi_syntax} : IntoVal Event.t.
Admitted.

Global Instance into_val_typed_Event `{ffi_syntax} : IntoValTyped Event.t mvccpb.Event :=
{|
  default_val := Event.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Event_Type `{ffi_syntax} : IntoValStructField "Type" mvccpb.Event Event.Type'.
Admitted.

Global Instance into_val_struct_field_Event_Kv `{ffi_syntax} : IntoValStructField "Kv" mvccpb.Event Event.Kv'.
Admitted.

Global Instance into_val_struct_field_Event_PrevKv `{ffi_syntax} : IntoValStructField "PrevKv" mvccpb.Event Event.PrevKv'.
Admitted.

Global Instance into_val_struct_field_Event_XXX_NoUnkeyedLiteral `{ffi_syntax} : IntoValStructField "XXX_NoUnkeyedLiteral" mvccpb.Event Event.XXX_NoUnkeyedLiteral'.
Admitted.

Global Instance into_val_struct_field_Event_XXX_unrecognized `{ffi_syntax} : IntoValStructField "XXX_unrecognized" mvccpb.Event Event.XXX_unrecognized'.
Admitted.

Global Instance into_val_struct_field_Event_XXX_sizecache `{ffi_syntax} : IntoValStructField "XXX_sizecache" mvccpb.Event Event.XXX_sizecache'.
Admitted.

Global Instance wp_struct_make_Event `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Type' Kv' PrevKv' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache':
  PureWp True
    (struct.make mvccpb.Event (alist_val [
      "Type" ::= #Type';
      "Kv" ::= #Kv';
      "PrevKv" ::= #PrevKv';
      "XXX_NoUnkeyedLiteral" ::= #XXX_NoUnkeyedLiteral';
      "XXX_unrecognized" ::= #XXX_unrecognized';
      "XXX_sizecache" ::= #XXX_sizecache'
    ]))%V
    #(Event.mk Type' Kv' PrevKv' XXX_NoUnkeyedLiteral' XXX_unrecognized' XXX_sizecache').
Admitted.


Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions mvccpb.pkg_name' var_addrs mvccpb.functions' mvccpb.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End mvccpb.
