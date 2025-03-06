(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.strings.
Require Export New.golang.theory.

Module strings.
Axiom falso : False.
Module Builder.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  addr' : loc;
  buf' : slice.t;
}.
End def.
End Builder.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Builder `{ffi_syntax}: Settable _ :=
  settable! Builder.mk < Builder.addr'; Builder.buf' >.
Global Instance into_val_Builder `{ffi_syntax} : IntoVal Builder.t.
Admitted.

Global Instance into_val_typed_Builder `{ffi_syntax} : IntoValTyped Builder.t strings.Builder :=
{|
  default_val := Builder.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Builder_addr `{ffi_syntax} : IntoValStructField "addr" strings.Builder Builder.addr'.
Admitted.

Global Instance into_val_struct_field_Builder_buf `{ffi_syntax} : IntoValStructField "buf" strings.Builder Builder.buf'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Builder `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} addr' buf':
  PureWp True
    (struct.make strings.Builder (alist_val [
      "addr" ::= #addr';
      "buf" ::= #buf'
    ]))%V
    #(Builder.mk addr' buf').
Admitted.


Global Instance Builder_struct_fields_split dq l (v : Builder.t) :
  StructFieldsSplit dq l v (
    "Haddr" ∷ l ↦s[strings.Builder :: "addr"]{dq} v.(Builder.addr') ∗
    "Hbuf" ∷ l ↦s[strings.Builder :: "buf"]{dq} v.(Builder.buf')
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

Definition is_defined := is_global_definitions strings.pkg_name' var_addrs strings.functions' strings.msets'.

Global Instance : PkgIsDefined strings.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End strings.
