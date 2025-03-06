(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.time.
Require Export New.golang.theory.

Module time.
Axiom falso : False.
Module Time.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  wall' : w64;
  ext' : w64;
  loc' : loc;
}.
End def.
End Time.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Time `{ffi_syntax}: Settable _ :=
  settable! Time.mk < Time.wall'; Time.ext'; Time.loc' >.
Global Instance into_val_Time `{ffi_syntax} : IntoVal Time.t.
Admitted.

Global Instance into_val_typed_Time `{ffi_syntax} : IntoValTyped Time.t time.Time :=
{|
  default_val := Time.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Time_wall `{ffi_syntax} : IntoValStructField "wall" time.Time Time.wall'.
Admitted.

Global Instance into_val_struct_field_Time_ext `{ffi_syntax} : IntoValStructField "ext" time.Time Time.ext'.
Admitted.

Global Instance into_val_struct_field_Time_loc `{ffi_syntax} : IntoValStructField "loc" time.Time Time.loc'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Time `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} wall' ext' loc':
  PureWp True
    (struct.make time.Time (alist_val [
      "wall" ::= #wall';
      "ext" ::= #ext';
      "loc" ::= #loc'
    ]))%V
    #(Time.mk wall' ext' loc').
Admitted.


Global Instance Time_struct_fields_split dq l (v : Time.t) :
  StructFieldsSplit dq l v (
    "Hwall" ∷ l ↦s[time.Time :: "wall"]{dq} v.(Time.wall') ∗
    "Hext" ∷ l ↦s[time.Time :: "ext"]{dq} v.(Time.ext') ∗
    "Hloc" ∷ l ↦s[time.Time :: "loc"]{dq} v.(Time.loc')
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

Definition is_defined := is_global_definitions time.pkg_name' var_addrs.

Global Instance : PkgIsDefined time.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End time.
