(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import go_etcd_io.raft.v3.confchange.
From New.golang Require Import theory.

Axiom falso : False.

Module Changer.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Tracker' : tracker.ProgressTracker.t;
  LastIndex' : w64;
}.
End def.
End Changer.


Global Instance settable_Changer `{ffi_syntax}: Settable _ :=
  settable! Changer.mk < Changer.Tracker'; Changer.LastIndex' >.
Global Instance into_val_Changer `{ffi_syntax} : IntoVal Changer.t.
Admitted.

Global Instance into_val_typed_Changer `{ffi_syntax} : IntoValTyped Changer.t confchange.Changer :=
{|
  default_val := Changer.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Changer_Tracker `{ffi_syntax} : IntoValStructField "Tracker" confchange.Changer Changer.Tracker'.
Admitted.

Global Instance into_val_struct_field_Changer_LastIndex `{ffi_syntax} : IntoValStructField "LastIndex" confchange.Changer Changer.LastIndex'.
Admitted.

Instance wp_struct_make_Changer `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Tracker' LastIndex':
  PureWp True
    (struct.make confchange.Changer (alist_val [
      "Tracker" ::= #Tracker';
      "LastIndex" ::= #LastIndex'
    ]))%V
    #(Changer.mk Tracker' LastIndex').
Admitted.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.go_etcd_io.raft.v3.confchange.
Require Export New.proof.proof_prelude.
Module confchange.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions confchange.pkg_name' var_addrs confchange.functions' confchange.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End defs.
End confchange.
