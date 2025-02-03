(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import os.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.os.
Require Export New.proof.proof_prelude.
Module os.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions os.pkg_name' var_addrs os.functions' os.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End defs.
End os.
