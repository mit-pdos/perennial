(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import time.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.time.
Require Export New.proof.proof_prelude.
Module time.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions time.pkg_name' var_addrs time.functions' time.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End defs.
End time.
