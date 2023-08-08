From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_logic Require Import atomic.
From Goose.github_com.mit_pdos.gokv Require Import leasekv.
From iris.base_logic.lib Require Import ghost_map.

Section proof.
Context `{!heapGS Σ}.
Context `{!ghost_mapG Σ string string}.

(* Specification of Kv interface. *)
Definition is_Kv_Put Put_fn γ : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, key ↪[γ] old_value >>>
    Put_fn #(LitString key) #(LitString value) @ ∅
  <<< key ↪[γ] value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get Get_fn γ : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, key ↪[γ] value >>>
    Get_fn #(LitString key) @ ∅
  <<< key ↪[γ] value >>>
  {{{ RET #(LitString value); True }}}.

Definition is_Kv_ConditionalPut CondPut_fn γ : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, key ↪[γ] old_value >>>
    CondPut_fn #(LitString key) #(LitString expect) #(LitString value) @ ∅
  <<< key ↪[γ] (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(LitString (if bool_decide (expect = old_value) then "ok" else "")); True }}}.

End proof.
