From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_logic Require Import atomic.
From Goose.github_com.mit_pdos.gokv Require Import kv.

Section definitions.
Context `{!heapGS Σ}.
(* KV points-to for the internal kv service *)
Context {kvptsto: string → string → iProp Σ}.

(* Specification of Kv interface. *)
Definition is_Kv_Put (Put_fn:val) : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    Put_fn #(LitString key) #(LitString value) @ ∅
  <<< kvptsto key value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get (Get_fn:val) : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, kvptsto key value >>>
    Get_fn #(LitString key) @ ∅
  <<< kvptsto key value >>>
  {{{ RET #(LitString value); True }}}.

Definition is_Kv_ConditionalPut (CondPut_fn:val) : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    CondPut_fn #(LitString key) #(LitString expect) #(LitString value) @ ∅
  <<< kvptsto key (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(LitString (if bool_decide (expect = old_value) then "ok" else "")); True }}}.

Definition is_Kv (k:loc) : iProp Σ :=
  ∃ Put_fn Get_fn CondPut_fn,
  "#Hput" ∷ readonly (k ↦[Kv :: "Put"] Put_fn) ∗
  "#HputSpec" ∷ is_Kv_Put Put_fn ∗

  "#Hget" ∷ readonly (k ↦[Kv :: "Get"] Get_fn) ∗
  "#HgetSpec" ∷ is_Kv_Get Get_fn ∗

  "#Hcput" ∷ readonly (k ↦[Kv :: "ConditionalPut"] CondPut_fn) ∗
  "#HcputSpec" ∷ is_Kv_ConditionalPut CondPut_fn
.

End definitions.
