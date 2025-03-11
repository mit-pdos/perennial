From New.proof Require Import grove_prelude.
From New.code Require Import github_com.mit_pdos.gokv.kv.
Require Import New.generatedproof.github_com.mit_pdos.gokv.kv.

Section definitions.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

(* KV points-to for the internal kv service *)
Implicit Types (kvptsto: go_string → go_string → iProp Σ).
Implicit Types (E:coPset).

#[global]
Program Instance : IsPkgInit kv :=
  ltac2:(build_pkg_init ()).
Final Obligation. apply _. Qed.

(* Specification of Kv interface. *)
Definition is_Kv_Put kvptsto E (v : interface.t) : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    (interface.get #"Put" #v) #key #value @ E
  <<< kvptsto key value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get kvptsto E (v : interface.t) : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, kvptsto key value >>>
    (interface.get #"Get" #v) #key @ E
  <<< kvptsto key value >>>
  {{{ RET #value; True }}}.

Definition is_Kv (k : interface.t) kvptsto E : iProp Σ :=
  "#HputSpec" ∷ is_Kv_Put kvptsto E k ∗
  "#HgetSpec" ∷ is_Kv_Get kvptsto E k.

Definition is_Kv_ConditionalPut kvptsto E (v : interface.t) : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    (interface.get #"ConditionalPut") #v #key #expect #value @ E
  <<< kvptsto key (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(if bool_decide (expect = old_value) then "ok" else ""); True }}}.


Definition is_KvCput (k : interface.t) kvptsto E : iProp Σ :=
  "#Hkv" ∷ is_Kv k kvptsto E ∗
  "#HcputSpec" ∷ is_Kv_ConditionalPut kvptsto E k.

End definitions.
