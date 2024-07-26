From New.proof Require Import grove_prelude.
From New.code Require Import github_com.mit_pdos.gokv.kv.

Section definitions.
Context `{!heapGS Σ}.
(* KV points-to for the internal kv service *)
Implicit Types (kvptsto: string → string → iProp Σ).
Implicit Types (E:coPset).

(* Specification of Kv interface. *)
Definition is_Kv_Put kvptsto E (v : val) : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    (interface.get "Put" v) #(LitString key) #(LitString value) @ E
  <<< kvptsto key value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get kvptsto E (v : val) : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, kvptsto key value >>>
    (interface.get "Get" v) #(LitString key) @ E
  <<< kvptsto key value >>>
  {{{ RET #(LitString value); True }}}.

Definition is_Kv (k : val) kvptsto E : iProp Σ :=
  "#HputSpec" ∷ is_Kv_Put kvptsto E k ∗
  "#HgetSpec" ∷ is_Kv_Get kvptsto E k
.

Definition is_Kv_ConditionalPut kvptsto E (v : val) : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    (interface.get "ConditionalPut") v #(LitString key) #(LitString expect) #(LitString value) @ E
  <<< kvptsto key (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(LitString (if bool_decide (expect = old_value) then "ok" else "")); True }}}.


Definition is_KvCput (k : val) kvptsto E : iProp Σ :=
  "#Hkv" ∷ is_Kv k kvptsto E ∗
  "#HcputSpec" ∷ is_Kv_ConditionalPut kvptsto E k
.

End definitions.
