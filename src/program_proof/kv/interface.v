From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import kv.

Delimit Scope byte_string_scope with go.

Section definitions.
Context `{!heapGS Σ}.
(* KV points-to for the internal kv service *)
Implicit Types (kvptsto: byte_string → byte_string → iProp Σ).
Implicit Types (E:coPset).

(* Specification of Kv interface. *)
Definition is_Kv_Put kvptsto E (Put_fn:val) : iProp Σ :=
  ∀ key value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    Put_fn #(LitString key) #(LitString value) @ E
  <<< kvptsto key value >>>
  {{{ RET #(); True }}}.

Definition is_Kv_Get kvptsto E (Get_fn:val) : iProp Σ :=
  ∀ key,
  {{{ True }}}
  <<< ∀∀ value, kvptsto key value >>>
    Get_fn #(LitString key) @ E
  <<< kvptsto key value >>>
  {{{ RET #(LitString value); True }}}.

Definition is_Kv_ConditionalPut kvptsto E (CondPut_fn:val) : iProp Σ :=
  ∀ key expect value,
  {{{ True }}}
  <<< ∀∀ old_value, kvptsto key old_value >>>
    CondPut_fn #(LitString key) #(LitString expect) #(LitString value) @ E
  <<< kvptsto key (if bool_decide (expect = old_value) then value else old_value) >>>
  {{{ RET #(LitString (if bool_decide (expect = old_value) then "ok"%go else ""%go)); True }}}.

Definition is_Kv (k:loc) kvptsto E : iProp Σ :=
  ∃ Put_fn Get_fn CondPut_fn,
  "#Hput" ∷ readonly (k ↦[Kv :: "Put"] Put_fn) ∗
  "#HputSpec" ∷ is_Kv_Put kvptsto E Put_fn ∗

  "#Hget" ∷ readonly (k ↦[Kv :: "Get"] Get_fn) ∗
  "#HgetSpec" ∷ is_Kv_Get kvptsto E Get_fn ∗

  "#Hcput" ∷ readonly (k ↦[Kv :: "ConditionalPut"] CondPut_fn) ∗
  "#HcputSpec" ∷ is_Kv_ConditionalPut kvptsto E CondPut_fn
.

End definitions.

Section hocap_definitions.
Context `{!heapGS Σ}.

(* HoCAP predicate *)
Implicit Types (P: gmap byte_string byte_string → iProp Σ).
Implicit Types (E:coPset).

(* Specification of Kv interface. *)
Definition is_Kv_Put_hocap P E (Put_fn:val) : iProp Σ :=
  ∀ key value Q,
  {{{
      ∀ σ, P σ ={E}=∗ P (<[ key := value ]> σ) ∗ Q
  }}}
     Put_fn #(LitString key) #(LitString value) @ E
  {{{
      RET #(); Q
  }}}.

Definition is_Kv_Get_hocap P E (Get_fn:val) : iProp Σ :=
  ∀ key Q,
  {{{ ∀ σ, P σ ={E}=∗ P σ ∗ Q (default ""%go (σ !! key))  }}}
    Get_fn #(LitString key) @ E
  {{{ value, RET #(LitString value); Q value }}}.

(* equivalent to the above, but maybe a bit cleaner by writing it with WP directly *)
Definition is_Kv_Get_hocap2 P E (Get_fn:val) : iProp Σ :=
  ∀ key Φ,
  (∀ σ, P σ ={E}=∗ P σ ∗ Φ #(LitString (default ""%go (σ !! key)))) -∗
  WP Get_fn #(LitString key) @ E {{ Φ }}
.

End hocap_definitions.
