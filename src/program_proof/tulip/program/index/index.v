From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.program Require Import tuple.
From Goose.github_com.mit_pdos.tulip Require Import index.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition is_index (idx : loc) (γ : tulip_names) (α : replica_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_index_persistent idx γ α :
    Persistent (is_index idx γ α).
  Admitted.

  Theorem wp_Index__GetTuple (idx : loc) (key : string) γ α :
    key ∈ keys_all ->
    is_index idx γ α -∗
    {{{ True }}}
      Index__GetTuple #idx #(LitString key)
    {{{ (tpl : loc), RET #tpl; is_tuple tpl key γ α }}}.
  Proof.
    (*@ func (idx *Index) GetTuple(key string) *Tuple {                         @*)
    (*@     // TODO                                                             @*)
    (*@     return &Tuple{}                                                     @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
