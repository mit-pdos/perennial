From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.program Require Import tuple.
From Goose.github_com.mit_pdos.tulip Require Import index.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition is_index (idx : loc) (α : replica_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_index_persistent idx α :
    Persistent (is_index idx α).
  Admitted.

  Theorem wp_Index__GetTuple (idx : loc) (key : string) α :
    key ∈ keys_all ->
    is_index idx α -∗
    {{{ True }}}
      Index__GetTuple #idx #(LitString key)
    {{{ (tpl : loc), RET #tpl; is_tuple tpl key α }}}.
  Proof.
    (*@ func (idx *Index) GetTuple(key string) *Tuple {                         @*)
    (*@     // TODO                                                             @*)
    (*@     return &Tuple{}                                                     @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
