From Perennial.program_proof.rsm Require Import distx distx_tuple.
From Goose.github_com.mit_pdos.rsm Require Import distx.


Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition is_index (idx : loc) (α : gname) : iProp Σ.
  Admitted.

  Theorem wp_Index__GetTuple (idx : loc) (key : string) α :
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
