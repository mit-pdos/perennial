From Perennial.program_proof.tulip Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import tuple.

Section res.
  Context `{!tulip_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition own_phys_hist_half α (key : string) (hist : dbhist) : iProp Σ.
  Admitted.
End res.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition is_tuple (tuple : loc) (key : string) (α : replica_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_tuple_persistent tuple key α :
    Persistent (is_tuple tuple key α).
  Admitted.

  Theorem wp_Tuple__AppendVersion (tuple : loc) (tid : u64) (val : string) key hist α :
    (length hist ≤ uint.nat tid)%nat ->
    is_tuple tuple key α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__AppendVersion #tuple #tid #(LitString val)
    {{{ RET #(); own_phys_hist_half α key (last_extend (uint.nat tid) hist ++ [Some val]) }}}.
  Proof.
  Admitted.

  Theorem wp_Tuple__KillVersion (tuple : loc) (tid : u64) key hist α :
    (length hist ≤ uint.nat tid)%nat ->
    is_tuple tuple key α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__KillVersion #tuple #tid
    {{{ RET #(); own_phys_hist_half α key (last_extend (uint.nat tid) hist ++ [None]) }}}.
  Proof.
  Admitted.

  (* TODO *)
  Theorem wp_Tuple__ReadVersion (tuple : loc) (tid : u64) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
      Tuple__ReadVersion #tuple #tid
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok); True }}}.
  Proof.
  Admitted.

End program.
