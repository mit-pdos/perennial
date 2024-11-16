From Perennial.program_proof.tulip.program Require Import prelude.

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

  Theorem wp_Tuple__AppendVersion (tuple : loc) (tsW : u64) (value : string) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [Some value] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple key α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__AppendVersion #tuple #tsW #(LitString value)
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
  Admitted.

  Theorem wp_Tuple__KillVersion (tuple : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [None] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple key α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__KillVersion #tuple #tsW
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
  Admitted.

  (* TODO *)
  Theorem wp_Tuple__ReadVersion (tuple : loc) (tsW : u64) key α :
    let ts := uint.nat tsW in
    is_tuple tuple key α -∗
    {{{ True }}}
      Tuple__ReadVersion #tuple #tsW
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok); True }}}.
  Proof.
  Admitted.

End program.
