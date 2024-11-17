From Perennial.program_proof.tulip.program Require Import prelude.

Section res.
  Context `{!tulip_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition own_phys_hist_half α (key : string) (hist : dbhist) : iProp Σ.
  Admitted.
End res.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition is_tuple (tuple : loc) (key : string) (γ : tulip_names) (α : replica_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_tuple_persistent tuple key γ α :
    Persistent (is_tuple tuple key γ α).
  Admitted.

  Theorem wp_Tuple__AppendVersion (tuple : loc) (tsW : u64) (value : string) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [Some value] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple key γ α -∗
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
    is_tuple tuple key γ α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__KillVersion #tuple #tsW
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
  Admitted.

  Theorem wp_Tuple__ReadVersion_xphys (tuple : loc) (tsW : u64) key γ α :
    let ts := uint.nat tsW in
    is_tuple tuple key γ α -∗
    {{{ True }}}
      Tuple__ReadVersion #tuple #tsW
    {{{ (t : u64) (v : dbval), RET (#t, dbval_to_val v);
        if decide (uint.nat t = O) then is_repl_hist_at γ key (pred ts) v else True
    }}}.
  Proof.
  Admitted.

  Theorem wp_Tuple__ReadVersion (tuple : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    is_tuple tuple key γ α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__ReadVersion #tuple #tsW
    {{{ (t : u64) (v : dbval), RET (#t, dbval_to_val v);
        own_phys_hist_half α key hist ∗
        if decide (uint.nat t = O)
        then is_repl_hist_at γ key (pred ts) v
        else is_repl_hist_lb γ key hist ∗
             ⌜last hist = Some v⌝ ∗
             ⌜uint.nat t = pred (length hist)⌝ ∗
             ⌜(length hist < ts)%nat⌝
    }}}.
  Proof.
  Admitted.

End program.
