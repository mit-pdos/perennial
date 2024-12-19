From Perennial.program_proof.rsm.distx Require Import prelude.
From Goose.github_com.mit_pdos.rsm Require Import distx.

Section resource.
  Context `{!distx_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition tupleN := nroot .@ "tuple".

  (* NB: One half of the phsyical tuple is kept in the replica invariant, one
  half in the tuple invariant. GC-related methods does not require the one in
  the replica invariant, essentially forcing GC to not change the abstract
  view. *)

  Definition hist_phys_quarter α (key : byte_string) (hist : dbhist) : iProp Σ.
  Admitted.

  Definition hist_phys_half α (key : byte_string) (hist : dbhist) : iProp Σ.
  Admitted.

  Definition hist_phys_lb α (key : byte_string) (hist : dbhist) : iProp Σ.
  Admitted.

  #[global]
  Instance is_hist_phys_lb_persistent α key hist :
    Persistent (hist_phys_lb α key hist).
  Admitted.

  Lemma hist_phys_combine α key hist1 hist2 :
    hist_phys_quarter α key hist1 -∗
    hist_phys_quarter α key hist2 -∗
    hist_phys_half α key hist1 ∗ ⌜hist2 = hist1⌝.
  Admitted.

  Lemma hist_phys_split α key hist :
    hist_phys_half α key hist -∗
    hist_phys_quarter α key hist ∗ hist_phys_quarter α key hist.
  Admitted.

  Lemma hist_phys_prefix α key hist histp :
    hist_phys_quarter α key hist -∗
    hist_phys_lb α key histp -∗
    ⌜prefix histp hist⌝.
  Admitted.

  Definition hist_phys_at α (key : byte_string) (ts : nat) (v : dbval) : iProp Σ :=
    ∃ hist, ⌜hist !! ts = Some v⌝ ∗ hist_phys_lb α key hist.

  Definition ts_phys_half α (key : byte_string) (tsprep : nat) : iProp Σ.
  Admitted.

  Definition tuple_phys_half α (key : byte_string) (hist : dbhist) (tsprep : nat) : iProp Σ :=
    hist_phys_half α key hist ∗ ts_phys_half α key tsprep.

End resource.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  Definition is_tuple (tuple : loc) (key : byte_string) (α : replica_names) : iProp Σ.
  Admitted.

  #[global]
  Instance is_tuple_persistent tuple key α :
    Persistent (is_tuple tuple key α).
  Admitted.

  (* NB: If we were simply to use Paxos rather than PCR, a better way would be
  requiring the [tid = tsprep], and moving the the length precondition into the
  tuple invariant. With PCR, however, a tuple could be modified by a txn with a
  timestamp different from the prepared timestamp. A more fundamental reason to
  this difference is that while Paxos allows deducing commit safety at the
  *replica* level, PCR can only deduce such at the *replica group* level. *)
  Theorem wp_Tuple__AppendVersion (tuple : loc) (tid : u64) (val : byte_string) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
    <<< ∀∀ hist, hist_phys_half α key hist ∗ ⌜(length hist ≤ uint.nat tid)%nat⌝ >>>
      Tuple__AppendVersion #tuple #tid #(LitString val) @ ↑tupleN
    <<< hist_phys_half α key (last_extend (uint.nat tid) hist ++ [Some val]) >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (tuple *Tuple) AppendVersion(tid uint64, val string) {             @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__Extend (tuple : loc) (tid : u64) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
    <<< ∀∀ hist tsprep, tuple_phys_half α key hist tsprep >>>
      Tuple__Extend #tuple #tid @ ↑tupleN
    <<< ∃∃ (ok : bool),
        ⌜bool_decide (readable (uint.nat tid) hist tsprep) = ok⌝ ∗
        let hist' := if ok then last_extend (uint.nat tid) hist else hist in
        tuple_phys_half α key hist' tsprep
    >>>
    {{{ RET #ok; True }}}.
  Proof.
    (*@ func (tuple *Tuple) Extend(tid uint64) bool {                           @*)
    (*@     // TODO                                                             @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__Free (tuple : loc) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
    <<< ∀∀ tsprep, ts_phys_half α key tsprep >>>
      Tuple__Free #tuple @ ↑tupleN
    <<< ts_phys_half α key O >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (tuple *Tuple) Free() {                                            @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__KillVersion (tuple : loc) (tid : u64) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
    <<< ∀∀ hist, hist_phys_half α key hist ∗ ⌜(length hist ≤ uint.nat tid)%nat⌝ >>>
      Tuple__KillVersion #tuple #tid @ ↑tupleN
    <<< hist_phys_half α key (last_extend (uint.nat tid) hist ++ [None]) >>>
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (tuple *Tuple) KillVersion(tid uint64) {                           @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  (* TODO: should check [tid], [tsprep], and [length hist]. *)
  Theorem wp_Tuple__Own (tuple : loc) (tid : u64) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
    <<< ∀∀ hist tsprep, tuple_phys_half α key hist tsprep >>>
      Tuple__Own #tuple #tid @ ↑tupleN
    <<< ∃∃ (ok : bool),
        tuple_phys_half α key hist (if ok then (uint.nat tid) else tsprep)
    >>>
    {{{ RET #ok; ⌜bool_decide (lockable (uint.nat tid) hist tsprep) = ok⌝ }}}.
  Proof.
    (*@ func (tuple *Tuple) Own(tid uint64) bool {                              @*)
    (*@     // TODO                                                             @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__ReadVersion (tuple : loc) (tid : u64) key α :
    is_tuple tuple key α -∗
    {{{ True }}}
      Tuple__ReadVersion #tuple #tid
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        if ok then hist_phys_at α key (pred (uint.nat tid)) v else True
    }}}.
  Proof.
    (*@ func (tuple *Tuple) ReadVersion(tid uint64) (Value, bool) {             @*)
    (*@     // TODO                                                             @*)
    (*@     // Return false if the abstract history has no value at index @tid. @*)
    (*@     return Value{}, false                                               @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
