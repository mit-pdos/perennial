From Perennial.program_proof.rsm Require Import distx.
From Goose.github_com.mit_pdos.rsm Require Import distx.


Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  (* NB: One half of the phsyical tuple is kept in the replica invariant, one
  half in the tuple invariant. GC-related methods does not require the one in
  the replica invariant, essentially forcing GC to not change the abstract
  view. *)
  
  Definition tuple_phys_half
    (α : gname) (key : string) (hist : dbhist) (tsprep : nat) : iProp Σ.
  Admitted.

  Definition is_tuple (tuple : loc) (key : string) (α : gname) : iProp Σ.
  Admitted.

  Theorem wp_Tuple__AppendVersion
    (tuple : loc) (tid : u64) (val : string) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__AppendVersion #tuple #tid #(LitString val)
    {{{ RET #(); tuple_phys_half α key (last_extend (uint.nat tid) hist ++ [Some val]) tsprep }}}.
  Proof.
    (*@ func (tuple *Tuple) AppendVersion(tid uint64, val string) {             @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__Extend (tuple : loc) (tid : u64) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__Extend #tuple #tid
    {{{ (ok : bool), RET #ok; if ok
                           then tuple_phys_half α key (last_extend (uint.nat tid) hist) tsprep
                           else tuple_phys_half α key hist tsprep
    }}}.
  Proof.
    (*@ func (tuple *Tuple) Extend(tid uint64) bool {                           @*)
    (*@     // TODO                                                             @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__Free (tuple : loc) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__Free #tuple
    {{{ RET #(); tuple_phys_half α key hist O }}}.
  Proof.
    (*@ func (tuple *Tuple) Free() {                                            @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__KillVersion (tuple : loc) (tid : u64) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__KillVersion #tuple #tid
    {{{ RET #(); tuple_phys_half α key (last_extend (uint.nat tid) hist ++ [None]) tsprep }}}.
  Proof.
    (*@ func (tuple *Tuple) KillVersion(tid uint64) {                           @*)
    (*@     // TODO                                                             @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__Own (tuple : loc) (tid : u64) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__Own #tuple #tid
    {{{ (ok : bool), RET #ok; if ok
                           then tuple_phys_half α key hist (uint.nat tid)
                           else tuple_phys_half α key hist tsprep
    }}}.
  Proof.
    (*@ func (tuple *Tuple) Own(tid uint64) bool {                              @*)
    (*@     // TODO                                                             @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Tuple__ReadVersion (tuple : loc) (tid : u64) key hist tsprep α :
    is_tuple tuple key α -∗
    {{{ tuple_phys_half α key hist tsprep }}}
      Tuple__ReadVersion #tuple #tid
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        tuple_phys_half α key hist tsprep ∗
        ⌜if ok then hist !! (uint.nat tid) = Some v else True⌝
    }}}.
  Proof.
    (*@ func (tuple *Tuple) ReadVersion(tid uint64) (Value, bool) {             @*)
    (*@     // TODO                                                             @*)
    (*@     // Return false if the abstract history has no value at index @tid. @*)
    (*@     return Value{}, false                                               @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
