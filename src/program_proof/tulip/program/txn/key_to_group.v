From Perennial.program_proof.tulip.program Require Import prelude.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_KeyToGroup (key : string) :
    {{{ True }}}
      KeyToGroup #(LitString key)
    {{{ (gid : u64), RET #gid; ⌜key_to_group key = gid⌝ }}}.
  Proof.
    (*@ func KeyToGroup(key string) uint64 {                                    @*)
    (*@     // TODO                                                             @*)
    (*@     return 0                                                            @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
