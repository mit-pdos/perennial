From Perennial.goose_lang Require Export prelude ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export prelude ffi.grove_ffi.

Section time.
Context `{!heapGS Σ}.

Axiom wp_TimeNow:
  {{{
      True
  }}}
    TimeNow #()
  {{{
       (t:u64), RET #t; True
  }}}
  .

Axiom wp_Sleep : forall (t:u64),
  {{{
      True
  }}}
    Sleep #t
  {{{
       RET #(); True
  }}}
  .

End time.
