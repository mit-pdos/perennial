From Perennial.goose_lang Require Export prelude ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export prelude ffi.grove_ffi.

Section exit.
Context `{!heapGS Σ}.

Axiom wp_Exit : forall (n:u64),
  {{{
      True
  }}}
    Exit #n
  {{{
       RET #(); False
  }}}
  .

End exit.
