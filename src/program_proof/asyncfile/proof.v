From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require asyncfile.

Section asyncfile_proof.

Context `{!heapGS Σ}.
Definition own_AsyncFile (N:namespace) (f:loc) (P: list u8 → iProp Σ) (data:list u8) : iProp Σ.
Admitted.

Lemma wp_AsyncFile__Write N f P olddata data_sl data Q:
  {{{
        "Hf" ∷ own_AsyncFile N f P olddata ∗
        "Hdata" ∷ own_slice_small data_sl byteT 1 data ∗
        "Hupd" ∷ (P olddata ={⊤∖↑N}=∗ P data ∗ Q)
  }}}
    asyncfile.AsyncFile__Write #f (slice_val data_sl)
  {{{
        (w:val), RET w;
        own_AsyncFile N f P data ∗
        WP w #() {{ _, Q }}
  }}}
.
Proof.
Admitted.

End asyncfile_proof.
