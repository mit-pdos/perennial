From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoutil.

From Perennial.program_proof.pav Require Import cryptoffi misc.

Section proof.
Context `{!heapGS Σ}.

Lemma wp_HasherWrite sl_hr hr ptr_hr sl_data (data : list w8) :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT (DfracOwn 1) hr ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr) ∗
    "#Hdata" ∷ own_slice_small sl_data byteT DfracDiscarded data
  }}}
  HasherWrite #ptr_hr (slice_val sl_data)
  {{{
    sl_hr', RET #();
    "Hhr" ∷ own_slice_small sl_hr' byteT (DfracOwn 1) (hr ++ data) ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr')
  }}}.
Proof. Admitted.

Lemma wp_HasherWriteSl sl_hr hr ptr_hr sl_data data :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT (DfracOwn 1) hr ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr) ∗
    "#Hdata" ∷ is_Slice2D sl_data data
  }}}
  HasherWriteSl #ptr_hr (slice_val sl_data)
  {{{
    sl_hr', RET #();
    "Hhr" ∷ own_slice_small sl_hr' byteT (DfracOwn 1) (hr ++ concat data) ∗
    "Hptr_hr" ∷ ptr_hr ↦[slice.T byteT] (slice_val sl_hr')
  }}}.
Proof. Admitted.

Lemma wp_HasherSumNil sl_hr hr :
  {{{
    "Hhr" ∷ own_slice_small sl_hr byteT (DfracOwn 1) hr
  }}}
  HasherSum (slice_val sl_hr) slice.nil
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "#Hhash" ∷ is_hash hr hash ∗
    "Hsl_hash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash
  }}}.
Proof. Admitted.

End proof.
